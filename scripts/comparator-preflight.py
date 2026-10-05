#!/usr/bin/env python3
"""Fail closed before any submitted Lean code reaches official Comparator.
This is an environment/provenance check, not a sandbox or proof checker.
"""
import argparse, ctypes, hashlib, json, os, pathlib, platform, shutil, socket, subprocess, sys, tempfile

BLOCKED = 78

def capture(argv):
    p = subprocess.run(argv, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {'command': argv, 'exit_code': p.returncode, 'output': p.stdout}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tools', type=pathlib.Path, required=True)
    ap.add_argument('--report', type=pathlib.Path, required=True)
    a = ap.parse_args()
    root = pathlib.Path(__file__).resolve().parent.parent
    pins = json.loads((root/'verification/comparator/toolchain.lock.json').read_text())
    result = {'status': 'blocked', 'proof_comparison': 'not_run', 'tests': 'not_run',
              'platform': platform.platform(), 'uid': os.geteuid(), 'checks': [], 'blockers': []}
    a.report.parent.mkdir(parents=True, exist_ok=True)
    def finish():
        a.report.write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result, indent=2))
        return 0 if result['status'] == 'passed' else BLOCKED
    installation = a.tools/'installation.json'
    if not installation.exists():
        result['blockers'].append('Pinned tools have not been installed; run comparator-setup.sh')
        return finish()
    installed = json.loads(installation.read_text())
    if installed['pins'] != pins:
        result['blockers'].append('Tool installation pins do not match the release lock')
    for name, entry in installed['binaries'].items():
        p = a.tools/'bin'/name
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != entry['sha256']:
            result['blockers'].append(f'Pinned binary changed or missing: {name}')
    for name in ['comparator', 'landrun']:
        c = capture(['git','-C',str(a.tools/name),'rev-parse','HEAD'])
        if c['exit_code'] or c['output'].strip() != pins[name]['revision']:
            result['blockers'].append(f'Wrong {name} source revision')
        c = capture(['git','-C',str(a.tools/name),'diff','--exit-code','HEAD','--'])
        if c['exit_code']:
            result['blockers'].append(f'Modified {name} source checkout')
    if os.geteuid() == 0:
        result['blockers'].append('Comparator upstream requires an unprivileged user')
    status_path = pathlib.Path('/proc/self/status')
    if status_path.exists():
        caps = next((line.split()[1] for line in status_path.read_text().splitlines() if line.startswith('CapEff:')), '0')
        if int(caps, 16):
            result['blockers'].append('Effective Linux capabilities must be empty')
    lean = shutil.which('lean')
    if not lean:
        result['blockers'].append('Lean 4.24.0 is not on PATH')
    else:
        version = capture([lean, '-V'])
        result['checks'].append(dict(version, role='required_lean_version', required=True))
        if version['exit_code'] or version['output'].strip() != '4.24.0':
            result['blockers'].append('Active Lean toolchain is not exact 4.24.0')
    if result['blockers']:
        return finish()
    landrun = str((a.tools/'bin/landrun').resolve())
    # Strict mode is safe even when Landlock is wholly absent. The workload is
    # only /usr/bin/true; no submitted file or proof is opened by this probe.
    strict = capture([landrun,'--ro','/','--ldd','--add-exec','--',shutil.which('true') or '/usr/bin/true'])
    strict.update(role='diagnostic_v9_only', required=False)
    result['checks'].append(strict)
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64','aarch64'):
        result['blockers'].append('ABI query currently supports Linux x86_64/aarch64 only')
        return finish()
    libc = ctypes.CDLL(None, use_errno=True)
    ctypes.set_errno(0)
    abi = libc.syscall(444, 0, 0, 1)  # landlock_create_ruleset(..., VERSION)
    err = ctypes.get_errno()
    result['landlock_abi'] = abi
    result['landlock_errno'] = err
    result['landlock_error'] = os.strerror(err) if abi < 0 else None
    result['process_security'] = [line for line in pathlib.Path('/proc/self/status').read_text().splitlines()
                                  if line.startswith(('NoNewPrivs:', 'Seccomp:', 'Seccomp_filters:', 'CapEff:'))]
    # ABI6 includes filesystem, TCP restrictions and IPC scoping. Never let
    # upstream's --best-effort silently turn off the sandbox on this host.
    if abi < 6:
        result['blockers'].append(f'Real Landlock ABI >=6 is required; query returned {abi}, errno {err} ({os.strerror(err)})')
        return finish()
    systemd = shutil.which('systemd-run')
    if not systemd:
        result['blockers'].append('systemd-run is required for the upstream AF_UNIX guard')
        return finish()
    guard = [systemd,'--user','--quiet','--wait','--pipe',
             '--property=RestrictAddressFamilies=~AF_UNIX','--property=NoNewPrivileges=yes','--']
    # The pinned 4.24 branch predates this security advisory. Its guard still
    # applies. We retain it even on newer kernels for a uniform audited flow.
    smoke = capture(guard + [landrun,'--best-effort','--ro','/','--rw','/dev','--ldd','--add-exec','--',shutil.which('true') or '/usr/bin/true'])
    result['checks'].append(smoke)
    if smoke['exit_code']:
        result['blockers'].append('Official systemd AF_UNIX guard + real Landrun smoke test failed')
        return finish()
    with tempfile.TemporaryDirectory(prefix='comparator-probe-') as tmp:
        canary = pathlib.Path(tmp)/'must-not-change'
        canary.write_text('unchanged\n')
        program = ('import errno,os,sys\n'
                   'try:\n f=os.open(sys.argv[1],os.O_WRONLY|os.O_TRUNC)\n'
                   'except OSError as e:\n sys.exit(0 if e.errno in (errno.EACCES,errno.EPERM) else 12)\n'
                   'else:\n os.close(f);sys.exit(11)\n')
        probe = capture(guard + [landrun,'--best-effort','--ro','/','--rw','/dev','--ldd','--add-exec','--',
                                sys.executable,'-c',program,str(canary)])
        result['checks'].append(probe)
        if probe['exit_code'] or canary.read_text() != 'unchanged\n':
            result['blockers'].append('Real Landrun did not enforce the read-only canary rule')
            return finish()
    # Test the required UNIX-domain-socket guard and TCP bind restriction on
    # harmless socket creation/binding. No remote endpoint is contacted.
    try:
        baseline = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        baseline.bind(('127.0.0.1', 0))
        port = baseline.getsockname()[1]
        baseline.close()
    except OSError as e:
        result['blockers'].append(f'Cannot establish unsandboxed TCP probe baseline: {e}')
        return finish()
    net_program = ('import errno,socket,sys\n'
                   'for family in (socket.AF_UNIX,socket.AF_INET):\n'
                   ' try:\n'
                   '  s=socket.socket(family,socket.SOCK_STREAM)\n'
                   '  if family==socket.AF_INET:s.bind(("127.0.0.1",int(sys.argv[1])))\n'
                   ' except OSError as e:\n'
                   '  if e.errno not in (errno.EACCES,errno.EPERM,errno.EAFNOSUPPORT):sys.exit(12)\n'
                   ' else:\n  s.close();sys.exit(11)\n')
    network = capture(guard + [landrun,'--best-effort','--ro','/','--rw','/dev','--ldd','--add-exec','--',
                              sys.executable,'-c',net_program,str(port)])
    network.update(role='required_network_enforcement', required=True)
    result['checks'].append(network)
    if network['exit_code']:
        result['blockers'].append('AF_UNIX guard or real Landrun TCP restriction was not enforced')
        return finish()
    result['status'] = 'passed'
    return finish()

if __name__ == '__main__':
    raise SystemExit(main())
