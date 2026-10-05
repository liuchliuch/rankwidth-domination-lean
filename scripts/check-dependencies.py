#!/usr/bin/env python3
"""Check immutable public dependency pins; optionally check local paper copies."""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys, tomllib
root = pathlib.Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--installed', action='store_true', help='also check the selected Lean and all dependency Git checkouts')
parser.add_argument('--paper', action='store_true', help='require and hash-check the original paper assets listed in paper/PROVENANCE.json')
args = parser.parse_args()
lock = json.loads((root/'dependencies.lock.json').read_text())
manifest = json.loads((root/'lake-manifest.json').read_text())
config = tomllib.loads((root/'lakefile.toml').read_text())
errors = []
def check(ok, message):
    if not ok: errors.append(message)
check((root/'lean-toolchain').read_text().strip() == lock['lean_toolchain'], 'Lean toolchain disagrees with lock')
check(config['name'] == manifest['name'], 'Lake configuration and manifest package names differ')
pinned = {p['name']:p for p in lock['packages']}
resolved = {p['name']:p for p in manifest['packages']}
check(set(pinned) == set(resolved), 'Lake manifest package set disagrees with lock')
for name, p in pinned.items():
    check(bool(re.fullmatch('[0-9a-f]{40}', p['rev'])), f'{name}: not an immutable Git revision')
    check(name in resolved and all(resolved[name].get(k)==p[k] for k in ('url','rev')), f'{name}: Lake manifest disagrees with lock')
mathlib_req = next(x for x in config['require'] if x['name']=='mathlib')
check(mathlib_req['git']==pinned['mathlib']['url'] and mathlib_req['rev']==pinned['mathlib']['rev'], 'mathlib requirement disagrees with lock')
check('RankwidthDomination.*' in config['lean_lib'][0].get('globs',[]), 'Lake default target does not include all project modules')
if args.paper:
    for name, entry in json.loads((root/'paper/PROVENANCE.json').read_text())['files'].items():
        p = root/name
        check(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==entry['sha256'], f'Paper hash mismatch: {name}')
if args.installed:
    try:
        version = subprocess.check_output(['lean','--version'],text=True).strip()
        expected = lock['lean_toolchain'].rsplit(':v',1)[-1]
        check(f'Lean (version {expected},' in version, f'Unexpected compiler: {version}')
    except (OSError,subprocess.CalledProcessError) as e:
        errors.append(f'Cannot query Lean: {e}')
    mathlib = pathlib.Path(os.environ.get('RW_MATHLIB_ROOT', root/'.lake/packages/mathlib'))
    upstream_manifest = mathlib/'lake-manifest.json'
    check(upstream_manifest.is_file() and hashlib.sha256(upstream_manifest.read_bytes()).hexdigest()==lock['mathlib_manifest_sha256'], 'Selected mathlib manifest differs from the pinned public revision')
    for name,p in pinned.items():
        candidates = [mathlib] if name=='mathlib' else [root/'.lake/packages'/name, mathlib/'.lake/packages'/name]
        location = next((x for x in candidates if x.is_dir()), candidates[0])
        try:
            head = subprocess.check_output(['git','-C',str(location),'rev-parse','HEAD'],text=True,stderr=subprocess.PIPE).strip()
            check(head == p['rev'],f'{name}: installed Git revision is {head}, expected {p["rev"]}')
            dirty = subprocess.check_output(['git','-C',str(location),'status','--porcelain','--untracked-files=no'],text=True).strip()
            check(not dirty,f'{name}: tracked dependency files are modified')
        except (OSError,subprocess.CalledProcessError) as e:
            errors.append(f'{name}: cannot verify checkout at {location}: {e}')
if errors:
    for error in errors: print('FAIL:',error,file=sys.stderr)
    raise SystemExit(1)
print('PASS: public immutable dependency pins' + ('; original paper hashes verified' if args.paper else '') + ('; selected compiler and dependency checkouts verified' if args.installed else ''))
