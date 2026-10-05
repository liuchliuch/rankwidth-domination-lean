#!/usr/bin/env python3
"""Invoke the pinned official Comparator, with mandatory real sandbox preflight."""
import argparse, importlib.util, json, os, pathlib, subprocess, sys, tempfile

ROOT=pathlib.Path(__file__).resolve().parent.parent
SPEC=ROOT/'verification/comparator'
spec=importlib.util.spec_from_file_location('prepare',ROOT/'scripts/comparator-prepare.py')
prep=importlib.util.module_from_spec(spec);spec.loader.exec_module(prep)
BLOCKED=78

def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

def preflight(tools,run):
    r=subprocess.run([sys.executable,str(ROOT/'scripts/comparator-preflight.py'),'--tools',str(tools),'--report',str(run/'preflight.json')],
                     text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (run/'preflight.log').write_text(r.stdout)
    print(r.stdout,end='')
    return r.returncode

def run_official(project,tools,log):
    env=dict(os.environ)
    env['PATH']=str(tools/'adapters')+os.pathsep+str(tools/'bin')+os.pathsep+env['PATH']
    env['LANDRUN_EXECUTABLE']=str((tools/'bin/landrun').resolve())
    env['LEAN_NUM_THREADS']=os.environ.get('LEAN_NUM_THREADS','2')
    env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    cmd=['systemd-run','--user','--quiet','--wait','--pipe',
         '--property=RestrictAddressFamilies=~AF_UNIX','--property=NoNewPrivileges=yes',
         '--setenv=PATH='+env['PATH'],'--setenv=LEAN_PATH=','--setenv=LEAN_SRC_PATH=',
         '--setenv=LANDRUN_EXECUTABLE='+env['LANDRUN_EXECUTABLE'],
         '--setenv=LEAN_NUM_THREADS='+env['LEAN_NUM_THREADS'],
         '--working-directory='+str(project),
         '--','lake','env',str(tools/'bin/comparator'),str(project/'config.json')]
    write(log.with_suffix('.command.json'),cmd)
    with log.open('w') as f:
        p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env=env)
        for line in p.stdout:
            print(line,end='',flush=True);f.write(line);f.flush()
        code=p.wait()
    return code,log.read_text()

def unchanged(project):
    inputs=json.loads((project/'source-snapshot.json').read_text())['inputs']
    return [p for p,h in inputs.items() if not pathlib.Path(p).is_file() or prep.sha(pathlib.Path(p))!=h]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['check','test'])
    p.add_argument('--tools',type=pathlib.Path,default=pathlib.Path(os.environ.get('RW_COMPARATOR_TOOLS_ROOT',pathlib.Path(os.environ.get('XDG_CACHE_HOME',pathlib.Path.home()/'.cache'))/'rankwidth-comparator/lean4.24')))
    p.add_argument('--work',type=pathlib.Path)
    p.add_argument('--mathlib',type=pathlib.Path,default=pathlib.Path(os.environ.get('RW_MATHLIB_ROOT',ROOT/'.lake/packages/mathlib')))
    a=p.parse_args();a.tools=a.tools.resolve()
    if os.environ.get('RW_LEAN_BIN'):os.environ['PATH']=os.environ['RW_LEAN_BIN']+os.pathsep+os.environ['PATH']
    run=a.work.resolve() if a.work else pathlib.Path(tempfile.mkdtemp(prefix='rankwidth-comparator-'))
    if run.is_relative_to(ROOT):raise SystemExit('Run artifacts must be outside the distributed source tree')
    if a.work:
        if run.exists() and any(run.iterdir()):raise SystemExit('Run directory must be absent or empty')
        run.mkdir(parents=True,exist_ok=True)
    print('Evidence directory:',run,flush=True)
    cases=json.loads((SPEC/'tests/cases.json').read_text()) if a.mode=='test' else None
    report={'status':'not_run','official_comparator_revision':json.loads((SPEC/'toolchain.lock.json').read_text())['comparator']['revision'],
            'mode':a.mode,'sandbox':'real Landrun + upstream systemd AF_UNIX restriction',
            'kernel':'official Lean 4.24 kernel replay','external_kernel':'not_run'}
    if cases:report['cases']=[dict(name=c['name'],status='not_run') for c in cases]
    code=preflight(a.tools,run)
    if code:
        report.update(status='blocked',exit_code=code,reason='Sandbox/provenance preflight did not pass; no official comparison or adversarial fixture was run')
        write(run/'result.json',report)
        print(report['reason'],file=sys.stderr)
        return BLOCKED
    if a.mode=='check':
        project=run/'project'
        try:
            report['coverage']=prep.validate_paper_coverage()
            snapshot=prep.prepare(project,a.tools,a.mathlib,SPEC/'reference',SPEC/'solution',SPEC/'config.json')
            if snapshot['definition_names']:raise ValueError('Paper contracts must not contain definition holes')
            code,output=run_official(project,a.tools,run/'official-comparator.log')
            drift=unchanged(project)
            passed=code==0 and 'Lean default kernel accepts the solution' in output and 'Your solution is okay!' in output and not drift
            report.update(status='passed' if passed else 'failed',exit_code=code,input_drift=drift,
                          theorem_count=len(snapshot['theorem_names']),definition_holes=0)
        except Exception as e:
            report.update(status='failed',reason=str(e),exit_code=1);passed=False
        write(run/'result.json',report)
        return 0 if passed else 1
    results=[]
    for case in cases:
        fixture=SPEC/'tests'/case['name'];project=run/case['name']
        try:
            prep.prepare(project,a.tools,a.mathlib,fixture/'reference',fixture/'solution',fixture/'config.json',module='Fixture',fallback=None)
            code,output=run_official(project,a.tools,run/(case['name']+'.log'))
            drift=unchanged(project)
            if case['expect']=='accept':
                ok=code==0 and 'Lean default kernel accepts the solution' in output and 'Your solution is okay!' in output
            else:
                # Rejection is valid only at the intended official check. A
                # build, sandbox, network, or missing-dependency failure fails
                # this regression instead of masquerading as a successful test.
                ok=code!=0 and all(marker in output for marker in case['required_output'])
            results.append({'name':case['name'],'status':'passed' if ok and not drift else 'failed',
                            'exit_code':code,'expected':case['expect'],'input_drift':drift})
        except Exception as e:results.append({'name':case['name'],'status':'failed','reason':str(e)})
    report['cases']=results;report['status']='passed' if all(x['status']=='passed' for x in results) else 'failed'
    write(run/'result.json',report)
    return 0 if report['status']=='passed' else 1

if __name__=='__main__':raise SystemExit(main())
