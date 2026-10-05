#!/usr/bin/env python3
"""Prepare separate reference/submission phases for unmodified Comparator.
Does not compile Lean, export declarations, compare proofs, or run a sandbox.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
SPEC = ROOT/'verification/comparator'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def imports(p):
    # All project headers use one-line imports. Remove nested Lean comments
    # first; quoted strings do not occur before these import declarations.
    s = p.read_text(); out=[]; i=0; depth=0
    while i < len(s):
        if s[i:i+2]=='/-': depth+=1; i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif s[i:i+2]=='--':
            end=s.find('\n',i);i=len(s) if end<0 else end
        else: out.append(s[i]);i+=1
    result=[]
    for line in re.findall(r'^\s*(?:public\s+)?import[ \t]+([^\n]+)$', ''.join(out), re.M):
        for name in line.split():
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name):raise ValueError(f'Unsupported import syntax in {p}: {line}')
            result.append(name)
    return result

def git_revision(p):
    revision=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'], text=True).strip()
    if subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--']).returncode:
        raise ValueError(f'Modified tracked dependency files: {p.name}')
    return revision

def resolve_packages(mathlib, tools):
    wanted=json.loads((ROOT/'dependencies.lock.json').read_text())['packages']
    original=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    entries={e['name']:e for e in original}
    paths={};manifest=[]
    for e in wanted:
        name=e['name']
        candidates=[mathlib] if name=='mathlib' else [mathlib/'.lake/packages'/name,ROOT/'.lake/packages'/name]
        p=next((p.resolve() for p in candidates if p.is_dir()),None)
        if p is None: raise ValueError(f'Missing pinned dependency {name}; obtain the project Mathlib cache first')
        if git_revision(p)!=e['rev']: raise ValueError(f'Wrong pinned dependency revision: {name}')
        paths[name]=p
        old=entries[name]
        manifest.append({'type':'path','name':name,'scope':old.get('scope',''),'dir':str(p),
                         'inherited':name!='mathlib','configFile':old.get('configFile','lakefile.lean'),
                         'manifestFile':old.get('manifestFile','lake-manifest.json')})
    pins=json.loads((SPEC/'toolchain.lock.json').read_text())
    for name in ['lean4export','lean4checker']:
        p=(tools/'comparator/.lake/packages'/name).resolve()
        if not p.is_dir() or git_revision(p)!=pins[name]['revision']:
            raise ValueError(f'Missing/wrong official {name} checkout; run comparator-setup.sh')
        paths[name]=p
        manifest.append({'type':'path','name':name,'scope':'leanprover','dir':str(p),
                         'inherited':False,'configFile':'lakefile.toml','manifestFile':'lake-manifest.json'})
    return paths,manifest

def phase(root, fallback, module, external):
    ordered=[];active=set();seen=set()
    def visit(mod):
        if mod in seen:return
        if mod in active:raise ValueError(f'Cyclic imports: {mod}')
        rel=pathlib.Path(mod.replace('.','/')+'.lean')
        choices=[root] + ([fallback] if fallback else [])
        srcroot=next((r for r in choices if (r/rel).is_file()),None)
        if srcroot is None:
            if any((p/rel).is_file() or (p/'.lake/build/lib/lean'/rel.with_suffix('.olean')).is_file() for p in external):return
            if mod.split('.')[0] in ('Init','Lean','Std','Lake'):return
            raise ValueError(f'{root}: unresolved reference import {mod}; no submission fallback is allowed for challenge')
        active.add(mod)
        for dep in imports(srcroot/rel):visit(dep)
        active.remove(mod);seen.add(mod)
        ordered.append({'root':str(srcroot),'relative':str(rel),'module':mod})
    visit(module)
    return ordered

def prepare(output, tools, mathlib, reference, solution, config_path, module='PaperAssertions', fallback=ROOT):
    output=output.resolve();tools=tools.resolve();mathlib=mathlib.resolve()
    if output.is_relative_to(ROOT):raise ValueError('Run artifacts must be outside the distributed source tree')
    if output.exists() and any(output.iterdir()):raise ValueError(f'Refusing nonempty run directory: {output}')
    for p in [reference,solution,config_path]:
        if not p.exists():raise ValueError(f'Missing independent contract input: {p}')
    output.mkdir(parents=True,exist_ok=True)
    packages,entries=resolve_packages(mathlib,tools)
    template=(SPEC/'lakefile.lean.in').read_text()
    for token,value in [('MATHLIB',mathlib),('EXPORT',packages['lean4export']),('CHECKER',packages['lean4checker'])]:
        template=template.replace('@@'+token+'@@',json.dumps(str(value),ensure_ascii=False))
    (output/'lakefile.lean').write_text(template)
    (output/'lean-toolchain').write_text('leanprover/lean4:v4.24.0\n')
    manifest={'version':'1.1.0','packagesDir':'.lake/packages','packages':entries,
              'name':'rankwidthComparatorHarness','lakeDir':'.lake'}
    (output/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    external=list(packages.values())
    challenge=phase(reference.resolve(),None,module,external)
    submitted=phase(solution.resolve(),fallback.resolve() if fallback else None,module,external)
    for name,plan in [('Challenge',challenge),('Solution',submitted)]:
        (output/(name+'.lean')).write_text('import '+module+'\n')
        plan.append({'root':str(output),'relative':name+'.lean','module':name})
    paths=[output/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in external]
    stage={'leanPath':':'.join(map(str,paths)),'challenge':challenge,'solution':submitted}
    (output/'stage-plan.json').write_text(json.dumps(stage,indent=2)+'\n')
    config=json.loads(config_path.read_text())
    config.update(challenge_module='Challenge',solution_module='Solution')
    expected=['propext','Quot.sound','Classical.choice']
    if config.get('permitted_axioms')!=expected:raise ValueError('Unexpected permitted axiom policy')
    if config.get('enable_nanoda') is not False:raise ValueError('This pinned integration uses the official Lean kernel only')
    (output/'config.json').write_text(json.dumps(config,indent=2)+'\n')
    inputs={}
    for f in challenge+submitted:
        p=pathlib.Path(f['root'])/f['relative'];inputs[str(p)]=sha(p)
    for p in reference.rglob('*'):
        if p.is_file(): inputs[str(p.resolve())]=sha(p)
    audit_inputs=[config_path,SPEC/'toolchain.lock.json',SPEC/'lakefile.lean.in',ROOT/'dependencies.lock.json',ROOT/'lake-manifest.json',ROOT/'docs/RESULT_INVENTORY.json',ROOT/'docs/UNNUMBERED_OBLIGATIONS.json',
                  output/'stage-plan.json',output/'config.json',output/'lakefile.lean',output/'lake-manifest.json',output/'lean-toolchain']
    audit_inputs += list((ROOT/'scripts').glob('comparator-*.py'))+list((ROOT/'scripts').glob('comparator-*.sh'))
    audit_inputs += list(SPEC.glob('*.json'))+list((ROOT/'paper/source').glob('*.tex'))
    if (ROOT/'paper/PROVENANCE.json').exists():audit_inputs.append(ROOT/'paper/PROVENANCE.json')
    for p in audit_inputs:
        inputs[str(p.resolve())]=sha(p)
    snapshot={'inputs':inputs,'challenge_modules':len(challenge),'solution_modules':len(submitted),
              'reference_root':str(reference.resolve()),'solution_root':str(solution.resolve()),
              'definition_names':config.get('definition_names',[]),
              'theorem_names':config.get('theorem_names',[]),'dependency_revisions_verified':True}
    (output/'source-snapshot.json').write_text(json.dumps(snapshot,indent=2)+'\n')
    return snapshot

def validate_paper_coverage(config_path=SPEC/'config.json', coverage_path=SPEC/'coverage.json'):
    """Check the retained reviewed inventory, plus original TeX when present.

    Compact releases deliberately retain provenance rather than bundled paper
    bytes. That mode never claims to have rechecked the absent original paper.
    """
    config=json.loads(config_path.read_text())
    coverage=json.loads(coverage_path.read_text())
    provenance=json.loads((ROOT/'paper/PROVENANCE.json').read_text())
    inventory=json.loads((ROOT/'docs/RESULT_INVENTORY.json').read_text())
    paper_entries=[v for name,v in provenance.get('files',{}).items() if name.endswith('.tex')]
    if len(paper_entries)!=1:raise ValueError('Expected one original TeX hash in retained provenance')
    paper_sha=paper_entries[0]['sha256']
    if coverage.get('paper_source_sha256')!=paper_sha:
        raise ValueError('Coverage source hash does not match retained paper provenance')
    reviewed=[row for row in inventory if row.get('label') and row.get('kind') in ('theorem','lemma','proposition','corollary')]
    labelled=[row['label'] for row in reviewed]
    paper_remarks=sum(row.get('kind')=='remark' for row in inventory)
    if len(labelled)!=30 or len(set(labelled))!=30 or paper_remarks!=2:
        raise ValueError('Retained reviewed inventory must contain exactly 30 labelled results and 2 remarks')
    paper_validation='recorded_provenance_only'
    sources=list((ROOT/'paper/source').glob('*.tex'))
    if sources:
        if len(sources)!=1:raise ValueError('Expected one original paper TeX source when present')
        if sha(sources[0])!=paper_sha:raise ValueError('Present original TeX does not match retained provenance')
        text=sources[0].read_text()
        actual=[]
        for kind,body in re.findall(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}',text,re.S):
            labels=re.findall(r'\\label\{([^}]+)\}',body)
            if labels:actual.append(labels[0])
        if len(actual)!=30 or set(actual)!=set(labelled):raise ValueError('Actual paper labels differ from retained reviewed inventory')
        if len(re.findall(r'\\begin\{remark\}',text))!=paper_remarks:raise ValueError('Actual paper remark count differs from retained inventory')
        paper_validation='actual_paper_rechecked'
    rows=coverage.get('results',[])
    recorded=[row['label'] for row in rows]
    if len(recorded)!=len(set(recorded)):raise ValueError('Duplicate labelled result in coverage map')
    if set(recorded)!=set(labelled):
        raise ValueError(f'Paper coverage differs: missing={sorted(set(labelled)-set(recorded))}, extra={sorted(set(recorded)-set(labelled))}')
    targets=set(config.get('theorem_names',[]))
    remarks=coverage.get('remarks',[])
    if len(remarks)!=paper_remarks:raise ValueError('Remark inventory coverage differs from retained reviewed inventory')
    for row in rows+remarks:
        label=row.get('label') or row.get('number')
        if not row.get('manual_assertions'):raise ValueError(f'No independently written assertion for {label}')
        if not set(row['manual_assertions']).issubset(row.get('assertions',[])):raise ValueError('Manual assertion absent from its result mapping')
        if not row.get('assertions'):raise ValueError(f'No contract assertions for {label}')
        missing=set(row['assertions'])-targets
        if missing:raise ValueError(f'Contracts absent from official configuration for {label}: {sorted(missing)}')
        if row.get('status')!='complete':raise ValueError(f'Contract coverage not complete for {label}: {row.get("status")}')
    if config.get('definition_names'):raise ValueError('Paper challenge cannot use definition holes')
    return {'labelled_results':len(labelled),'remarks':len(remarks),'configured_theorems':len(targets),
            'paper_source_sha256':paper_sha,'paper_validation':paper_validation,
            'paper_bytes_rechecked':paper_validation=='actual_paper_rechecked',
            'inventory_coverage':'complete','semantic_translation':'requires the separate source-to-paper review'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=pathlib.Path,required=True)
    p.add_argument('--tools',type=pathlib.Path,required=True)
    p.add_argument('--mathlib',type=pathlib.Path,default=pathlib.Path(os.environ.get('RW_MATHLIB_ROOT',ROOT/'.lake/packages/mathlib')))
    p.add_argument('--reference',type=pathlib.Path,default=SPEC/'reference')
    p.add_argument('--solution',type=pathlib.Path,default=SPEC/'solution')
    p.add_argument('--config',type=pathlib.Path,default=SPEC/'config.json')
    p.add_argument('--module',default='PaperAssertions')
    p.add_argument('--standalone',action='store_true')
    a=p.parse_args()
    result=prepare(a.output,a.tools,a.mathlib,a.reference,a.solution,a.config,a.module,None if a.standalone else ROOT)
    print(json.dumps({k:v for k,v in result.items() if k!='inputs'},indent=2))

if __name__=='__main__':main()
