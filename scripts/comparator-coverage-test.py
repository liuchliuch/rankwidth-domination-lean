#!/usr/bin/env python3
"""Test coverage validation on a release tree, including paper-free compact mode.
Pure local JSON/source inventory checks; no compiler, network, or Comparator run.
"""
import argparse, copy, importlib.util, json, pathlib, shutil, tempfile

def load(project, key):
    p=project/'scripts/comparator-prepare.py'
    spec=importlib.util.spec_from_file_location(key,p)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project',type=pathlib.Path,required=True)
    p.add_argument('--report',type=pathlib.Path)
    a=p.parse_args();project=a.project.resolve()
    baseline=load(project,'release_coverage').validate_paper_coverage()
    has_paper=bool(list((project/'paper/source').glob('*.tex')))
    assert baseline['paper_bytes_rechecked']==has_paper
    required=['scripts/comparator-prepare.py','paper/PROVENANCE.json','docs/RESULT_INVENTORY.json',
              'verification/comparator/config.json','verification/comparator/coverage.json']
    checks=[]
    with tempfile.TemporaryDirectory(prefix='comparator-coverage-test-') as temp:
        root=pathlib.Path(temp)
        for rel in required:
            out=root/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(project/rel,out)
        validator=load(root,'compact_coverage')
        compact=validator.validate_paper_coverage()
        assert compact['paper_validation']=='recorded_provenance_only'
        assert compact['paper_bytes_rechecked'] is False
        checks.append({'case':'compact_without_paper_bytes','status':'passed'})
        config=root/'verification/comparator/config.json';coverage=root/'verification/comparator/coverage.json'
        inventory=root/'docs/RESULT_INVENTORY.json'
        original={path:path.read_text() for path in [config,coverage,inventory]}
        def change(path,fn):
            x=json.loads(path.read_text());fn(x);path.write_text(json.dumps(x))
        cases=[
            ('missing_label',coverage,lambda x:x['results'].pop(),'Paper coverage differs'),
            ('wrong_source_hash',coverage,lambda x:x.update(paper_source_sha256='0'*64),'retained paper provenance'),
            ('missing_manual_contract',coverage,lambda x:x['results'][0].update(manual_assertions=[]),'No independently written assertion'),
            ('unconfigured_contract',config,lambda x:x['theorem_names'].clear(),'Contracts absent'),
            ('pending_result',coverage,lambda x:x['results'][0].update(status='pending'),'not complete'),
            ('incomplete_retained_inventory',inventory,lambda x:x.pop(0),'exactly 30 labelled results'),
            ('missing_remark',coverage,lambda x:x['remarks'].clear(),'Remark inventory'),
            ('definition_hole',config,lambda x:x.update(definition_names=['hole']),'cannot use definition holes')]
        for name,path,fn,marker in cases:
            for file,text in original.items():file.write_text(text)
            change(path,fn)
            try:validator.validate_paper_coverage()
            except ValueError as e:
                if marker not in str(e):raise AssertionError(f'{name}: unexpected failure: {e}')
            else:raise AssertionError(f'{name}: invalid inventory was accepted')
            checks.append({'case':name,'status':'passed'})
    result={'status':'passed','scope':'release-tree coverage portability, not proof comparison',
            'release_tree_paper_validation':baseline['paper_validation'],
            'official_comparator':'not_run','checks':checks}
    if a.report:
        a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
