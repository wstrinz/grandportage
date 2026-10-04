import contextlib,hashlib,importlib.util,io,json,tempfile
from pathlib import Path
from grandportage import cli,frontier_bundle as B
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('bundle_tests',ROOT/'oracle/checkout/tests/test_frontier_bundle.py')
T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
work=Path(tempfile.mkdtemp(prefix='frontier-boundary-',dir=ROOT/'tmp'))
rows=[]
def build(name,receipt):
    root=work/name;root.mkdir()
    manifest=T._write_bundle(root,{'only':receipt})
    return manifest,B.build_path(manifest)
v=T._receipt([T._observation('A')]);v['open_items']=['A','A']
_,r=build('duplicate-open',v)
assert r['receipts'][0]['open_count']==2 and r['counts']['open']==1
rows.append({'name':'duplicate open list accepted','receipt_open_count':2,'aggregate_open_count':1})
_,r=build('newline-id',T._receipt([T._observation('A\n')]))
assert r['items'][0]['id']=='A\n'
rows.append({'name':'trailing newline semantic ID','accepted_id':r['items'][0]['id']})
_,r=build('missing-replacement',T._receipt([T._observation('A',state='CLOSED',status='RESOLVED',replacements=['ABSENT'])]))
assert r['items'][0]['replacement_ids']==['ABSENT']
rows.append({'name':'single receipt absent replacement','accepted':True,'scope':'Replacement existence is checked for supersession resolutions, not lone observations; no theorem admitted'})
for label,target_kind in [('overwrite-manifest','manifest'),('overwrite-receipt','receipt')]:
    manifest,_=build(label,T._receipt([T._observation('A')]))
    target=manifest if target_kind=='manifest' else manifest.parent/'only.json'
    before=hashlib.sha256(target.read_bytes()).hexdigest()
    with contextlib.redirect_stdout(io.StringIO()):code=cli.main(['frontier-bundle',str(manifest),'--emit-review',str(target)])
    after=json.loads(target.read_text(encoding='utf-8'))
    assert code==0 and after['schema']=='gp-frontier-current-review/v1'
    rows.append({'name':label,'exit_code':code,'input_overwritten':True,'original_sha256':before,'output_schema':after['schema']})
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Five private synthetic diagnostics, no original source or campaign mutated; derived-view consistency only.','controls':rows}
(ROOT/'reports/FRONTIER-BUNDLE-BOUNDARIES.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('5 frontier bundle controls verified')
