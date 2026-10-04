import copy, contextlib, hashlib, io, json, os, tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from grandportage import cli, dossier as D, release as R
ROOT=Path(__file__).resolve().parents[1]
work=Path(tempfile.mkdtemp(prefix='materializer-boundary-',dir=ROOT/'tmp'))
source=work/'source';source.mkdir()
fixture=ROOT/'oracle/checkout/fixtures/dossier/synthetic'
for name in ['authority.md','proof.txt','verify_synthetic.py','synthetic-receipt.json']:
    (source/name).write_bytes((fixture/name).read_bytes())
manifest=ROOT/'oracle/checkout/fixtures/release/synthetic/release.json'
def fake_git(root,*args):return ('0000000123456789' if args[0]=='rev-parse' else ''),None
rows=[]
with patch.object(D,'_git',fake_git):
    plan=R.build_path(manifest,source_root=source)
    original=R.shutil.copyfile
    def copy_changed(src,dst,*args,**kwargs):
        if Path(src).name=='proof.txt':Path(src).write_text('changed between hash and copy\n',encoding='utf-8')
        return original(src,dst,*args,**kwargs)
    with patch.object(R.shutil,'copyfile',copy_changed):
        R.materialize(plan,source,work/'archive-race')
    actual=R._digest(work/'archive-race/receipts/proof.txt')
    bound=next(i['sha256'] for i in plan['inventory'] if i['id']=='SYNTHETIC.PROOF').removeprefix('sha256:')
    assert actual!=bound
    rows.append({'name':'injected source change after digest before copy','archive_created':True,'expected_digest':bound,'archived_digest':actual,'scope':'deterministic copy-boundary injection; Git cleanliness mocked; not an observed external race'})
    (source/'proof.txt').write_bytes((fixture/'proof.txt').read_bytes())
    modified=copy.deepcopy(plan);modified['inventory'][0]['license_status']='EXCLUDE'
    R.materialize(modified,source,work/'archive-mutated-plan')
    assert modified['history']==plan['history']
    rows.append({'name':'mutated internal plan retains readiness and fingerprint','archive_created':True,'license':'EXCLUDE','scope':'direct API caller modification only; normal CLI rebuilds plan'})
# Plain writer controls use only scratch files.
def invoke(path,protected=(),force=False):
    with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()):
        return cli._write_named_derived_output(SimpleNamespace(output=str(path),force=force),'derived\n',protected=protected)
target=work/'plain.txt';target.write_text('original\n',encoding='utf-8')
assert invoke(target)==2 and target.read_text()=='original\n'
rows.append({'name':'existing output without force','exit_code':2,'original_preserved':True})
assert invoke(target,[str(target)],True)==2
rows.append({'name':'identical protected path with force','exit_code':2,'original_preserved':True})
collision=work/'collision.txt';temp=Path(str(collision)+'.'+str(os.getpid())+'.tmp');temp.write_text('preexisting sentinel\n',encoding='utf-8')
try:invoke(collision)
except FileExistsError:pass
else:raise AssertionError('expected exclusive-create refusal')
assert not temp.exists() and not collision.exists()
rows.append({'name':'preexisting PID temporary file','exception':'FileExistsError','preexisting_temp_deleted':True,'target_created':False})
casepath=work/'ProtectedCase.txt';casepath.write_text('protected\n',encoding='utf-8')
alias=casepath.with_name('protectedcase.txt')
if not alias.exists():raise AssertionError('control requires case-insensitive filesystem')
assert invoke(alias,[str(casepath)],True)==0 and casepath.read_text()=='derived\n'
rows.append({'name':'case-alias protected input on Windows','exit_code':0,'protected_input_replaced':True,'scope':'same-file spelling on this case-insensitive filesystem; scratch data only'})
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Synthetic private diagnostics, no production input changed; no mathematical admission tested.','controls':rows}
(ROOT/'reports/MATERIALIZATION-BOUNDARY-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('6 materialization/output controls verified')
