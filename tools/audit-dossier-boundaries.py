import copy, hashlib, json, subprocess, tempfile, sys
from pathlib import Path
from grandportage import dossier as D
ROOT=Path(__file__).resolve().parents[1]
fixture=ROOT/'oracle/checkout/fixtures/dossier/synthetic/dossier.json'
value=json.loads(fixture.read_text(encoding='utf-8'))
rows=[]
def capture(name, doc):
    row={'name':name,'source_status':doc['source']['audit']['status'],'profiles':{p['id']:p['status'] for p in doc['profiles']},'files':doc['source']['audit']['files']}
    rows.append(row)
    return row
v=copy.deepcopy(value)
v['artifacts'][0]['replay']={'status':'PASS','command':'nonexistent-command-never-executed','receipt':'authored assertion only'}
a=capture('authored replay PASS without source audit',D.build(v))
assert a['source_status']=='UNCHECKED' and a['profiles']['SYNTHETIC.PUBLICATION_FLAG']=='READY'
v['profiles'][0]['criteria'].append({'id':'AUDIT.FRESH','kind':'SOURCE_FRESH','description':'Require clean source'})
a=capture('same input with freshness criterion',D.build(v))
assert a['profiles']['SYNTHETIC.PUBLICATION_FLAG']=='NOT_READY'
repo=Path(tempfile.mkdtemp(prefix='dossier-crlf-',dir=ROOT/'tmp'))
def git(*args):
    return subprocess.check_output(['git','-C',str(repo),*args],stderr=subprocess.PIPE).decode().strip()
git('init','-q'); git('config','core.autocrlf','false')
for name in ('authority.md','proof.txt'):
    (repo/name).write_bytes((fixture.parent/name).read_bytes().replace(b'\r\n',b'\n').replace(b'\n',b'\r\n'))
git('add','authority.md','proof.txt')
git('-c','user.name=Phase0 synthetic audit','-c','user.email=phase0@example.invalid','-c','commit.gpgsign=false','commit','-qm','Synthetic CRLF dossier fixture')
v=copy.deepcopy(value); v['source']['expected_commit']=git('rev-parse','HEAD')
a=capture('CRLF working tree LF-normalized audit',D.build(v,source_root=repo))
b=capture('same committed CRLF blobs pinned audit',D.build(v,source_root=repo,source_ref='HEAD'))
assert a['source_status']=='CURRENT_CLEAN'
assert b['source_status']=='STALE' and all(f['status']=='DIGEST_MISMATCH' for f in b['files'])
replay=subprocess.run([sys.executable,'-B',str(fixture.parent/'verify_synthetic.py')],capture_output=True,text=True)
assert replay.returncode != 0 and 'FileNotFoundError' in replay.stderr
rows.append({'name':'retained synthetic replay script','exit_code':replay.returncode,'stderr':replay.stderr,'scope':'Fixture packaging failure, not mathematical replay'})
report={'scope':'Synthetic offline derived-read-model diagnostics; no campaign harvest or graph authority. Commands in authored replay metadata were not executed.','oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((ROOT/'oracle/checkout/grandportage/dossier.py').read_bytes()).hexdigest(),'controls':rows}
(ROOT/'reports/DOSSIER-BOUNDARIES-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('5 dossier controls verified')
