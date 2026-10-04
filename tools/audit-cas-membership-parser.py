"""Offline membership transcript controls; injected answers, no live CAS."""
import hashlib,json
from pathlib import Path
from grandportage import cas,groebner as G
r=Path(__file__).resolve().parents[1]
rows=[]
for name,matrix,expected in [('valid','GP_M[1,1]=1\nGP_M[2,1]=0',['1','0']),('missing_first','GP_M[2,1]=0',['0','0']),('duplicate_first','GP_M[1,1]=0\nGP_M[1,1]=1\nGP_M[2,1]=0',['0','0'])]:
 def runner(p,t):
  body='@@GP_RED:\n0' if p.outputs==['GP_RED'] else '@@GP_M:\n'+matrix
  return {'returncode':0,'aborted':False,'stdout':body+'\n'+p.completion_marker+'\n','stderr':'','argv':['injected']}
 backend=cas.SingularBackend(runner=runner,binary_version='test-double')
 answer=backend.membership(['x','y'],'x',['x','y'])
 assert answer['is_member'] and answer['cofactors']==expected
 try:
  G.check_membership_identity('x',['x','y'],answer['cofactors'],['x','y']); exact=True
 except G.CertificateError:exact=False
 assert exact==(name=='valid')
 rows.append({'control':name,'producer':answer,'exact_checker_accepts':exact,'attached_certificate':backend.executions[-1].artifact.certificate is not None,'can_record':backend.can_record_verdicts})
report={'source_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'observations':rows,'scope':'Injected backend answers test producer parsing. Missing/duplicate rows yield incorrect candidate certificates; exact replay refuses. No native graph admission or live Singular failure claimed.'}
(r/'reports/CAS-MEMBERSHIP-PARSER-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(rows,indent=2))
