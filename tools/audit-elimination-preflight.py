"""Check elimination inclusion and JSON/native preflight boundaries offline."""
from pathlib import Path
import copy, hashlib, importlib.util, json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import groebner as G
rows=[]
def refused(name, fn):
 try: fn()
 except G.CertificateError as exc: rows.append({'id':name,'accepted':False,'message':str(exc)})
 else: raise AssertionError(name+' unexpectedly accepted')
base={'method':'groebner_elimination_v1','characteristic':0,'ring_vars':['y','x'],'eliminated':['y'],'source_generators':['x'],'basis':['x'],'target_generators':['x'],'source_in_basis':[['1']],'critical_pairs':[],'retained_in_target':[['1']]}
for name,cert in [('equal_ideal',base),('strict_upper_ideal',dict(base,basis=['1'],target_generators=['1'],source_in_basis=[['x']]))]:
 result=G.check_elimination_certificate(cert)
 rows.append({'id':name,'accepted':True,'checked':result})
refused('strict_upper_has_no_reverse_identity',lambda:G.check_membership_identity('1',['x'],['0'],['y','x']))
alias=copy.deepcopy(base);alias['retained_in_target']=alias['source_in_basis']
refused('acyclic_shared_rows',lambda:G.check_elimination_certificate(alias))
normalized=json.loads(json.dumps(alias));result=G.check_elimination_certificate(normalized)
rows.append({'id':'shared_rows_after_json_roundtrip','accepted':True,'checked':result})
cycle={};cycle['self']=cycle
refused('actual_cycle',lambda:G.preflight_certificate(cycle))
native=copy.deepcopy(base);native['basis']=[G.Polynomial(['y','x'],0,{(0,-1):1})]
refused('native_negative_power_object',lambda:G.check_elimination_certificate(native))
report={'controls':rows,'source_sha256':r.sha(ROOT/'oracle/checkout/grandportage/groebner.py'),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'findings':['Elimination accepts a strict upper ideal as intended: it proves only I intersect S subset J. At x=0, 1 is nonzero, independently excluding reverse ideal membership.','Global seen-object tracking rejects acyclic sharing as a cycle; ordinary serialized JSON with duplicated rows succeeds.','Certificate preflight rejects native Polynomial objects before arithmetic; the prior internal negative-exponent control does not enter this interface.'],'proposed_fix':'Document inclusion direction and retain separate no-invention evidence. Either declare tree-only native inputs or use active-ancestor cycle detection while charging repeated occurrences to the resource budget. Preserve rejection of non-JSON objects.','scope':'Seven bounded offline controls; no CAS, campaign read, graph mutation or frozen-source edit. No false mathematical acceptance established.'}
(ROOT/'reports/ELIMINATION-PREFLIGHT-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Seven elimination/preflight boundary controls verified.')
