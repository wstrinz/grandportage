"""Measure operation-output proof replay versus producer provenance."""
from pathlib import Path
from copy import deepcopy
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import store as S,format as F,provenance as P,verify as V,groebner as G
from tests.test_artifacts import _artifact,_manifest

def graph(empty=False):
 g=S.Graph();g.apply(F.meta_event(),source='diagnostic',lineno=1)
 for i,e in enumerate([dict(ev='model',id='S',what='source',characteristic=0,ring_vars=['y','x'],generators=['x']),dict(ev='model',id='T',what='target',characteristic=0,ring_vars=['x'],generators=[] if empty else ['x'],eliminated=['y']),dict(ev='edge',id='E',src='S',dst='T',type='IMAGE_CLOSURE',map_kind='POLYNOMIAL',why='eliminate y',built_by_operation='Eliminate')]):g.apply(e,source='diagnostic',lineno=i+2)
 return g.validate()
proof=dict(cofactors=[['1']],targets=['x'],generators=['x'],ring_vars=['y','x'],target_ring_vars=['x'],eliminated=['y'])
records=[]
for mode in ['valid_producer','tampered_old_binding','invalid_reissued_producer','invalid_native','empty_native']:
 empty=mode=='empty_native';g=graph(empty);rep=deepcopy(proof)
 if empty:rep['cofactors']=[];rep['targets']=[]
 elif mode.startswith('invalid'):rep['cofactors']=[['0']]
 execution=P.native_execution_provenance() if mode.endswith('native') else _manifest(_artifact())
 event=V._verdict_event(g,'operation','E','VERIFIED','offline diagnostic',rep,execution=execution)
 if mode=='tampered_old_binding':event['representation']['cofactors']=[['0']]
 current,reason=P.current_verdict(g,event);g.apply(event,source='diagnostic',lineno=5)
 active=g.edges['E'].get('output_verdict')
 arithmetic=True
 if not empty:
  try:G.check_membership_identity('x',['x'],event['representation']['cofactors'][0],['y','x'],0)
  except G.CertificateError:arithmetic=False
 assert current==(mode in ['valid_producer','invalid_reissued_producer','empty_native'])
 assert (active=='VERIFIED')==current
 assert arithmetic==(mode in ['valid_producer','empty_native'])
 records.append(dict(control=mode,current=current,reason=reason,active=active,identity_valid=arithmetic))
report=dict(oracle_commit=r.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sources={n:r.sha(ROOT/'oracle/checkout'/n) for n in ['grandportage/store.py','grandportage/provenance.py','tests/test_artifacts.py']},controls=records,scope='Actual freshness and native Graph.apply. Producer traces fabricated; no CAS, binary probe, graph persistence or patched freshness.',finding='Nonempty operation-output cofactors are not arithmetically replayed at fold under producer provenance. Old binding rejects tampering; native empty-trace eligibility rejects nonempty output but accepts the vacuous zero target. This is a trusted-producer boundary, not a proven live producer error.',proposal='Replay each output membership and exact input partition at admission; preserve zero-output vacuity without granting completeness.')
(ROOT/'reports/OPERATION-REPLAY-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Five operation custody controls passed.')
