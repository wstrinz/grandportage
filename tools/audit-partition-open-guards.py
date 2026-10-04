"""Check whether open branch guards participate in partition verification."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import store as S,format as F,verify as V
records=[]
for guarded in [False,True]:
 g=S.Graph();g.apply(F.meta_event())
 for mid in ['M','B1','B2']:
  e=dict(ev='model',id=mid,what=mid,characteristic=0,coefficient_domain='Q',point_universe='BASE',ring_vars=['x'],generators=[])
  if guarded and mid!='M':e['open_conditions']=['x']
  g.apply(e)
 g.apply(dict(ev='claim',id='C',model='M',kind='PREDICATE',statement='branches cover parent',established_by='READ',ladder='claimed'))
 g.apply(dict(ev='partition',id='P',parent='M',branches=['B1','B2'],exhaustive='C',why='coverage control'));g.validate()
 calls=[]
 class ExactZeroIdealBackend:
  def membership(self,ring,target,generators,**kw):
   assert ring==['x'] and target=='1' and generators==[]
   calls.append(dict(operation='membership',ring=ring,target=target,generators=generators));return dict(is_member=False,reduced='1')
  def partition_cover(self,ring,parent,branches,**kw):
   assert ring==['x'] and parent==[] and branches==[[],[]]
   calls.append(dict(operation='partition_cover',ring=ring,parent=parent,branches=branches));return True,dict(why='intersection of two zero ideals is zero',uncovered=[])
 verdict,why=V.partition_exhaustiveness(g,'P',_backend=ExactZeroIdealBackend());assert verdict==V.COVERS
 records.append(dict(guarded=guarded,verdict=verdict,reason=why,backend_calls=calls,witness=dict(x=0,parent_member=True,branch_membership=[not guarded,not guarded]),branch_guards=[g.models[x].get('open_conditions',[]) for x in ['B1','B2']]))
assert records[0]['backend_calls']==records[1]['backend_calls']
report=dict(oracle_commit=r.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sources={n:r.sha(ROOT/'oracle/checkout'/n) for n in ['grandportage/verify.py','grandportage/store.py','grandportage/cas.py']},controls=records,scope='Native graph validation and actual partition verifier with an exact zero-ideal backend stub; no CAS or persisted verdict. Stub asserts every argument and gives mathematically exact answers to the ideal-only queries.',finding='Both open branches D(x) miss x=0 in parent A1, but omitted guards yield the same VERIFIED response as closed branches. Unlike synthesized verdict controls, the verifier itself returns the overstrong coverage result on the supplied backend answers.',proposal='Refuse guarded branches until coverage includes constructible/open conditions or a checked localization-aware certificate; retain closed cover positive control.')
(ROOT/'reports/PARTITION-OPEN-GUARD-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Closed cover accepted; open branches also accepted despite missing x=0; identical ideal-only backend queries.')
