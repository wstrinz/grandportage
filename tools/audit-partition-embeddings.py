"""Measure selected-root context at the partition coverage boundary."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import store as S,format as F,verify as V
records=[]
for mismatch in [False,True]:
 g=S.Graph();g.apply(F.meta_event());intervals={}
 for mid in ['M','B1','B2']:
  lo,hi=('-2','-1') if mismatch and mid!='M' else ('1','2');intervals[mid]=[lo,hi]
  g.apply(dict(ev='model',id=mid,what=mid,characteristic=0,coefficient_domain='Q',point_universe='REAL_CLOSURE',ring_vars=['x'],generators=['x^2-2'],embedding=dict(var='x',kind='REAL',isolating_interval=dict(lo=lo,hi=hi))))
 g.apply(dict(ev='claim',id='C',model='M',kind='PREDICATE',statement='branches cover parent',established_by='READ',ladder='claimed'))
 g.apply(dict(ev='partition',id='P',parent='M',branches=['B1','B2'],exhaustive='C',why='selected root cover'));g.validate();calls=[]
 class ExactSameIdealBackend:
  def membership(self,ring,target,generators,**kw):
   assert ring==['x'] and target=='1' and generators==['x^2-2'];calls.append('unit membership in proper ideal');return dict(is_member=False,reduced='1')
  def partition_cover(self,ring,parent,branches,**kw):
   assert ring==['x'] and parent==['x^2-2'] and branches==[['x^2-2'],['x^2-2']];calls.append('identical closed ideals cover');return True,dict(why='identical branch and parent ideals',uncovered=[])
 verdict,why=V.partition_exhaustiveness(g,'P',_backend=ExactSameIdealBackend());assert verdict==V.COVERS
 records.append(dict(mismatched_selection=mismatch,verdict=verdict,reason=why,intervals=intervals,point_scopes={mid:S.point_scope(g.models[mid]) for mid in intervals},backend_calls=calls,actual_cover=not mismatch))
assert records[0]['backend_calls']==records[1]['backend_calls']
report=dict(oracle_commit=r.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sources={n:r.sha(ROOT/'oracle/checkout'/n) for n in ['grandportage/store.py','grandportage/verify.py']},controls=records,scope='Actual native model/partition validation and verifier with exact identical-ideal backend stub; no live CAS or persisted verdict.',finding='point_scope omits selected embedding. Two negative-root branches of x^2-2 do not cover its positive-root parent, yet identical ideal-only coverage returns VERIFIED.',proposal='Bind selected-point context in cover checking. Require compatible selections or an explicit checked map/locus coverage theorem; do not treat equal polynomial ideals as equal selected models.')
(ROOT/'reports/PARTITION-EMBEDDING-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Matched roots cover; disjoint selected roots also reported covered despite omitted positive root.')
