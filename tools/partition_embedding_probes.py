"""Selected-root cover observations with exact bounded ideal responses."""
from grandportage import store as S,format as F,verify as V

def probe(case,route):
 d=case['inputs'];models=[d['parent']]+d['branches']
 if len(d['branches'])!=2:raise ValueError('Two-branch controls only')
 for m in models:
  if m['field']!='Q' or m['variables']!=['x'] or m['equations']!=['x^2-2'] or m['selected_real_interval'] not in (['1','2'],['-2','-1']):raise ValueError('Unsupported selected-root control')
 g=S.Graph();g.apply(F.meta_event())
 for mid,m in zip(['M','B1','B2'],models):
  lo,hi=m['selected_real_interval'];g.apply(dict(ev='model',id=mid,what=mid,characteristic=0,coefficient_domain='Q',point_universe='REAL_CLOSURE',ring_vars=m['variables'],generators=m['equations'],embedding=dict(var='x',kind='REAL',isolating_interval=dict(lo=lo,hi=hi))))
 g.apply(dict(ev='claim',id='C',model='M',kind='PREDICATE',statement='branches cover parent',established_by='READ',ladder='claimed'))
 g.apply(dict(ev='partition',id='P',parent='M',branches=['B1','B2'],exhaustive='C',why='selected-point cover'));g.validate();calls=[]
 class ExactSameIdealBackend:
  def membership(self,ring,target,generators,**kw):
   if ring!=['x'] or target!='1' or generators!=['x^2-2']:raise ValueError('Unsupported membership query')
   calls.append('proper ideal membership');return dict(is_member=False,reduced='1')
  def partition_cover(self,ring,parent,branches,**kw):
   if ring!=['x'] or parent!=['x^2-2'] or branches!=[['x^2-2'],['x^2-2']]:raise ValueError('Unsupported cover query')
   calls.append('identical ideals cover');return True,dict(why='identical closed ideals',uncovered=[])
 verdict,why=V.partition_exhaustiveness(g,'P',_backend=ExactSameIdealBackend())
 return dict(observed_verdict='ACCEPT' if verdict==V.COVERS else 'REFUSE',reason=why,raw_verdict=verdict,backend_calls=calls,external_execution=False,scope='Actual native partition verifier; exact identical-ideal stub, no CAS or persisted verdict.')
