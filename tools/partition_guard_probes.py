"""Observe coverage of zero-ideal loci with explicitly declared open guards."""
from grandportage import store as S,format as F,verify as V

def probe(case,route):
 d=case['inputs'];models=[d['parent']]+d['branches']
 if len(d['branches'])!=2:raise ValueError('Two-branch controls only')
 for m in models:
  if m['field']!='Q' or m['variables']!=['x'] or m['equations']!=[] or m['nonzero'] not in ([],['x']):raise ValueError('Unsupported zero-ideal control')
 g=S.Graph();g.apply(F.meta_event())
 for mid,m in zip(['M','B1','B2'],models):g.apply(dict(ev='model',id=mid,what=mid,characteristic=0,coefficient_domain='Q',point_universe='BASE',ring_vars=m['variables'],generators=m['equations'],open_conditions=m['nonzero']))
 g.apply(dict(ev='claim',id='C',model='M',kind='PREDICATE',statement='branches cover parent',established_by='READ',ladder='claimed'))
 g.apply(dict(ev='partition',id='P',parent='M',branches=['B1','B2'],exhaustive='C',why='coverage control'));g.validate();calls=[]
 class ExactZeroIdealBackend:
  def membership(self,ring,target,generators,**kw):
   if ring!=['x'] or target!='1' or generators!=[]:raise ValueError('Unsupported membership query')
   calls.append(dict(operation='membership',target=target,generators=generators));return dict(is_member=False,reduced='1')
  def partition_cover(self,ring,parent,branches,**kw):
   if ring!=['x'] or parent!=[] or branches!=[[],[]]:raise ValueError('Unsupported ideal cover query')
   calls.append(dict(operation='partition_cover',parent=parent,branches=branches));return True,dict(why='intersection of zero ideals is zero',uncovered=[])
 verdict,why=V.partition_exhaustiveness(g,'P',_backend=ExactZeroIdealBackend())
 return dict(observed_verdict='ACCEPT' if verdict==V.COVERS else 'REFUSE',reason=why,raw_verdict=verdict,backend_calls=calls,origin_membership=dict(parent=not d['parent']['nonzero'],branches=[not m['nonzero'] for m in d['branches']]),external_execution=False,scope='Exact zero-ideal backend stub; actual partition verifier, no persisted verdict or live CAS.')
