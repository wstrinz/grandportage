"""Separate universe compatibility, historical readability and untyped authority."""
from grandportage import store as S,format as F,kernel as K

def probe(case,route):
 d=case['inputs']
 if d['relation'] not in K.DECLARABLE_TYPES:raise ValueError('Unsupported relation')
 if d['question'] not in ('record_step','license_nonempty_along'):raise ValueError('Unsupported question')
 g=S.Graph();g.apply(F.meta_event())
 for mid,key in [('A','source_universe'),('B','target_universe')]:
  m=dict(ev='model',id=mid,what=mid,characteristic=0,ring_vars=d['variables'],generators=d['equations'])
  if d[key] is not None:m.update(coefficient_domain='Q',point_universe=d[key])
  g.apply(m)
 e=dict(ev='edge',id='E',src='A',dst='B',type=d['relation'],why='context control')
 if d['relation']==K.UNTYPED:e.update(debt_why=d['debt_reason'],map_kind=K.RATIONAL)
 else:e['map_kind']=K.IDENTITY_MAP if d['relation'] in (K.RESTRICTION,K.EQUIVALENCE) else K.POLYNOMIAL
 try:g.apply(e);g.validate()
 except S.GraphError as exc:return dict(observed_verdict='REFUSE',reason=str(exc),stage='structural_validation',external_execution=False)
 if d['question']=='record_step':return dict(observed_verdict='ACCEPT',reason='Native graph accepts the declaration; this is not a mathematical licence.',external_execution=False)
 result=K.transport(d['relation'],K.ALONG,K.NONEMPTY)
 return dict(observed_verdict='ACCEPT' if result.licensed else 'REFUSE',reason=result.reason,stage='conditional_transport',external_execution=False)
