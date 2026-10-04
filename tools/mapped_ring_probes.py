"""Paired exact map-checking and receipt-admission observations."""
from grandportage import store as S,format as F,verify as V,provenance as P

def probe(case,route):
 d=case['inputs']
 if d['question'] not in ('check_proof','admit_positive_receipt'):raise ValueError('Unsupported map question')
 if d['source']['field']!='Q' or d['target']['field']!='Q':raise ValueError('Only rational controls supported')
 if d['source']['variables']!=d['target']['variables']:raise ValueError('Shared-ring convention required')
 g=S.Graph();g.apply(F.meta_event())
 for mid,key in [('A','source'),('B','target')]:g.apply(dict(ev='model',id=mid,what=key,characteristic=0,ring_vars=d[key]['variables'],generators=d[key]['equations']))
 g.apply(dict(ev='edge',id='E',src='A',dst='B',type='EQUIVALENCE',map_kind='POLYNOMIAL',why='supplied polynomial maps',ring_iso=True,forward=d['point_forward'],inverse=d['point_inverse'],ring_iso_certificate=dict(schema='mapped_ring_iso_v1',forward_cofactors=d['target_pullback_rows'],inverse_cofactors=d['source_pullback_rows'])))
 g.validate();verdict,why=V.ring_iso(g,'E')
 if d['question']=='check_proof':return dict(observed_verdict='ACCEPT' if verdict==V.ISO_VERIFIED else 'REFUSE',reason=why,producer_verdict=verdict,external_execution=False)
 event=V._verdict_event(g,'ring_iso','E',V.ISO_VERIFIED,'synthetic positive receipt regardless of actual verifier result',execution=P.native_execution_provenance())
 current,reason=P.current_verdict(g,event)
 try:g.apply(event);g.validate()
 except S.GraphError as exc:return dict(observed_verdict='REFUSE',reason=str(exc),producer_verdict=verdict,external_execution=False)
 return dict(observed_verdict='ACCEPT' if g.edges['E'].get('ring_iso_verdict')==V.ISO_VERIFIED else 'REFUSE',reason=reason,current=current,producer_verdict=verdict,producer_reason=why,external_execution=False,scope='Deliberately synthetic positive native receipt; not the actual verifier output and not a claim of a live producer failure.')
