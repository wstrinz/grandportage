"""Replay neutral section receipts at the frozen fold boundary; never run a CAS."""
from copy import deepcopy
from grandportage import store as S, format as F, verify as V, provenance as P
from tests.test_artifacts import _artifact,_manifest

def probe(case,route):
 d=case['inputs'];src=d['source'];dst=d['target']
 if src['field']!='Q' or dst['field']!='Q':raise ValueError('Only exact rational section controls supported')
 if set(d['section'])!=set(d['eliminated']):raise ValueError('Section must name eliminated variables')
 if set(src['variables'])!=set(dst['variables'])|set(d['eliminated']):raise ValueError('Invalid variable partition')
 g=S.Graph();g.apply(F.meta_event(),source='neutral section control',lineno=1)
 events=[dict(ev='model',id='SOURCE',what='source',characteristic=0,ring_vars=src['variables'],generators=src['equations']),dict(ev='model',id='TARGET',what='target',characteristic=0,ring_vars=dst['variables'],generators=dst['equations'],eliminated=d['eliminated']),dict(ev='edge',id='E',src='SOURCE',dst='TARGET',type='IMAGE_CLOSURE',map_kind='POLYNOMIAL',why='retained-coordinate projection',built_by_operation='Eliminate')]
 for i,e in enumerate(events):g.apply(e,source='neutral section control',lineno=i+2)
 g.validate()
 def representation(rows):
  return dict(method='polynomial_section_v1',section=d['section'],source_ring_vars=src['variables'],target_ring_vars=dst['variables'],eliminated=d['eliminated'],source_generators=src['equations'],target_generators=dst['equations'],images={v:d['section'].get(v,v) for v in src['variables']},rows=[dict(source_generator=x['equation'],substituted=x['substitution_result'],cofactors=x['cofactors']) for x in rows])
 proof=representation(d['proof_rows']);bound=proof if d['previously_bound_rows'] is None else representation(d['previously_bound_rows'])
 event=V._verdict_event(g,'elimination','E',V.SECTION_VERIFIED,'offline producer envelope',bound,execution=_manifest(_artifact()))
 event['representation']=deepcopy(proof)
 current,reason=P.current_verdict(g,event)
 try:g.apply(event,source='offline producer envelope',lineno=5)
 except S.GraphError as exc:return dict(observed_verdict='REFUSE',reason=str(exc),freshness_current=current,external_execution=False)
 active=g.edges['E'].get('contraction_verdict')
 return dict(observed_verdict='ACCEPT' if active==V.SECTION_VERIFIED else 'REFUSE',reason=reason,active_section=active,freshness_current=current,execution_descriptor='fabricated historical test metadata; no actual producer execution or binary probe',external_execution=False,scope='Admission of section evidence only; no no-invention verdict or complete transport asserted')
