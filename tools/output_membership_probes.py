"""Neutral output-membership controls; producer metadata is simulated, never executed."""
from copy import deepcopy
from grandportage import store as S,format as F,provenance as P,verify as V
from tests.test_artifacts import _artifact,_manifest

def probe(case,route):
 d=case['inputs'];src=d['source'];dst=d['output']
 if src['field']!='Q' or dst['field']!='Q':raise ValueError('Only rational controls supported')
 if d['execution_evidence'] not in ('producer_trace','no_execution'):raise ValueError('Unsupported execution evidence')
 if dst['variables']!=[v for v in src['variables'] if v not in d['eliminated']]:raise ValueError('Invalid retained partition')
 g=S.Graph();g.apply(F.meta_event(),source='output control',lineno=1)
 for i,e in enumerate([dict(ev='model',id='S',what='source',characteristic=0,ring_vars=src['variables'],generators=src['equations']),dict(ev='model',id='T',what='output',characteristic=0,ring_vars=dst['variables'],generators=dst['equations'],eliminated=d['eliminated']),dict(ev='edge',id='E',src='S',dst='T',type='IMAGE_CLOSURE',map_kind='POLYNOMIAL',why='eliminate coordinates',built_by_operation='Eliminate')]):g.apply(e,source='output control',lineno=i+2)
 g.validate()
 def rep(rows):return dict(cofactors=[x['cofactors'] for x in rows],targets=[x['equation'] for x in rows],generators=src['equations'],ring_vars=src['variables'],target_ring_vars=dst['variables'],eliminated=d['eliminated'])
 proof=rep(d['membership_rows']);bound=proof if d['previously_bound_rows'] is None else rep(d['previously_bound_rows'])
 execution=_manifest(_artifact()) if d['execution_evidence']=='producer_trace' else P.native_execution_provenance()
 event=V._verdict_event(g,'operation','E','VERIFIED','offline membership control',bound,execution=execution);event['representation']=deepcopy(proof)
 current,reason=P.current_verdict(g,event)
 try:g.apply(event,source='output control',lineno=5)
 except S.GraphError as exc:return dict(observed_verdict='REFUSE',reason=str(exc),external_execution=False)
 active=g.edges['E'].get('output_verdict')
 return dict(observed_verdict='ACCEPT' if active=='VERIFIED' else 'REFUSE',reason=reason,current=current,active_output=active,external_execution=False,execution_evidence=d['execution_evidence'],limitation='Producer trace is fabricated test metadata. No CAS or binary probe; no output completeness claimed.')
