"""Neutral model-inventory diagnostics against the frozen GP implementation."""
from grandportage import store as S, check as C

def observe(d):
    if d['scenario']=='coverage_inventory':
        rows=lambda xs:[dict(axis=r['dimension'],at=r['indices'],name=r['description']) for r in xs]
        events=[dict(ev='model',id='context',desc='inventory',coverage_axes=d['asserted_dimensions'],declares=d['represented_indices'],touches=rows(d['construction_uses']),reads=rows(d['conclusion_uses']))]
        g=S.Graph().apply_all([(e,'inventory-corpus',i) for i,e in enumerate(events)]).validate()
        gaps=C.coverage_gaps(g,g.models['context']);findings=C.check_coverage(g)
        return dict(observed_verdict='REFUSE' if gaps else 'ACCEPT',reason='Only recorded-index coverage on asserted axes; no proof that represented constraints are sufficient.',gaps=gaps,findings=[f.as_dict() for f in findings],external_execution=False)
    if d['scenario']!='equation_refinement':raise ValueError('Unknown inventory scenario')
    types={'equations_forgotten':'NECESSARY_CONDITION','equivalent_presentations':'EQUIVALENCE'}
    events=[dict(ev='model',id=x,desc=x) for x in ['more_equations','fewer_equations']]
    events.append(dict(ev='edge',id='forget',src='more_equations',dst='fewer_equations',type=types[d['declared_relation']],refinement=True,why='source adds equations',map_kind='IDENTITY_MAP'))
    g=S.Graph().apply_all([(e,'inventory-corpus',i) for i,e in enumerate(events)]).validate()
    findings=C.check_refinement(g)
    return dict(observed_verdict='REFUSE' if findings else 'ACCEPT',reason='Legacy refinement-tag consistency only, not a check of actual ideal equality or independence of added equations.',findings=[f.as_dict() for f in findings],external_execution=False)

def probe(case,route):return observe(case['inputs'])
