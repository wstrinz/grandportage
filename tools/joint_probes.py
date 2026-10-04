"""Neutral joint-premise scenarios compiled only for the frozen oracle."""
from grandportage import store as S,check as C
KINDS={'universal_property':'PREDICATE','exhibited_point':'NONEMPTY','empty':'EMPTY'}
def probe(case,route):
    d=case['inputs'];events=[dict(ev='model',id=name,desc=name) for name in d['contexts']]
    for r in d.get('relations',[]):
        if r['relation']!='equations_forgotten':raise ValueError('Unknown relation')
        events.append(dict(ev='edge',id=r['name'],src=r['source'],dst=r['target'],type='NECESSARY_CONDITION',why='forgets equations'))
    premises=[]
    for index,p in enumerate(d['premises']):
        if 'missing_reason' in p:
            premises.append(dict(required_kind=KINDS[p['statement_class']],at=p['context'],missing_why=p['missing_reason']))
            continue
        name='PREMISE-'+str(index)
        c=dict(ev='claim',id=name,model=p['context'],kind=KINDS[p['statement_class']],statement=p['statement'])
        if c['kind']=='NONEMPTY':c.update(witness_kind='EXHIBITED',scope='Q')
        if c['kind']=='EMPTY':c['certificate']='UNIT_IDEAL_CERT'
        events.append(c)
        path=[]
        for step in p.get('route',[]):
            if step['direction'] not in ('forward','reverse'):raise ValueError('Invalid direction')
            path.append([step['relation'],'ALONG' if step['direction']=='forward' else 'AGAINST'])
        premises.append(dict(claim=name,path=path))
    inference=dict(ev='inference',id='RESULT',premises=premises,concludes_kind=KINDS[d['conclusion_class']],asserted=d['conclusion_text'])
    if 'cover' in d:
        cover=d['cover'];events.append(dict(ev='claim',id='EXHAUSTIVE',model=cover['parent'],kind='PREDICATE',statement='the branches exhaust the parent'))
        events.append(dict(ev='partition',id='COVER',parent=cover['parent'],branches=cover['branches'],exhaustive='EXHAUSTIVE',why='declared case split'))
        inference['via_partition']='COVER'
        if cover['include_exhaustiveness_premise']:premises.append(dict(claim='EXHAUSTIVE',path=[]))
    events.append(inference)
    try:g=S.Graph().apply_all([(e,'joint-corpus',i) for i,e in enumerate(events)]).validate()
    except S.GraphError as exc:return dict(observed_verdict='REFUSE',reason=str(exc),refused_at='fold')
    if 'cover' in d:
        # Conditional-rule isolation, not a forged claim that the cover was checked.
        if d['cover']['verification_assumption']!='exhaustive':raise ValueError('Missing explicit assumption')
        g.partitions['COVER']['exhaustive_verdict']='VERIFIED'
    allowed,trace=C.audit_inference(g,'RESULT')
    findings=C.run(g)
    rendered=C.render(findings,{},False)
    return dict(observed_verdict='ACCEPT' if allowed else 'REFUSE',reason='Conditional premise-route/coverage audit; no entailment or checked premise authority is inferred.',trace=trace,conclusion_context=g.inferences['RESULT']['concludes_at'],findings=[f.as_dict() for f in findings if f.rule==C.R_TRANSPORT],report_rendered=isinstance(rendered,str),external_execution=False)
