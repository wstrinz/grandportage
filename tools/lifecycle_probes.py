"""Frozen lifecycle and provenance probes. Observations are not new held claims."""
import copy
from grandportage import store as S, check as C, kernel as K, verify as V, format as F

def decision(ok, reason, **extra):
    return dict(observed_verdict='ACCEPT' if ok else 'REFUSE',reason=str(reason),**extra)

def fold(records):
    return S.Graph().apply_all([(copy.deepcopy(e),'corpus',i) for i,e in enumerate(records)]).validate()

def snapshot(g):
    return {name:{key:{k:v for k,v in value.items() if not k.startswith('_')} for key,value in sorted(getattr(g,name).items())}
            for name in ('models','claims','edges','inferences')}

def probe(case,route):
    d=case['inputs'];action=route['action']
    if d.get('vocabulary') == 'lifecycle-scenario/v1':
        from lifecycle_inputs import decode
        d=decode(d)
    if action in ('fold','no_rule','clean','absent','successors','order'):
        try:
            g=fold(d['records'])
            if action=='order':
                other=fold(d['prefix']+d['new']+d['old'])
                a,b=snapshot(g),snapshot(other)
                # Source positions are diagnostics, not semantic state.
                return decision(a==b,'Compared complete model/claim/edge/inference records after both branch orders.',forward=a,reverse=b)
        except (S.GraphError,K.SupersessionError) as exc:
            return decision(False,exc,refused_at='fold')
        findings=C.run(g)
        selected=[f.as_dict() for f in findings if f.rule in d.get('rules',[])]
        if action=='no_rule':ok=not selected
        elif action=='clean':ok=d['query_id'] in C.clean_inferences(g,findings)
        elif action=='absent':ok=d['query_id'] in getattr(g,d['registry'])
        elif action=='successors':ok=sorted(g.claims[d['query_id']].get('superseded_by',[]))==sorted(d['successors'])
        else:ok=True
        return decision(ok,'Pinned fold and selected lifecycle query; no proof of declared predicates.',
                        findings=selected,clean_inferences=C.clean_inferences(g,findings),
                        withdrawn_edges=sorted(C.withdrawn_edges(g)),
                        retractions=[list(key) for key in g.retractions],state=snapshot(g))
    if action=='receipt':
        from test_verdict_provenance import _identity_graph,_verdict
        g=_identity_graph();event=_verdict(g);event['id']='receipt.current'
        if d.get('legacy'):
            event={k:event[k] for k in ('ev','id','subject','of','verdict','why')}
            # The regression is an epoch-0 log; native logs require provenance fields.
            g=S.Graph()
            g.apply(dict(ev='model',id='M',what='a line',characteristic=0,ring_vars=['x'],generators=['x']))
            g.apply(dict(ev='claim',id='C',model='M',kind=K.IDENTITY,statement='x vanishes',lhs='x',rhs='0',ring_vars=['x'],identity_origin=K.DERIVED,established_by='RAN',ladder='exact-checked'))
        else:event.update(d.get('mutation',{}))
        if d.get('new_generator'):g=_identity_graph(d['new_generator'])
        if d.get('order'):
            valid=_verdict(g);valid['id']='receipt.valid'
            stale=copy.deepcopy(valid);stale['id']='receipt.stale';stale['kernel_epoch']=F.KERNEL_EPOCH-1
            for e in ([valid,stale] if d['order']=='valid_stale' else [stale,valid]):g.apply(e)
            active=g.claims['C'].get('identity_verdict')=='VERIFIED_DERIVED'
        else:
            g.apply(event);active=g.verdicts[event['id']]['current'] and g.claims['C'].get('identity_verdict')=='VERIFIED_DERIVED'
        return decision(active,'Receipt-binding observation using fabricated historical backend metadata.',
                        projected=g.claims['C'].get('identity_verdict'),
                        receipts={i:dict(current=e['current'],stale_reason=e['stale_reason']) for i,e in g.verdicts.items()},
                        external_execution=False)
    if action=='section':
        from test_verdict_provenance import _elimination_graph,_section_representation,_execution
        g=_elimination_graph();success=V._verdict_event(g,'elimination','E',V.SECTION_VERIFIED,'section checked',_section_representation(),execution=_execution())
        rejected=V._verdict_event(g,'elimination','E',V.SECTION_REJECTED,'different proof rejected',execution=_execution(with_trace=False))
        if d.get('mutation')=='missing':success.pop('representation')
        if d.get('mutation')=='proof':success['representation']['section']['y']='x^99'
        events={'success':success,'rejected':rejected}
        try:
            for name in d['sequence']:g.apply(events[name])
        except S.GraphError as exc:return decision(False,exc,refused_at='fold',external_execution=False)
        return decision(g.edges['E'].get('contraction_verdict')==V.SECTION_VERIFIED,
                        'Exact section arithmetic replays at fold; backend metadata is a fabricated fixture.',
                        projected=g.edges['E'].get('contraction_verdict'),
                        receipts={i:dict(current=e['current'],stale_reason=e['stale_reason']) for i,e in g.verdicts.items()},external_execution=False)
    raise ValueError(action)
