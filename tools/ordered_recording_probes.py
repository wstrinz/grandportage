"""Translate neutral ordered-identity custody inputs to native SOS replay."""
from grandportage import format as F, store as S, verify as V, provenance as P

def probe(case, route):
    d=case['inputs']
    graph=S.Graph();graph.apply(F.meta_event())
    graph.apply(dict(ev='model',id='M',about='ANY_ORDERED',compute_in='Q',coefficient_domain='Q',characteristic=0,point_universe='BASE',ring_vars=d['variables'],generators=d['model_equations']))
    graph.apply(dict(ev='claim',id='E',model='M',kind='EMPTY',statement='no ordered-field zero',certificate='ORDERED_SOS_CERT',scope='ANY_ORDERED'))
    certificate=dict(method='rational_sos_cofactor_v1',ring_vars=d['variables'],generators=d['evidence_equations'],squares=d['squares'],cofactors=d['multipliers'])
    verdict,reason,rep=V.ordered_sos(graph,'E',certificate)
    if verdict!=V.CERT_VERIFIED:
        return dict(observed_verdict='REFUSE',reason=reason,stage='identity_verifier',external_execution=False)
    event=V._verdict_event(graph,'certificate','E',verdict,reason,rep,execution=P.native_execution_provenance())
    try:graph.apply(event)
    except S.GraphError as exc:
        return dict(observed_verdict='REFUSE',reason=str(exc),stage='receipt_replay',verifier_verdict=verdict,representation=rep,external_execution=False)
    reach=graph.claims['E'].get('certificate_reach')
    if reach!={'kind':'ORDERED'}:raise RuntimeError('Unexpected recorded reach')
    return dict(observed_verdict='ACCEPT',reason='Exact identity replayed and recorded with ordered-only reach.',stage='receipt_replay',reach=reach,external_execution=False)
