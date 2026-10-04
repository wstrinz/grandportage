"""Replay product identities separately from proposed branch construction."""
from grandportage import product_split as P, operations as O

def probe(case, route):
    d = case['inputs']
    spec = dict(schema=P.SCHEMA, characteristic=d['characteristic'], ring_vars=d['variables'], unit_generators=d['declared_units'], receipts=[dict(id='receipt', **d['identity'])])
    try:
        if d['question'] == 'check_identity':
            report = P.verify(spec)
            return dict(observed_verdict='ACCEPT', reason='Exact product identity verified; interpretation premises remain open.', receipt=report, external_execution=False)
        if d['question'] != 'construct_from_matching_generator':
            raise RuntimeError('Unsupported product question')
        op = O.product_split('parent', d['variables'], d['parent_equations'], spec, 'receipt', coefficient_domain='Q', point_universe='ALGEBRAIC_CLOSURE', open_conditions=d['open_guards'])
        models = [e for e in op.events if e['ev'] == 'model']
        assert len(models) == 2
        assert all(m.get('open_conditions', []) == d['open_guards'] for m in models)
        assert not any(e['ev'] == 'verdict' for e in op.events)
        return dict(observed_verdict='ACCEPT', reason='Proposed branches constructed under the matching-generator contract; no coverage verdict emitted.', event_kinds=[e['ev'] for e in op.events], branch_equations=[m['generators'] for m in models], external_execution=False)
    except (P.ProductSplitError, ValueError) as exc:
        return dict(observed_verdict='REFUSE', reason=str(exc), external_execution=False)
