"""Replay narrow factor and affine-pattern claims without model authority."""
from grandportage import factor_power as F, factor_power_contradiction as C

def probe(case, route):
    d = case['inputs']
    if d['exponent_limit'] != F.MAX_EXPONENT:
        raise ValueError('Requested profile differs from pinned exponent limit')
    factor = dict(schema=F.SCHEMA, characteristic=d['characteristic'], ring_vars=d['variables'], unit_generators=d['declared_units'], receipts=[dict(id='power', **d['power_identity'])])
    try:
        if d['question'] == 'check_power_identity':
            report = F.verify(factor)
        elif d['question'] == 'check_affine_contradiction_pattern':
            report = C.verify(dict(schema=C.SCHEMA, factor_power=factor, factor_receipt='power', pivot=d['pivot'], consequence=dict(id='second', **d['consequence'])))
        else:
            raise RuntimeError('Unsupported factor question')
    except (F.FactorPowerError, C.FactorPowerContradictionError) as exc:
        return dict(observed_verdict='REFUSE', reason=str(exc), external_execution=False)
    return dict(observed_verdict='ACCEPT', reason='Exact requested identity/pattern verified; model and interpretation obligations remain open.', receipt=report, external_execution=False)
