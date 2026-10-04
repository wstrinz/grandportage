"""Bind two exact passes under an explicit canonical-export contract."""
from grandportage import laurent_lowering as L, coefficient_expansion as C, laurent_coefficient_pipeline as P

def probe(case, route):
    d = case['inputs']
    if d['binding_contract'] != 'same_canonical_export':
        raise ValueError('Unsupported binding contract')
    image = d['downstream_image']
    if isinstance(image, dict):
        if set(image) != {'terms'}: raise ValueError('Unknown sparse representation')
        image = dict(schema='sparse_polynomial_v1', terms=image['terms'])
    laurent = dict(schema=L.SCHEMA, characteristic=d['characteristic'], series_variable=d['parameter'], coefficient_variables=d['coefficient_variables'], inputs={'F':d['laurent_terms']}, program=[], equalities=[dict(id='self',left='F',right='F')], exports=[dict(id=e['name'],node='F',shift=e['shift']) for e in d['exports']])
    coefficient = dict(schema=C.SCHEMA, characteristic=d['characteristic'], parameter=d['parameter'], coefficient_variables=d['coefficient_variables'], source_variables=['s'],images={'s':image},bounded_variables={},equations=[dict(id='eq',expression='s',degree=d['degree'],coverage=C.COMPLETE,coefficients=d['coefficient_rows'])])
    # Verify both passes independently before measuring composition.
    L.verify(laurent)
    C.verify(coefficient)
    try:
        report = P.verify(dict(schema=P.SCHEMA,laurent=laurent,coefficient_expansion=coefficient,bindings=[dict(export=name,image='s') for name in d['image_bindings']]))
    except P.LaurentCoefficientPipelineError as exc:
        return dict(observed_verdict='REFUSE',reason=str(exc),individual_passes_verified=True,external_execution=False)
    return dict(observed_verdict='ACCEPT',reason='Both passes and exact canonical binding verify; no graph or chart authority.',individual_passes_verified=True,licenses=report['licenses'],authority_boundary=report['authority_boundary'],external_execution=False)
