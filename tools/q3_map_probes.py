"""Q3 exact reference probes for formal map/localization boundaries.

These compute concrete arithmetic/predicate countermodels. They do not run Lean
or assert a native GP v0.37 verifier verdict.
"""


def _gaussian_mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _operation(d):
    control = d.get('control')
    if d.get('map') != 'Z_to_Zi_inclusion':
        raise ValueError('Unknown operation map')
    if control == 'root_forward':
        if d != {'control': control, 'map': 'Z_to_Zi_inclusion',
                 'polynomial': 'x-1', 'source_point': 1}:
            raise ValueError('Changed root-forward fixture')
        source_value = d['source_point'] - 1
        target_point = (d['source_point'], 0)
        target_value = (target_point[0] - 1, target_point[1])
        if source_value != 0 or target_value != (0, 0):
            raise ValueError('Forward root arithmetic failed')
        return _result('ACCEPT', 'Integer root 1 maps to Gaussian root (1,0).',
                       source_value=source_value, target_value=target_value)
    if control == 'empty_pullback':
        if d != {'control': control, 'map': 'Z_to_Zi_inclusion',
                 'polynomial': '1', 'target_empty_proved': True}:
            raise ValueError('Changed EMPTY-pullback fixture')
        # The constant one is (1,0) in Zi and 1 in Z, so neither is zero.
        if (1, 0) == (0, 0) or 1 == 0:
            raise ValueError('Nontriviality control failed')
        return _result('ACCEPT', 'Target EMPTY for constant 1 pulls back to source EMPTY.',
                       target_constant=(1, 0), source_constant=1)
    if control == 'empty_forward':
        if d != {'control': control, 'map': 'Z_to_Zi_inclusion',
                 'polynomial': 'x^2+1', 'gaussian_point': [0, 1]}:
            raise ValueError('Changed forward-EMPTY fixture')
        point = tuple(d['gaussian_point'])
        square = _gaussian_mul(point, point)
        value = (square[0] + 1, square[1])
        # For every integer n, n*n >= 0, hence n*n+1 > 0.
        source_empty_argument = 'n*n+1 >= 1 for every integer n'
        if value != (0, 0):
            raise ValueError('Gaussian witness is not a root')
        return _result('REFUSE', 'Source EMPTY does not travel forward: i*i+1=0 in Zi.',
                       source_empty_argument=source_empty_argument,
                       gaussian_square=square, target_value=value,
                       map_surjective=False)
    raise ValueError('Unknown operation-map control')


def _localization(d):
    control = d.get('control')
    if d.get('ambient') != 'Z' or d.get('ideal_generator') != 6 or d.get('guard') != 2:
        raise ValueError('Unknown localization context')
    if control == 'local_membership':
        if d != {'control': control, 'ambient': 'Z', 'ideal_generator': 6,
                 'guard': 2, 'element': 3, 'multiplier': 2}:
            raise ValueError('Changed local-membership fixture')
        multiple = d['multiplier'] * d['element']
        if multiple % 6 != 0 or d['multiplier'] != d['guard']:
            raise ValueError('Localization witness failed')
        return _result('ACCEPT', 'Multiplier 2 sends 3 to 6 in the source ideal.',
                       multiplier_product=multiple, localized_member=True,
                       ambient_member=d['element'] % 6 == 0)
    if control == 'ambient_return':
        if d != {'control': control, 'ambient': 'Z', 'ideal_generator': 6,
                 'guard': 2, 'element': 3, 'multiplier': 2}:
            raise ValueError('Changed ambient-return fixture')
        local = (d['multiplier'] * d['element']) % 6 == 0
        ambient = d['element'] % 6 == 0
        if not local or ambient:
            raise ValueError('Ambient-return countermodel failed')
        return _result('REFUSE', '3 is locally zero at 2 but 3 is not in ambient (6).',
                       localized_member=local, ambient_member=ambient)
    if control == 'ambient_direct':
        if d != {'control': control, 'ambient': 'Z', 'ideal_generator': 6,
                 'guard': 2, 'element': 6, 'source_ideal_cofactor': 1}:
            raise ValueError('Changed direct-membership fixture')
        ambient = d['element'] == 6 * d['source_ideal_cofactor']
        if not ambient:
            raise ValueError('Direct ideal witness failed')
        return _result('ACCEPT', 'Separate source-ideal witness 6=6*1 proves ambient membership.',
                       ambient_member=ambient, source_ideal_cofactor=1)
    raise ValueError('Unknown localization control')


def _orientation(d):
    control = d.get('control')
    if d != {'control': control, 'source_point': 0, 'target_point': 1,
             'forward': 'x+1', 'backward': 'y-1', 'source_predicate': 'x=0'}:
        raise ValueError('Changed translation fixture')
    x, y = d['source_point'], d['target_point']
    if y != x + 1 or x != y - 1:
        raise ValueError('Map inverse fixture failed')
    source_true = x == 0
    backward_rewrite = (y - 1) == 0
    forward_oriented_rewrite = (y + 1) == 0
    if not source_true or not backward_rewrite or forward_oriented_rewrite:
        raise ValueError('Orientation arithmetic failed')
    if control == 'backward_rewrite':
        return _result('ACCEPT', 'P(backward(1)) is P(0), matching the source predicate.',
                       source_predicate=source_true, rewritten_predicate=backward_rewrite)
    if control == 'wrong_forward_rewrite':
        return _result('REFUSE', 'P(forward(1)) is P(2), so forward-oriented substitution loses P(0).',
                       source_predicate=source_true,
                       wrong_rewritten_predicate=forward_oriented_rewrite)
    raise ValueError('Unknown orientation control')


def _equivalence(d):
    control = d.get('control')
    if control == 'identity_inclusion':
        if d != {'control': control, 'carrier': ['a', 'b'],
                 'source_points': ['a'], 'target_points': ['a'],
                 'forward': {'a': 'a', 'b': 'b'},
                 'backward': {'a': 'a', 'b': 'b'}}:
            raise ValueError('Changed identity fixture')
    elif control == 'swap_not_containment':
        if d != {'control': control, 'carrier': ['a', 'b'],
                 'source_points': ['a'], 'target_points': ['b'],
                 'forward': {'a': 'b', 'b': 'a'},
                 'backward': {'a': 'b', 'b': 'a'}}:
            raise ValueError('Changed swap fixture')
    else:
        raise ValueError('Unknown equivalence control')
    carrier = d['carrier']; src = set(d['source_points']); dst = set(d['target_points'])
    f = d['forward']; b = d['backward']
    inverses = all(b[f[x]] == x and f[b[x]] == x for x in carrier)
    maps = all(f[x] in dst for x in src) and all(b[x] in src for x in dst)
    literal_containment = src <= dst
    reverse_containment = dst <= src
    if not inverses or not maps:
        raise ValueError('Mapped equivalence premises failed')
    if control == 'identity_inclusion':
        if not literal_containment or not reverse_containment:
            raise ValueError('Identity inclusion failed')
        return _result('ACCEPT', 'Identity mapped equivalence also has literal inclusion.',
                       mapped_equivalence=True, literal_containment=True)
    if literal_containment or reverse_containment:
        raise ValueError('Swap containment countermodel failed')
    return _result('REFUSE', 'Swap gives mapped equivalence but neither literal containment.',
                   mapped_equivalence=True, literal_containment=False,
                   reverse_literal_containment=False)


def _result(verdict, reason, **evidence):
    return {'observed_verdict': verdict, 'reason': reason,
            'reference_evidence': evidence, 'native_lean_verdict': None,
            'external_execution': False}


def probe(case, route):
    d = case['inputs']
    layer = route['layer']
    if layer == 'reference_operation_map':
        return _operation(d)
    if layer == 'reference_localization_ambient':
        return _localization(d)
    if layer == 'reference_map_orientation':
        return _orientation(d)
    if layer == 'reference_equivalence_containment':
        return _equivalence(d)
    raise ValueError('Unknown Q3 reference layer')
