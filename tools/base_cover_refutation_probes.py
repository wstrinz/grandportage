"""Bounded 84.8 cover-refutation contrast; native classifier, injected ideal result.

The backend answers are explicit assumptions. Elementary exact reference arithmetic
shows the proposed BASE conclusion is false for this concrete parent.
"""
from grandportage import format as F, store as S, verify as V


class _InjectedGeometricHole:
    def __init__(self):
        self.calls = []

    def membership(self, ring, target, generators, **kwargs):
        if (ring != ['x'] or target != '1' or generators != ['x^2+1']
                or kwargs.get('characteristic') != 0):
            raise ValueError('Unexpected unit-ideal query')
        self.calls.append({'operation': 'membership', 'ring': ring,
                           'target': target, 'generators': generators})
        return {'is_member': False, 'reduced': '1'}

    def partition_cover(self, ring, parent, branches, **kwargs):
        if (ring != ['x'] or parent != ['x^2+1']
                or branches != [['1'], ['1']]
                or kwargs.get('characteristic') != 0):
            raise ValueError('Unexpected geometric cover query')
        self.calls.append({'operation': 'partition_cover', 'ring': ring,
                           'parent': parent, 'branches': branches})
        return False, {'why': 'two unit-ideal branches have empty loci',
                       'uncovered': ['1']}


def _graph(point_universe):
    g = S.Graph()
    g.apply(F.meta_event())
    for mid, generators in [('M', ['x^2+1']), ('B0', ['1']), ('B1', ['1'])]:
        g.apply({'ev': 'model', 'id': mid, 'what': mid,
                 'coefficient_domain': 'Q', 'characteristic': 0,
                 'point_universe': point_universe, 'ring_vars': ['x'],
                 'generators': generators})
    g.apply({'ev': 'claim', 'id': 'C', 'model': 'M', 'kind': 'PREDICATE',
             'statement': 'empty-locus branches cover parent',
             'established_by': 'READ', 'ladder': 'claimed'})
    g.apply({'ev': 'partition', 'id': 'P', 'parent': 'M',
             'branches': ['B0', 'B1'], 'exhaustive': 'C',
             'why': 'empty-union cover contrast'})
    g.validate()
    return g


def probe(case, route):
    d = case['inputs']
    control = d.get('control')
    expected_universe = {'base_refutation': S.BASE_POINT_UNIVERSE,
                         'geometric_refutation': S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE}
    if control not in expected_universe:
        raise ValueError('Unknown cover-refutation control')
    if d != {'control': control, 'coefficient_domain': 'Q',
             'variables': ['x'], 'parent_equations': ['x^2+1'],
             'semantic_branches': [],
             'native_empty_union_encoding': [['1'], ['1']],
             'point_universe': expected_universe[control],
             'geometric_test': 'explicitly_assumed_injected'}:
        raise ValueError('Changed 84.8 countermodel fixture')
    # A literal zero-branch partition is not representable in the frozen graph.
    # Two branches with equation 1=0 have the same empty union of point loci.
    g = _graph(d['point_universe'])
    backend = _InjectedGeometricHole()
    raw, reason = V.partition_exhaustiveness(g, 'P', _backend=backend)
    if [x['operation'] for x in backend.calls] != ['membership', 'partition_cover']:
        raise ValueError('Partition classifier did not inspect both premises')
    expected_raw = (V.NOT_GEOMETRICALLY_EXHAUSTIVE if control == 'base_refutation'
                    else V.NOT_EXHAUSTIVE)
    if raw != expected_raw:
        raise ValueError('Partition classifier changed: ' + raw)
    # Exact semantic countermodel: q^2+1>0 for every q in Q, while i^2+1=0.
    # A branch with generator 1 has no point in either field.
    i = (0, 1)
    i_squared = (i[0]*i[0]-i[1]*i[1], 2*i[0]*i[1])
    if i_squared != (-1, 0) or (i_squared[0]+1, i_squared[1]) != (0, 0):
        raise ValueError('Geometric root arithmetic changed')
    return {
        'observed_verdict': ('REFUSE' if control == 'base_refutation' else 'ACCEPT'),
        'reason': reason,
        'native_classifier_verdict': raw,
        'native_classifier_called': True,
        'backend_calls': backend.calls,
        'geometric_test_injected': True,
        'literal_empty_branch_family': d['semantic_branches'],
        'native_empty_union_encoding': d['native_empty_union_encoding'],
        'exact_reference': {'rational_no_root_argument':
            'For every rational q, q^2 is nonnegative, so q^2+1>0.',
            'algebraic_closure_root': 'i, with i^2=-1',
            'i_squared_pair': list(i_squared),
            'both_branch_loci_empty': True,
            'base_cover_truth': True,
            'geometric_cover_truth': False},
        'lean_recompiled': False,
        'external_execution': False,
        'persisted_verdict': False,
    }
