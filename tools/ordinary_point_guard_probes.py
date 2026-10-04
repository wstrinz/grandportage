"""Bound literal-value diagnostic of the pinned ordinary point guard branch.

Uses the predecessor test seam; never reports a production backend verdict.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def probe(case, route):
    path = ROOT / 'corpus/must' / (case['id'] + '.json')
    if sha(path) != route['case_sha256'] or json.loads(path.read_text(encoding='utf-8')) != case:
        raise ValueError('Bound ordinary point case changed')
    for source, expected in route['source_sha256'].items():
        if sha(ROOT / 'oracle/checkout' / source) != expected:
            raise ValueError('Pinned ordinary point diagnostic source changed: ' + source)
    data = case['inputs']
    if data['coefficient_domain'] != 'Q' or data['point_universe'] != 'rational points' or data['nonzero_guards'] != ['x']:
        raise ValueError('Unsupported diagnostic model')
    equations = data['equations']
    variables = ['x', 'y'] if equations == ['y'] else ['x']
    if equations not in ([], ['y']) or data['variables'] != variables or set(data['point']) != set(variables):
        raise ValueError('Unsupported diagnostic expressions/coordinates')
    if any(value not in ('0', '1') for value in data['point'].values()):
        raise ValueError('Only literal zero/one coordinates are supported')
    from test_adversarial import _ExactPointBackend, _open_witness_graph
    from grandportage import verify as V

    class RecordedBackend(_ExactPointBackend):
        def __init__(self):
            self.calls = []
        def evaluate_point(self, ring, expressions, point, **kwargs):
            aggregate, details = super().evaluate_point(ring, expressions, point, **kwargs)
            self.calls.append({'ring': list(ring), 'expressions': list(expressions),
                               'aggregate_all_zero': aggregate, 'details': details})
            return aggregate, details

    graph = _open_witness_graph(equations, data['point'], 'W')
    backend = RecordedBackend()
    native, reason = V.point_witness(graph, 'W', _backend=backend)
    if len(backend.calls) != 1:
        raise ValueError('Expected one literal backend evaluation')
    call = backend.calls[0]
    if call['ring'] != variables or call['expressions'] != equations + ['x'] or call['details']['point'] != data['point']:
        raise ValueError('Diagnostic projection changed the neutral expressions/point')
    verdicts = {V.WITNESS_VERIFIED: 'ACCEPT', V.WITNESS_REFUTED: 'REFUSE'}
    if native not in verdicts or verdicts[native] != case['expected']['verdict']:
        raise ValueError('Diagnostic decision does not match the reviewed contract: ' + str(native))
    return {'observed_verdict': None, 'status': 'DIAGNOSTIC_OBSERVED',
            'diagnostic_verdict': verdicts[native], 'diagnostic_native_spelling': native,
            'diagnostic_matches_expected': True, 'evaluation': call,
            'reason': reason, 'production_function_called': 'grandportage.verify.point_witness',
            'test_helper': 'tests/test_adversarial.py::_ExactPointBackend/_open_witness_graph',
            'singular_executed': False, 'native_receipt_produced': False,
            'held_authority_established': False,
            'projection_limit': 'Test graph omits explicit coefficient_domain/point_universe; literal rational coordinates only. Bypasses production CAS coordinate validation, execution binding and parsing.'}
