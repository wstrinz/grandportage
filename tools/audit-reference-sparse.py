"""Compare sparse-input validation at the reference and production boundaries."""
from pathlib import Path
import hashlib, importlib.util, json
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('replay', ROOT / 'tools/check-corpus.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
r.validate()
from grandportage import reference_oracle as R, groebner as G

def sparse(coefficient, powers):
    return {'schema': 'sparse_polynomial_v1', 'terms': [{'coefficient': coefficient, 'powers': powers}]}

controls = [
    ('canonical', sparse('1', [['x', 2]]), 'x^2', True, True),
    ('duplicate_power', sparse('1', [['x', 1], ['x', 2]]), 'x^2', True, False),
    ('noncanonical_coefficient', sparse('2/2', [['x', 2]]), 'x^2', True, False),
    ('numeric_coefficient', sparse(1, [['x', 2]]), 'x^2', True, False),
    ('zero_term', sparse('0', [['x', 2]]), '0', True, False),
    ('wrong_identity', sparse('1', [['x', 2]]), 'x', False, False),
]
rows = []
for name, value, target, reference_accepts, production_accepts in controls:
    row = {'id': name, 'generator': value, 'target': target}
    for label, checker, expected in [('reference', R.reduce_by_explicit_cofactors, reference_accepts), ('production', G.check_membership_identity, production_accepts)]:
        try:
            result = checker(target, [value], ['1'], ['x'], 0)
            observed = {'accepted': True, 'result': result}
        except (R.ReferenceError, G.CertificateError) as exc:
            observed = {'accepted': False, 'exception': type(exc).__name__, 'message': str(exc)}
        assert observed['accepted'] is expected, (name, label, observed)
        row[label] = observed
    rows.append(row)
report = {
    'controls': rows,
    'source_hashes': {p: r.sha(ROOT / p) for p in ['oracle/checkout/grandportage/reference_oracle.py', 'oracle/checkout/grandportage/groebner.py']},
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'finding': 'Reference accepts four malformed/noncanonical sparse representations that production refuses first. Duplicate x powers overwrite rather than accumulate. This is a standalone reference-validation gap, not a production false licence.',
    'proposed_fix': 'Give every checker an explicit input language and validate duplicate factors, canonical coefficients and zero terms independently before arithmetic; retain a valid control and false-identity refusal.',
    'scope': 'Pinned direct functions, exact Q arithmetic, no graph events, CAS, historical execution or campaign access.'
}
(ROOT / 'reports/REFERENCE-SPARSE-BOUNDARY.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print('Six reference/production controls verified; four reference-only validation gaps, no production acceptance.')
