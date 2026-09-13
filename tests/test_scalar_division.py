"""Cloquet: polynomial quotient must never stand in for rational division."""
import pytest

from grandportage import cas, kernel as K, provenance as P
from grandportage import store as S, verify as V
from test_verdict_provenance import _execution, _identity_graph, _verdict


CASES = [
    ("1/T", "0"),
    ("(T^2+2)/(2*T)", "T/2"),
    # True modulo T^4-16*T^2+4, including the selected positive root.
    # The raw rational expression is still outside this CAS input language.
    ("(T^2+2)/(2*T)", "(18*T-T^3)/4"),
]


def never_run(*args, **kwargs):
    pytest.fail("unsupported division reached the execution boundary")


@pytest.mark.parametrize("lhs,rhs", CASES)
@pytest.mark.parametrize("generators", [[], ["T^4-16*T^2+4"]])
def test_rational_claims_refuse_before_execution(lhs, rhs, generators):
    with pytest.raises(cas.CASError, match="nonzero scalar coefficients"):
        cas.classify_identity(["T"], lhs, rhs, generators, _runner=never_run)


@pytest.mark.parametrize("expr", [
    "1/(T+1)", "T/T", "0/T", "1/(T-T+2)", "1/(1/T)",
    "1/(2-2)", "1/(T^0)", "1/leadcoef(T)",
])
def test_division_is_not_licensed_by_cancellation_or_backend_functions(expr):
    with pytest.raises(cas.CASError, match="unsupported division"):
        cas.classify_identity(["T"], expr, "0", _runner=never_run)


@pytest.mark.parametrize("operation", ["generator", "map", "body", "saturation"])
def test_shared_boundary_covers_more_than_claim_sides(operation):
    with pytest.raises(cas.CASError, match="unsupported division"):
        if operation == "generator":
            cas.classify_identity(["T"], "T", "0", ["1/T"], _runner=never_run)
        elif operation == "map":
            cas.substitute_and_reduce(["T"], "T", {"T": "1/T"}, _runner=never_run)
        elif operation == "body":
            cas.CASProgram(cas.SINGULAR, "GP_R", ["T"],
                           [("GP_P", "poly", "T")], ["GP_P=1/T"], ["GP_P"])
        else:
            cas.SingularBackend(runner=never_run).compile_saturation(["T"], ["T"], "1/T")


def test_constant_denominator_zero_in_characteristic_refuses():
    with pytest.raises(cas.CASError, match="zero divisor"):
        cas.classify_identity(["T"], "T/2", "0", characteristic=2, _runner=never_run)


def test_batch_keeps_unsupported_guarded_claim_unverified(tmp_path):
    S.append([
        {"ev": "model", "id": "M", "ring_vars": ["T"], "characteristic": 0,
         "generators": ["T^4-16*T^2+4"], "open_conditions": ["T"]},
        {"ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
         "lhs": "1/T", "rhs": "0", "ring_vars": ["T"],
         "statement": "hostile scalar quotient", "identity_origin": K.AMBIENT},
    ], str(tmp_path))
    result = V.verify_all(str(tmp_path), _runner=never_run, record=True)
    graph = S.load(S.graph_path(str(tmp_path)))
    assert all(not v["verdict"].startswith("VERIFIED") for v in graph.verdicts.values())
    assert all(r.evidence.verdict == V.UNVERIFIED
               for r in graph.authority_receipts.values())
    assert "unsupported division" in str(result)


def test_pre_fix_receipt_remains_history_without_authority():
    graph = _identity_graph()
    event = _verdict(graph)
    manifest = _execution()
    manifest["implementation_version"] = 4
    event["backend"] = P.encode_backend_provenance(manifest)
    graph.apply(event)
    assert graph.verdicts[event["id"]]["current"] is False
    assert "identity_verdict" not in graph.claims["C"]
    assert graph.authority_receipts == {}
    assert P.backend_provenance(event["backend"], current_only=False) is not None


@pytest.mark.live
def test_native_constant_denominator_control_and_true_polynomial_restatement():
    backend = cas.SingularBackend()
    origin, _ = backend.classify_identity(["T"], "(T^2+2)/2", "(T^2)/2+1", timeout=20)
    assert origin == K.AMBIENT
    # Exact constant-denominator flattening of sqrt(5) in Q[T]/(T^4-16T^2+4).
    origin, _ = backend.classify_identity(
        ["T"], "((18*T-T^3)/4)^2", "5", ["T^4-16*T^2+4"], timeout=20)
    assert origin == K.DERIVED
    count = backend.execution_count
    for lhs, rhs in CASES:
        with pytest.raises(cas.CASError, match="unsupported division"):
            backend.classify_identity(["T"], lhs, rhs, ["T^4-16*T^2+4"], timeout=20)
    assert backend.execution_count == count
