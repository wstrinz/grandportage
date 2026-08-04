"""Principal-open localization certificates and adversarial controls."""

import copy
import json

import pytest

from grandportage import backend as B
from grandportage import check as C
from grandportage import cli
from grandportage import groebner as G
from grandportage import format as F
from grandportage import kernel as K
from grandportage import localization as L
from grandportage import store as S
from grandportage import verify as V


def _spec():
    return {
        "schema": L.SCHEMA,
        "characteristic": 0,
        "ring_vars": ["q", "t", "y"],
        "generators": ["q*t*y"],
        "guards": ["q", "t"],
        "expression": {
            "numerator": "y",
            "denominator_powers": [2, 1],
        },
        "certificate": {
            "localization_powers": [1, 1],
            "membership_target": "q*t*y",
            "cofactors": ["1"],
        },
    }


def test_exact_guard_monomial_certifies_localized_membership_only():
    report = L.verify(_spec())

    assert report["verdict"] == L.VERIFIED
    assert report["licenses"] == [
        "identity_in_declared_localization_only"
    ]
    assert report["normalized"]["expression"] == {
        "numerator": "y",
        "denominator_powers": [2, 1],
    }
    assert report["normalized"]["certificate"]["membership_target"] == (
        "q*t*y"
    )
    assert report["checked"]["generator_count"] == 1


def test_same_identity_without_the_needed_guard_power_is_rejected():
    spec = _spec()
    spec["certificate"]["localization_powers"] = [0, 1]

    with pytest.raises(L.LocalizationError, match="expected t\\*y"):
        L.verify(spec)


def test_wrong_cofactor_is_rejected_by_exact_expansion():
    spec = _spec()
    spec["certificate"]["cofactors"] = ["2"]

    with pytest.raises(L.LocalizationError, match="wrong polynomial"):
        L.verify(spec)


@pytest.mark.parametrize("mutate, message", [
    (lambda spec: spec.update({"guards": ["q", "q+0"]}),
     "remain distinct"),
    (lambda spec: spec.update({"guards": ["0"]}),
     "zero polynomial cannot be inverted"),
    (lambda spec: spec["expression"].update({"denominator_powers": [1]}),
     "one power per guard"),
    (lambda spec: spec["certificate"].update({
        "localization_powers": [65, 0]}),
     "0 through 64"),
    (lambda spec: spec.update({"surprise": True}),
     "unknown field"),
])
def test_certificate_surface_is_closed_and_bounded(mutate, message):
    spec = _spec()
    mutate(spec)
    with pytest.raises(L.LocalizationError, match=message):
        L.verify(spec)


def test_denominator_scope_is_bound_into_the_report_fingerprint():
    first = L.verify(_spec())
    changed = _spec()
    changed["expression"]["denominator_powers"] = [3, 1]
    second = L.verify(changed)

    assert first["spec_fingerprint"] != second["spec_fingerprint"]


def test_cli_prints_narrow_authority_and_can_emit_json(tmp_path, capsys):
    path = tmp_path / "localization.json"
    path.write_text(json.dumps(_spec()), encoding="utf-8")

    assert cli.main([
        "verify-localization-membership", "--spec", str(path),
    ]) == 0
    text = capsys.readouterr().out
    assert L.VERIFIED in text
    assert "no ambient identity or point transport" in text

    assert cli.main([
        "verify-localization-membership", "--spec", str(path), "--json",
    ]) == 0
    report = json.loads(capsys.readouterr().out)
    assert report["licenses"] == [
        "identity_in_declared_localization_only"
    ]


def test_mutating_the_recorded_target_does_not_survive():
    spec = copy.deepcopy(_spec())
    spec["certificate"]["membership_target"] = "q*y"

    with pytest.raises(L.LocalizationError, match="expected q\\*t\\*y"):
        L.verify(spec)


def test_sparse_generator_and_target_verify_without_infix_reparsing():
    spec = _spec()
    sparse = G.encode_sparse_polynomial(G.parse_polynomial(
        "q*t*y", spec["ring_vars"]
    ))
    spec["generators"] = [sparse]
    spec["certificate"]["membership_target"] = sparse

    report = L.verify(spec)

    assert report["verdict"] == L.VERIFIED
    assert report["normalized"]["generators"] == [sparse]


def test_sparse_zero_guard_is_still_refused():
    spec = _spec()
    spec["guards"] = [{
        "schema": G.SPARSE_POLYNOMIAL_SCHEMA, "terms": [],
    }]
    with pytest.raises(L.LocalizationError, match="zero polynomial"):
        L.verify(spec)


class _LocalizedMembershipBackend:
    def __init__(self):
        self.targets = []

    def membership(self, ring_vars, target, generators, characteristic=0,
                   timeout=300):
        self.targets.append(target)
        if G.parse_polynomial(target, ring_vars, characteristic) == \
                G.parse_polynomial("q*t", ring_vars, characteristic):
            return {"is_member": True, "cofactors": ["1"]}
        return {"is_member": False, "cofactors": []}


def _localized_empty_graph(model_overrides=None):
    graph = S.Graph()
    graph.apply(F.meta_event())
    model = {
        "ev": "model", "id": "OPEN", "what": "q and t nonzero",
        "characteristic": 0, "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": ["q", "t"], "generators": ["q*t"],
        "open_conditions": ["q", "t"],
    }
    model.update(model_overrides or {})
    graph.apply(model)
    graph.apply({
        "ev": "claim", "id": "OPEN-EMPTY", "model": "OPEN",
        "kind": K.EMPTY, "statement": "the open chart has no points",
        "certificate": "LOCALIZED_UNIT_IDEAL_CERT",
        "established_by": "RAN", "ladder": "exact-checked",
    })
    return graph


def test_localized_unit_certificate_promotes_only_the_exact_open_model():
    graph = _localized_empty_graph()
    backend = _LocalizedMembershipBackend()
    verdict, why, representation = V.localized_unit_ideal(
        graph, "OPEN-EMPTY", _backend=backend)

    assert verdict == V.CERT_VERIFIED
    assert backend.targets == ["q*t"]
    assert representation["method"] == "localized_unit_ideal_v1"
    assert representation["proof"]["certificate"][
        "localization_powers"] == [1, 1]
    assert "No parent emptiness is implied" in why
    assert K.derive_scope(
        K.EMPTY, "LOCALIZED_UNIT_IDEAL_CERT", None) == K.SCHEME
    assert not K.transport(
        K.RESTRICTION, K.ALONG, K.EMPTY, scope=K.SCHEME,
        certificate="LOCALIZED_UNIT_IDEAL_CERT").licensed


def test_localized_unit_bounded_miss_is_typed_ignorance_not_refutation():
    class Miss(_LocalizedMembershipBackend):
        def membership(self, *args, **kwargs):
            return {"is_member": False, "cofactors": []}

    verdict, why, representation = V.localized_unit_ideal(
        _localized_empty_graph(), "OPEN-EMPTY", _backend=Miss())

    assert verdict == V.UNVERIFIED
    assert representation is None
    assert "search exhaustion" in why
    assert "not evidence" in why

def _execution_manifest():
    trace = [{
        "semantic_input_fingerprint": B.semantic_fingerprint("test", []),
        "program_fingerprint": B.text_fingerprint("test program"),
        "stdout_fingerprint": B.text_fingerprint("test output"),
        "stderr_fingerprint": B.text_fingerprint(""),
        "artifact_fingerprint": B.semantic_fingerprint("artifact", []),
        "returncode": 0,
        "aborted": False,
    }]
    return {
        "schema": 2,
        "contract": B.SINGULAR_CONTRACT,
        "implementation": B.SINGULAR_IMPLEMENTATION,
        "implementation_version": B.SINGULAR_IMPLEMENTATION_VERSION,
        "protocol_version": B.BACKEND_PROTOCOL_VERSION,
        "binary_version": "Singular test",
        "executions": trace,
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", trace),
    }


def test_localized_unit_verdict_replays_and_projects_current_authority():
    graph = _localized_empty_graph()
    verdict, why, representation = V.localized_unit_ideal(
        graph, "OPEN-EMPTY", _backend=_LocalizedMembershipBackend())
    event = V._verdict_event(
        graph, "certificate", "OPEN-EMPTY", verdict, why, representation,
        execution=_execution_manifest())

    graph.apply(event)

    claim = graph.claims["OPEN-EMPTY"]
    assert event["verifier"] == "verify.localized_unit_ideal"
    assert claim["certificate_verdict"] == V.CERT_VERIFIED
    assert claim["representation"] == representation
    assert graph.verdicts[event["id"]]["current"] is True

    mutated = json.loads(json.dumps(event))
    mutated["id"] = "mutated-local-proof"
    mutated["representation"]["proof"]["guards"] = ["q"]
    mutated["input_fingerprint"] = V.P.input_fingerprint(
        graph, "certificate", "OPEN-EMPTY",
        representation=mutated["representation"])
    with pytest.raises(S.GraphError, match="exact replay|does not match"):
        graph.apply(mutated)

@pytest.mark.parametrize("model_updates", [
    {"generators": ["q*t^2"]},
    {"open_conditions": ["q"]},
    {"open_conditions": ["q^2", "t"]},
    {"characteristic": 5, "coefficient_domain": "F_5"},
    {"point_universe": S.BASE_POINT_UNIVERSE},
    {"ring_vars": ["p", "t"], "generators": ["p*t"],
     "open_conditions": ["p", "t"]},
])
def test_localized_unit_verdict_refuses_or_stales_on_exact_model_change(
        model_updates):
    original = _localized_empty_graph()
    verdict, why, representation = V.localized_unit_ideal(
        original, "OPEN-EMPTY", _backend=_LocalizedMembershipBackend())
    event = V._verdict_event(
        original, "certificate", "OPEN-EMPTY", verdict, why, representation,
        execution=_execution_manifest())
    changed = _localized_empty_graph(model_updates)

    try:
        changed.apply(event)
    except S.GraphError as exc:
        assert "replay" in str(exc) or "does not match" in str(exc)
    else:
        stored = changed.verdicts[event["id"]]
        assert stored["current"] is False
        assert "fingerprint" in stored["stale_reason"]
        assert changed.claims["OPEN-EMPTY"].get(
            "certificate_verdict") is None


def test_local_empty_does_not_transport_to_its_parent_without_coverage():
    graph = _localized_empty_graph()
    claim = graph.claims["OPEN-EMPTY"]
    graph.claims["OPEN-EMPTY"] = dict(
        claim, certificate_verdict=V.CERT_VERIFIED)
    graph.apply({
        "ev": "model", "id": "PARENT", "what": "the ambient q,t model",
        "characteristic": 0, "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": ["q", "t"], "generators": ["q*t"],
    })
    graph.apply({
        "ev": "edge", "id": "OPEN-IN-PARENT", "src": "OPEN",
        "dst": "PARENT", "type": K.RESTRICTION,
        "map_kind": K.IDENTITY_MAP,
        "why": "the principal-open chart is only part of its parent",
    })
    graph.apply({
        "ev": "inference", "id": "ILLICIT-PARENT-EMPTY",
        "claim": "OPEN-EMPTY", "path": [["OPEN-IN-PARENT", K.ALONG]],
        "concludes_kind": K.EMPTY,
        "asserted": "the parent is empty because one open chart is empty",
    })

    licensed, trace = C.audit_inference(graph, "ILLICIT-PARENT-EMPTY")
    assert not licensed
    assert "does NOT license EMPTY" in trace[0][3]


def test_localized_unit_name_alone_grants_no_effective_authority():
    graph = _localized_empty_graph()
    claim = graph.claims["OPEN-EMPTY"]

    assert C.effective_certificate(claim) is None
    findings = [
        finding for finding in C.run(graph)
        if finding.fid == "EVIDENCE-GRADE:localized-unit:OPEN-EMPTY"
    ]
    assert len(findings) == 1
    assert "name alone grants no effective certificate" in findings[0].detail
    graph.apply({
        "ev": "model", "id": "COPY", "what": "equivalent copy",
        "characteristic": 0, "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": ["q", "t"], "generators": ["q*t"],
        "open_conditions": ["q", "t"],
    })
    graph.apply({
        "ev": "edge", "id": "ISO", "src": "OPEN", "dst": "COPY",
        "type": K.EQUIVALENCE, "map_kind": K.RATIONAL,
        "why": "positive control: an equivalence would normally carry EMPTY",
    })
    graph.apply({
        "ev": "inference", "id": "CARRY", "claim": "OPEN-EMPTY",
        "path": [["ISO", K.ALONG]], "concludes_kind": K.EMPTY,
        "asserted": "the equivalent copy is empty",
    })
    graph.validate()
    licensed, trace = C.audit_inference(graph, "CARRY")
    assert not licensed
    assert "no current VERIFIED verdict" in trace[0][3]


    checked = dict(claim, certificate_verdict="VERIFIED")
    assert C.effective_certificate(checked) == "LOCALIZED_UNIT_IDEAL_CERT"
    graph.claims["OPEN-EMPTY"] = checked
    assert C.audit_inference(graph, "CARRY")[0]
