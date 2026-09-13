"""Bounded algebraic-extension-valued point witness contract."""

from copy import deepcopy

import pytest

from grandportage import backend as B
from grandportage import cas
from grandportage import format as F
from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def _field(polynomial="a^2+1"):
    return {
        "kind": "simple_number_field_v1",
        "base": "Q",
        "symbol": "a",
        "minimal_polynomial": polynomial,
    }


def _model(universe="ALGEBRAIC_CLOSURE", generator="x^2+1"):
    return {
        "ev": "model", "id": "M", "what": "a Q-scheme",
        "coefficient_domain": "Q", "characteristic": 0,
        "point_universe": universe, "ring_vars": ["x"],
        "generators": [generator], "open_conditions": ["x"],
    }


def _claim(coordinate="a", field=None):
    return {
        "ev": "claim", "id": "C", "model": "M", "kind": K.NONEMPTY,
        "statement": "the displayed extension-valued point exists",
        "witness_kind": K.EXHIBITED,
        "witness_field": field or _field(),
        "witness_point": {"x": coordinate},
    }


def _graph(events):
    graph = S.Graph()
    graph.apply_all([(event, "number-field-v1", index)
                     for index, event in enumerate(
                         [F.meta_event()] + list(events), 1)])
    return graph.validate()


@pytest.mark.parametrize("coordinate", ["a", "-a"])
def test_q_i_point_and_its_conjugate_verify_exactly(coordinate):
    graph = _graph([_model(), _claim(coordinate)])

    verdict, why, receipt = V.point_witness(graph, "C")

    assert verdict == V.WITNESS_VERIFIED, why
    assert receipt["method"] == "simple_number_field_v1"
    assert receipt["field"]["degree"] == 2
    assert receipt["coordinates"]["x"] in (["0", "1"], ["0", "-1"])
    assert receipt["equations"][0]["value"] == []
    assert receipt["guards"][0]["value"] != []


def test_wrong_quotient_coordinate_is_a_mathematical_refutation():
    graph = _graph([_model(), _claim("1")])
    verdict, why, receipt = V.point_witness(graph, "C")
    assert verdict == V.WITNESS_REFUTED
    assert "does not vanish" in why
    assert receipt["equations"][0]["value"] == ["2"]


@pytest.mark.parametrize("field,coordinate,fragment", [
    (_field("a^2-1"), "a", "reducible"),
    (_field(), {"numerator": "1", "denominator": "a^2+1"},
     "not invertible"),
])
def test_bad_field_and_unlicensed_denominator_are_inconclusive(
        field, coordinate, fragment):
    graph = _graph([_model(), _claim(coordinate, field=field)])
    verdict, why, receipt = V.point_witness(graph, "C")
    assert verdict == V.UNVERIFIED
    assert fragment in why
    assert receipt is None


def test_extension_witness_does_not_smuggle_in_ordered_ambient_semantics():
    model = _model(universe="REAL_CLOSURE")
    model["embedding"] = {
        "kind": "REAL", "var": "x",
        "isolating_interval": {"lo": "0", "hi": "1"},
    }
    graph = _graph([model, _claim()])
    verdict, why, receipt = V.point_witness(graph, "C")
    assert verdict == V.UNVERIFIED
    assert "ALGEBRAIC_CLOSURE" in why
    assert receipt is None


def test_extension_witness_records_native_authority_without_singular(tmp_path):
    S.append([_model(), _claim()], str(tmp_path))
    results = V.verify_all(
        root=str(tmp_path), record=True,
        backend=cas.SingularBackend(binary_version="unavailable:test"))

    assert [(subject, oid, verdict)
            for subject, oid, verdict, _why in results] == [
                ("witness", "C", V.WITNESS_VERIFIED)]
    graph = S.load(S.graph_path(str(tmp_path)))
    event = next(iter(graph.verdicts.values()))
    assert event["current"] is True
    assert event["verifier"] == "verify.extension_point_witness"
    assert P.native_provenance(event["backend"]) is not None
    assert graph.claims["C"]["witness_verdict"] == V.WITNESS_VERIFIED


def test_native_provenance_rejects_a_manifest_claiming_backend_executions():
    """Non-empty `executions` disqualifies a manifest from the native,
    trace-free provenance class -- an adversary cannot smuggle real (or
    fabricated) CAS work through the native fast path to dodge the
    binary-version staleness check that a Singular-labeled manifest must
    still pass."""
    manifest = dict(P.native_execution_provenance())
    manifest["executions"] = [{"aborted": False, "returncode": 0,
                               "stdout_fingerprint": B.text_fingerprint("x")}]
    encoded = P.encode_execution_provenance(manifest)
    assert P.native_provenance(encoded) is None


def test_singular_labeled_empty_trace_still_pays_the_binary_version_toll(
        tmp_path):
    """A verdict can structurally qualify for the trace-free exemption (real
    native math, e.g. a checked extension witness) while still being labeled
    with the Singular backend contract instead of the native one. Unlike a
    genuinely native manifest, that labeling is never exempt from
    binary-version currency -- proving native-vs-Singular is a real
    distinction with consequences, not an interchangeable presentation of
    the same fact. Fabricating a Singular label for work that was never run
    through Singular does not gain an adversary anything: it only trades an
    exemption for a check the fabrication will fail."""
    S.append([_model(), _claim()], str(tmp_path))
    graph = S.load(S.graph_path(str(tmp_path)))
    verdict, why, receipt = V.point_witness(graph, "C")
    assert verdict == V.WITNESS_VERIFIED

    fake_singular_manifest = {
        "schema": 2, "contract": "singular",
        "implementation": "grandportage.cas.SingularBackend",
        "implementation_version": B.SINGULAR_IMPLEMENTATION_VERSION, "protocol_version": 2,
        "binary_version": "Singular for x86_64 version 0.0.0 (fabricated)",
        "executions": [],
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", []),
    }
    encoded = P.encode_execution_provenance(fake_singular_manifest)
    assert P.native_provenance(encoded) is None, (
        "a Singular-schema manifest must never decode as native provenance, "
        "empty trace or not")

    event = V._verdict_event(
        graph, "witness", "C", verdict, why, receipt,
        execution=fake_singular_manifest)
    graph.apply(event, "number-field-v1", 99)
    # The graph was loaded with check_binary_version=True (S.load's default),
    # so the fabricated Singular label is judged as soon as it folds -- no
    # reload needed to see it lose currency.
    stored = graph.verdicts[event["id"]]
    assert stored["current"] is False
    # Whether this environment has Singular installed or not, the fabricated
    # binary_version cannot possibly match the live process's -- either it
    # disagrees outright or no live identity is available to agree with.
    assert "backend binary" in stored["stale_reason"], stored["stale_reason"]
    assert graph.claims["C"].get("witness_verdict") != V.WITNESS_VERIFIED


def test_extension_receipt_tampering_is_rejected_on_fold():
    graph = _graph([_model(), _claim()])
    verdict, why, receipt = V.point_witness(graph, "C")
    event = V._verdict_event(
        graph, "witness", "C", verdict, why, receipt,
        execution=P.native_execution_provenance())
    graph.apply(event, "number-field-v1", 10)
    assert graph.claims["C"]["witness_verdict"] == V.WITNESS_VERIFIED

    attacked = _graph([_model(), _claim()])
    tampered = deepcopy(event)
    tampered["id"] = "V_BAD"
    tampered["representation"]["coordinates"]["x"] = ["1"]
    tampered.update(P.metadata(
        attacked, "witness", "C", verdict=verdict,
        verifier="verify.extension_point_witness",
        execution=P.native_execution_provenance(),
        representation=tampered["representation"]))
    with pytest.raises(S.GraphError, match="does not replay"):
        attacked.apply(tampered, "number-field-v1", 11)
