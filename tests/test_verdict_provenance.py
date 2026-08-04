"""Epoch-1 verifier answers are evidence only while their provenance matches."""

import pytest

from grandportage import backend as B
from grandportage import format as F
from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def _identity_graph(generator="x"):
    graph = S.Graph()
    graph.apply(F.meta_event())
    graph.apply({
        "ev": "model", "id": "M", "what": "a line",
        "characteristic": 0, "ring_vars": ["x"],
        "generators": [generator],
    })
    graph.apply({
        "ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
        "statement": "x vanishes", "lhs": "x", "rhs": "0",
        "ring_vars": ["x"], "identity_origin": K.DERIVED,
        "established_by": "RAN", "ladder": "exact-checked",
    })
    return graph


def _execution(with_trace=True):
    trace = ([{
        "semantic_input_fingerprint": B.semantic_fingerprint(
            "test_semantic_input", []),
        "program_fingerprint": B.text_fingerprint("test program"),
        "stdout_fingerprint": B.text_fingerprint("test stdout"),
        "stderr_fingerprint": B.text_fingerprint(""),
        "artifact_fingerprint": B.semantic_fingerprint(
            "test_execution_artifact", []),
        "returncode": 0,
        "aborted": False,
    }] if with_trace else [])
    return {
        "schema": 2,
        "contract": B.SINGULAR_CONTRACT,
        "implementation": B.SINGULAR_IMPLEMENTATION,
        "implementation_version": B.SINGULAR_IMPLEMENTATION_VERSION,
        "protocol_version": B.BACKEND_PROTOCOL_VERSION,
        "binary_version": "Singular 4.2.1",
        "executions": trace,
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", trace
        ),
    }


def _verdict(graph, verdict="VERIFIED_DERIVED"):
    return V._verdict_event(
        graph, "claim", "C", verdict, "x reduces to zero modulo (x)",
        execution=_execution())


def test_fresh_epoch1_verdict_is_active():
    graph = _identity_graph()
    event = _verdict(graph)

    graph.apply(event)

    assert graph.claims["C"]["identity_verdict"] == "VERIFIED_DERIVED"
    assert graph.verdicts[event["id"]]["current"] is True


def test_fresh_verdict_carries_detailed_backend_provenance():
    event = _verdict(_identity_graph())

    manifest = P.backend_provenance(event["backend"])
    assert manifest["contract"] == "singular"
    assert manifest["implementation"].endswith("SingularBackend")
    assert manifest["implementation_version"] == B.SINGULAR_IMPLEMENTATION_VERSION
    assert manifest["protocol_version"] == B.BACKEND_PROTOCOL_VERSION
    assert manifest["binary_version"] == "Singular 4.2.1"
    assert manifest["trace_fingerprint"] == B.semantic_fingerprint(
        "backend_execution_trace", manifest["executions"]
    )


def test_exact_ring_iso_certificate_allows_a_verifier_native_empty_trace():
    graph = S.Graph()
    graph.apply(F.meta_event())
    for model_id in ("A", "B"):
        graph.apply({
            "ev": "model", "id": model_id, "what": model_id,
            "characteristic": 0, "ring_vars": ["x"],
            "generators": ["x"],
        })
    graph.apply({
        "ev": "edge", "id": "E", "src": "A", "dst": "B",
        "type": K.EQUIVALENCE, "map_kind": K.POLYNOMIAL,
        "why": "identity", "ring_iso": True,
        "forward": {"x": "x"}, "inverse": {"x": "x"},
        "ring_iso_certificate": {
            "schema": "mapped_ring_iso_v1",
            "forward_cofactors": [["1"]],
            "inverse_cofactors": [["1"]],
        },
    })
    verdict, why = V.ring_iso(graph, "E")
    assert verdict == V.ISO_VERIFIED, why
    event = V._verdict_event(
        graph, "ring_iso", "E", verdict, why,
        execution=_execution(with_trace=False))

    graph.apply(event)

    assert graph.verdicts[event["id"]]["current"] is True
    assert graph.edges["E"]["ring_iso_verdict"] == V.ISO_VERIFIED

def test_v050_reader_shape_accepts_m2_event_but_its_backend_rule_is_stale():
    """Freeze the v0.5.0 closed schema and backend equality rule.

    These are copied from the tagged reader, whose native format-1 verdict
    fields already included `backend` as an opaque nonempty string and whose
    currentness check required that string to equal exactly `singular`.
    """
    v050_fields = {
        "ev", "id", "subject", "of", "verdict", "why", "representation",
        "verifier", "verifier_version", "kernel_epoch", "backend",
        "input_fingerprint",
    }
    event = _verdict(_identity_graph())

    assert set(event).issubset(v050_fields)
    assert event["backend"] != "singular"


def test_trace_requirement_distinguishes_backend_and_structural_authority():
    claim_graph = _identity_graph()
    claim_event = V._verdict_event(
        claim_graph, "claim", "C", "VERIFIED_DERIVED", "why",
        execution=_execution(with_trace=False))
    claim_graph.apply(claim_event)

    assert claim_graph.verdicts[claim_event["id"]]["current"] is False
    assert "lacks a backend execution trace" in (
        claim_graph.verdicts[claim_event["id"]]["stale_reason"])

    edge_graph = S.Graph()
    edge_graph.apply(F.meta_event())
    for mid, generators in (("A", ["x"]), ("B", [])):
        edge_graph.apply({
            "ev": "model", "id": mid, "what": mid,
            "characteristic": 0, "ring_vars": ["x"],
            "generators": generators,
        })
    edge_graph.apply({
        "ev": "edge", "id": "E", "src": "A", "dst": "B",
        "type": K.NECESSARY_CONDITION, "map_kind": K.IDENTITY_MAP,
        "why": "the target zero ideal has no generators to reduce",
    })
    edge_event = V._verdict_event(
        edge_graph, "edge", "E", "VERIFIED", "vacuous containment",
        execution=_execution(with_trace=False))
    edge_graph.apply(edge_event)

    assert edge_graph.verdicts[edge_event["id"]]["current"] is True
    assert edge_graph.edges["E"]["containment"] == "VERIFIED"

    ordinary = S.Graph()
    ordinary.apply(F.meta_event())
    for mid, generators in (("A", ["x"]), ("B", ["x^2"])):
        ordinary.apply({
            "ev": "model", "id": mid, "what": mid,
            "characteristic": 0, "ring_vars": ["x"],
            "generators": generators,
        })
    ordinary.apply({
        "ev": "edge", "id": "E", "src": "A", "dst": "B",
        "type": K.NECESSARY_CONDITION, "map_kind": K.IDENTITY_MAP,
        "why": "non-vacuous containment needs a reduction",
    })
    fabricated = V._verdict_event(
        ordinary, "edge", "E", "VERIFIED", "no reduction retained",
        execution=_execution(with_trace=False))
    ordinary.apply(fabricated)

    assert ordinary.verdicts[fabricated["id"]]["current"] is False
    assert "not a verifier-native structural decision" in (
        ordinary.verdicts[fabricated["id"]]["stale_reason"])

    cross_characteristic = S.Graph()
    cross_characteristic.apply(F.meta_event())
    for mid, characteristic, generators in (
            ("A", 0, ["x"]), ("B", 2, [])):
        cross_characteristic.apply({
            "ev": "model", "id": mid, "what": mid,
            "characteristic": characteristic, "ring_vars": ["x"],
            "generators": generators,
        })
    cross_characteristic.apply({
        "ev": "edge", "id": "E", "src": "A", "dst": "B",
        "type": K.NECESSARY_CONDITION, "map_kind": K.IDENTITY_MAP,
        "why": "different coefficient fields",
    })
    invalid_vacuity = V._verdict_event(
        cross_characteristic, "edge", "E", "VERIFIED", "empty target",
        execution=_execution(with_trace=False))
    cross_characteristic.apply(invalid_vacuity)
    assert cross_characteristic.verdicts[
        invalid_vacuity["id"]]["current"] is False

    def operation_graph(built_characteristic):
        graph = S.Graph()
        graph.apply(F.meta_event())
        graph.apply({
            "ev": "model", "id": "A", "what": "source",
            "characteristic": 0, "ring_vars": ["x", "y"],
            "generators": ["y"],
        })
        graph.apply({
            "ev": "model", "id": "B", "what": "empty output",
            "characteristic": built_characteristic, "ring_vars": ["x"],
            "generators": [], "eliminated": ["y"],
        })
        graph.apply({
            "ev": "edge", "id": "E", "src": "A", "dst": "B",
            "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
            "why": "eliminate y", "built_by_operation": "Eliminate",
        })
        event = V._verdict_event(
            graph, "operation", "E", "VERIFIED", "empty output",
            execution=_execution(with_trace=False))
        graph.apply(event)
        return graph, event

    valid_operation, valid_event = operation_graph(0)
    assert valid_operation.verdicts[valid_event["id"]]["current"] is True
    invalid_operation, invalid_event = operation_graph(2)
    assert invalid_operation.verdicts[invalid_event["id"]]["current"] is False

    def saturation_graph(saturated_at=None):
        graph = S.Graph()
        graph.apply(F.meta_event())
        graph.apply({
            "ev": "model", "id": "A", "what": "source",
            "characteristic": 0, "ring_vars": ["x"],
            "generators": ["x"],
        })
        built = {
            "ev": "model", "id": "B", "what": "saturation output",
            "characteristic": 0, "ring_vars": ["x"], "generators": [],
        }
        if saturated_at is not None:
            built["saturated_at"] = saturated_at
        graph.apply(built)
        graph.apply({
            "ev": "edge", "id": "E", "src": "B", "dst": "A",
            "type": K.NECESSARY_CONDITION, "map_kind": K.IDENTITY_MAP,
            "why": "saturate at x", "built_by_operation": "SaturateClosure",
        })
        event = V._verdict_event(
            graph, "operation", "E", "VERIFIED", "empty output",
            execution=_execution(with_trace=False))
        graph.apply(event)
        return graph, event

    invalid_saturation, invalid_sat_event = saturation_graph()
    assert invalid_saturation.verdicts[
        invalid_sat_event["id"]]["current"] is False
    valid_saturation, valid_sat_event = saturation_graph("x")
    assert valid_saturation.verdicts[
        valid_sat_event["id"]]["current"] is True


def test_pre_marker_singular_v1_verdict_is_readable_but_stale_under_v2():
    graph = _identity_graph()
    old_execution = _execution()
    old_execution["implementation_version"] = 1
    event = V._verdict_event(
        graph, "claim", "C", "VERIFIED_DERIVED",
        "Singular implementation v1 reduced x to zero",
        execution=old_execution,
    )
    event["id"] = "v.C.singular-implementation-v1"

    graph.apply(event)

    stored = graph.verdicts[event["id"]]
    assert stored["current"] is False
    assert "backend execution provenance" in stored["stale_reason"]
    assert "identity_verdict" not in graph.claims["C"]
    assert P.backend_provenance(event["backend"]) is None


def test_pre_artifact_singular_v2_verdict_is_readable_but_stale():
    graph = _identity_graph()
    old_execution = _execution()
    old_execution["implementation_version"] = 2
    event = V._verdict_event(
        graph, "claim", "C", "VERIFIED_DERIVED",
        "Singular v2 retained hashes but no durable raw object",
        execution=old_execution,
    )
    event["id"] = "v.C.singular-implementation-v2"

    graph.apply(event)

    stored = graph.verdicts[event["id"]]
    assert stored["current"] is False
    assert "backend execution provenance" in stored["stale_reason"]
    assert "identity_verdict" not in graph.claims["C"]



def test_pre_m2_epoch1_verdict_is_readable_but_stale():
    graph = _identity_graph()
    event = _verdict(graph)
    event["backend"] = "singular"
    event["id"] = "v.C.pre-m2"

    graph.apply(event)

    assert "identity_verdict" not in graph.claims["C"]
    assert "backend execution provenance" in graph.verdicts[event["id"]]["stale_reason"]


def test_v2_verdict_refuses_fabricated_missing_execution_provenance():
    with pytest.raises(ValueError, match="explicit execution provenance"):
        V._verdict_event(
            _identity_graph(), "claim", "C", "VERIFIED_DERIVED", "why")


def test_legacy_verified_remains_readable_but_inactive():
    graph = S.Graph()
    graph.apply({
        "ev": "model", "id": "M", "what": "a line",
        "characteristic": 0, "ring_vars": ["x"], "generators": ["x"],
    })
    graph.apply({
        "ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
        "statement": "x vanishes", "lhs": "x", "rhs": "0",
        "ring_vars": ["x"], "identity_origin": K.DERIVED,
        "established_by": "RAN", "ladder": "exact-checked",
    })
    event = {
        "ev": "verdict", "id": "v.C.legacy", "subject": "claim",
        "of": "C", "verdict": "VERIFIED_DERIVED",
        "why": "an epoch-0 verifier said so",
    }

    graph.apply(event)

    assert "identity_verdict" not in graph.claims["C"]
    assert graph.verdicts[event["id"]]["current"] is False
    assert "epoch-0" in graph.verdicts[event["id"]]["stale_reason"]


def test_verdict_for_different_semantic_input_is_stale():
    original = _identity_graph("x")
    event = _verdict(original)
    changed = _identity_graph("x^2")

    changed.apply(event)

    assert "identity_verdict" not in changed.claims["C"]
    assert "fingerprint" in changed.verdicts[event["id"]]["stale_reason"]


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("verifier", "verify.some_old_identity"),
        ("verifier_version", 999),
        ("kernel_epoch", F.KERNEL_EPOCH + 1),
        ("backend", "not-singular"),
    ],
)
def test_mismatched_verifier_kernel_or_backend_is_stale(field, value):
    graph = _identity_graph()
    event = _verdict(graph)
    event[field] = value
    event["id"] = "v.C.mismatch.%s" % field

    graph.apply(event)

    assert "identity_verdict" not in graph.claims["C"]
    assert graph.verdicts[event["id"]]["current"] is False


@pytest.mark.parametrize("mutation", ["implementation", "protocol", "trace", "version", "entry", "test-double"])
def test_tampered_backend_descriptor_is_stale(mutation):
    graph = _identity_graph()
    event = _verdict(graph)
    manifest = P.backend_provenance(event["backend"])
    if mutation == "implementation":
        manifest["implementation"] = "evil.Backend"
    elif mutation == "protocol":
        manifest["protocol_version"] -= 1
    elif mutation == "trace":
        manifest["trace_fingerprint"] = "sha256:" + "0" * 64
    elif mutation == "version":
        manifest["binary_version"] = "unavailable: OSError"
    elif mutation == "entry":
        manifest["executions"] = [{}]
        manifest["trace_fingerprint"] = B.semantic_fingerprint(
            "backend_execution_trace", manifest["executions"])
    else:
        manifest["binary_version"] = "test-double"
    event["backend"] = P.encode_backend_provenance(manifest)
    event["id"] = "v.C.tampered.%s" % mutation

    graph.apply(event)

    assert "identity_verdict" not in graph.claims["C"]
    assert graph.verdicts[event["id"]]["current"] is False


def _never(*_args, **_kwargs):
    raise AssertionError("a verifier with unknown characteristic ran the CAS")


def _missing_characteristic_graph():
    graph = S.Graph()
    graph.models.update({
        "A": {"id": "A", "ring_vars": ["x"], "generators": ["x"]},
        "B": {"id": "B", "ring_vars": ["x"], "generators": ["x^2"]},
    })
    return graph


def test_identity_declines_unknown_characteristic_before_cas():
    graph = _missing_characteristic_graph()
    graph.claims["C"] = {
        "id": "C", "model": "A", "kind": K.IDENTITY,
        "lhs": "x", "rhs": "0", "ring_vars": ["x"],
    }
    verdict, why = V.identity(graph, "C", _runner=_never)
    assert verdict == V.UNVERIFIED
    assert "no characteristic" in why


@pytest.mark.parametrize("checker", ["containment", "ring_iso", "operation"])
def test_edge_verifiers_decline_unknown_characteristic_before_cas(checker):
    graph = _missing_characteristic_graph()
    if checker == "containment":
        graph.edges["E"] = {
            "id": "E", "src": "A", "dst": "B",
            "type": K.NECESSARY_CONDITION, "map_kind": K.IDENTITY_MAP,
        }
        out = V.containment(graph, "E", _runner=_never)
    elif checker == "ring_iso":
        graph.edges["E"] = {
            "id": "E", "src": "A", "dst": "B", "type": K.EQUIVALENCE,
            "map_kind": K.IDENTITY_MAP,
            "forward": {"x": "x"}, "inverse": {"x": "x"},
        }
        out = V.ring_iso(graph, "E", _runner=_never)
    else:
        graph.edges["E"] = {
            "id": "E", "src": "B", "dst": "A",
            "built_by_operation": "SaturateClosure",
        }
        graph.models["B"]["saturated_at"] = "x"
        out = V.operation_output(graph, "E", _runner=_never)
    assert out[0] == V.UNVERIFIED
    assert "no characteristic" in out[1]


def test_partition_witness_and_certificate_decline_unknown_characteristic():
    graph = _missing_characteristic_graph()
    graph.models["C"] = {
        "id": "C", "ring_vars": ["x"], "generators": ["x-1"],
    }
    graph.partitions["P"] = {
        "id": "P", "parent": "A", "branches": ["B", "C"],
    }
    graph.claims["W"] = {
        "id": "W", "model": "A", "kind": K.NONEMPTY,
        "witness_point": {"x": 0},
    }
    graph.claims["U"] = {
        "id": "U", "model": "A", "kind": K.EMPTY,
        "certificate": "UNIT_IDEAL_CERT",
    }

    results = [
        V.partition_exhaustiveness(graph, "P", _runner=_never),
        V.point_witness(graph, "W", _runner=_never),
        V.unit_ideal(graph, "U", _runner=_never),
    ]
    for verdict, why, *_rest in results:
        assert verdict == V.UNVERIFIED
        assert "no characteristic" in why

def _elimination_graph():
    graph = S.Graph()
    graph.apply(F.meta_event())
    graph.apply({
        "ev": "model", "id": "SOURCE", "what": "source",
        "characteristic": 0, "ring_vars": ["y", "x"],
        "generators": ["y*x-1", "y^2-x"],
    })
    graph.apply({
        "ev": "model", "id": "TARGET", "what": "target",
        "characteristic": 0, "ring_vars": ["x"],
        "generators": ["x^3-1"], "eliminated": ["y"],
    })
    graph.apply({
        "ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
        "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
        "why": "eliminate y", "built_by_operation": "Eliminate",
    })
    return graph


def _section_representation():
    return {
        "method": "polynomial_section_v1",
        "section": {"y": "x^2"},
        "source_ring_vars": ["y", "x"],
        "target_ring_vars": ["x"],
        "eliminated": ["y"],
        "source_generators": ["y*x-1", "y^2-x"],
        "target_generators": ["x^3-1"],
        "images": {"y": "x^2", "x": "x"},
        "rows": [
            {"source_generator": "y*x-1", "substituted": "x^3-1",
             "cofactors": ["1"]},
            {"source_generator": "y^2-x", "substituted": "x^4-x",
             "cofactors": ["x"]},
        ],
    }


def test_verified_section_projects_distinct_contraction_authority():
    graph = _elimination_graph()
    event = V._verdict_event(
        graph, "elimination", "E", V.SECTION_VERIFIED,
        "section checked", _section_representation(), execution=_execution())
    graph.apply(event)

    edge = graph.edges["E"]
    assert edge["contraction_verdict"] == V.SECTION_VERIFIED
    assert edge["contraction_representation"]["section"] == {"y": "x^2"}
    assert "representation" not in edge
    assert graph.verdicts[event["id"]]["current"] is True


def test_rejected_section_does_not_erase_prior_exact_certificate():
    graph = _elimination_graph()
    success = V._verdict_event(
        graph, "elimination", "E", V.SECTION_VERIFIED,
        "section checked", _section_representation(), execution=_execution())
    graph.apply(success)
    rejected = V._verdict_event(
        graph, "elimination", "E", V.SECTION_REJECTED,
        "this different proposed section fails",
        execution=_execution(with_trace=False))
    graph.apply(rejected)

    assert graph.edges["E"]["contraction_verdict"] == V.SECTION_VERIFIED
    assert graph.edges["E"]["contraction_why"] == "section checked"
    assert graph.verdicts[rejected["id"]]["current"] is True


def test_elimination_authority_fields_are_not_declarable():
    graph = _elimination_graph()
    with pytest.raises(S.GraphError) as exc:
        graph.apply({
            "ev": "edge", "id": "FORGED", "src": "SOURCE", "dst": "TARGET",
            "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
            "why": "forged", "contraction_verdict": V.SECTION_VERIFIED,
        })
    assert ("VERDICT and not a declaration" in str(exc.value)
            or "unknown field `contraction_verdict`" in str(exc.value))
def test_verified_section_without_proof_object_is_refused():
    graph = _elimination_graph()
    event = V._verdict_event(
        graph, "elimination", "E", V.SECTION_VERIFIED,
        "claims a section but stores none", execution=_execution())
    with pytest.raises(S.GraphError, match="needs its polynomial-section"):
        graph.apply(event)


def test_section_proof_object_must_match_its_exact_endpoints():
    graph = _elimination_graph()
    representation = _section_representation()
    representation["source_generators"] = ["invented"]
    representation["rows"][0]["source_generator"] = "invented"
    representation["rows"] = representation["rows"][:1]
    event = V._verdict_event(
        graph, "elimination", "E", V.SECTION_VERIFIED,
        "mismatched proof object", representation, execution=_execution())
    with pytest.raises(S.GraphError, match="does not match the exact source"):
        graph.apply(event)


def test_contraction_representation_is_a_guarded_computed_field():
    assert S.Graph._COMPUTED_FIELDS["contraction_representation"] == (
        "verify.elimination_section")
def test_mutating_stored_section_certificate_makes_verdict_stale():
    original_graph = _elimination_graph()
    event = V._verdict_event(
        original_graph, "elimination", "E", V.SECTION_VERIFIED,
        "section checked", _section_representation(), execution=_execution())
    event["representation"]["section"]["y"] = "x^99"
    event["representation"]["images"]["y"] = "x^99"
    event["representation"]["rows"][0]["substituted"] = "totally_forged"
    event["representation"]["rows"][0]["cofactors"] = ["also_forged"]

    replay = _elimination_graph()
    replay.apply(event)

    assert replay.verdicts[event["id"]]["current"] is False
    assert "fingerprint does not match" in (
        replay.verdicts[event["id"]]["stale_reason"])
    assert "contraction_verdict" not in replay.edges["E"]
def test_section_verdict_stamped_as_groebner_is_stale():
    graph = _elimination_graph()
    event = V._verdict_event(
        graph, "elimination", "E", V.SECTION_VERIFIED,
        "section checked", _section_representation(), execution=_execution())
    event["verifier"] = "verify.elimination_groebner"
    graph.apply(event)

    assert graph.verdicts[event["id"]]["current"] is False
    assert "contraction_verdict" not in graph.edges["E"]


def test_metadata_refuses_crossed_section_verifier_identity():
    graph = _elimination_graph()
    with pytest.raises(ValueError, match="must be produced"):
        V._verdict_event(
            graph, "elimination", "E", V.SECTION_VERIFIED,
            "section checked", _section_representation(),
            execution=_execution(), verifier="verify.elimination_groebner")