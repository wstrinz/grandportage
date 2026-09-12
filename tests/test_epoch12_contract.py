"""Executable answer keys frozen before epoch-12 graph integration."""

from copy import deepcopy

import pytest

from grandportage import field as E
from grandportage import check as C
from grandportage import format as F
from grandportage import kernel as K
from grandportage import ordered_sos as SOS
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def test_concrete_extension_is_not_universal_instantiation():
    assert E.concrete_extension("Q", "R").allowed
    assert E.concrete_extension("R", "C").allowed
    assert not E.concrete_extension("R", "Q").allowed
    assert not E.concrete_extension("R", "ANY_ORDERED").allowed
    assert not E.concrete_extension("ANY_ORDERED", "R").allowed


def test_ordered_and_characteristic_zero_reach_have_distinct_targets():
    ordered = {"kind": "ORDERED"}
    assert E.instantiate(ordered, "Q").allowed
    assert E.instantiate(ordered, "R").allowed
    assert not E.instantiate(ordered, "C").allowed
    assert not E.instantiate(ordered, "F_2").allowed

    char_zero = {"kind": "CHAR_0"}
    assert E.instantiate(char_zero, "Q").allowed
    assert E.instantiate(char_zero, "R").allowed
    assert E.instantiate(char_zero, "C").allowed
    assert not E.instantiate(char_zero, "F_2").allowed


def test_field_specific_and_none_never_generalize():
    finite = {"kind": "FIELD_SPECIFIC", "field": "F_2"}
    assert E.instantiate(finite, "F_2").allowed
    assert not E.instantiate(finite, "Q").allowed
    assert not E.instantiate({"kind": "NONE"}, "Q").allowed
    with pytest.raises(E.FieldError, match="concrete field"):
        E.validate_reach({"kind": "FIELD_SPECIFIC", "field": "ANY_CHAR_0"})


def test_exact_identity_reach_is_model_bound_not_a_global_boolean():
    assert E.reach_for_exact_identity("Q") == {"kind": "CHAR_0"}
    assert E.reach_for_exact_identity("F_2") == {
        "kind": "FIELD_SPECIFIC", "field": "F_2"}


def test_format8_certificate_policy_is_structured_but_mints_no_reach():
    certificate = {
        "ev": "certificate", "id": "CUSTOM_ORDERED",
        "reach": {"kind": "ORDERED"},
        "why": "a verifier for this domain may earn ordered reach",
    }
    claim = {
        "ev": "claim", "id": "C", "model": "M", "kind": K.EMPTY,
        "statement": "claimed ordered emptiness",
        "certificate": "CUSTOM_ORDERED", "scope": "ANY_ORDERED",
    }
    graph = _typed_graph([_typed_model("M", "ANY_ORDERED"),
                          certificate, claim])
    assert graph.cert_records["CUSTOM_ORDERED"]["reach"] == {
        "kind": "ORDERED"}
    assert "certificate_reach" not in graph.claims["C"]
    changed = deepcopy(certificate)
    changed["reach"] = {"kind": "CHAR_0"}
    changed_graph = _typed_graph([
        _typed_model("M", "ANY_ORDERED"), changed, claim])
    assert (P.input_fingerprint(graph, "certificate", "C")
            != P.input_fingerprint(changed_graph, "certificate", "C"))

    bad = dict(certificate, id="BAD", base_changes=True)
    with pytest.raises(S.GraphError, match="unknown field.*base_changes"):
        _typed_graph([bad])


def test_compute_alias_agrees_or_refuses():
    assert E.model_compute_in({"compute_in": "Q"}) == "Q"
    assert E.model_compute_in({"coefficient_domain": "F_3"}) == "F_3"
    assert E.model_compute_in({"compute_in": "Q",
                               "coefficient_domain": "Q"}) == "Q"
    with pytest.raises(E.FieldError, match="identical"):
        E.model_compute_in({"compute_in": "Q",
                            "coefficient_domain": "F_3"})


def test_point_context_retains_universe_and_selected_embedding():
    q = {"about": "Q", "point_universe": "BASE"}
    r = {"about": "R", "point_universe": "BASE"}
    assert E.compatible_point_context(q, r).allowed

    closure = {"about": "Q", "point_universe": "ALGEBRAIC_CLOSURE"}
    assert not E.compatible_point_context(closure, r).allowed

    selected = {"about": "Q", "point_universe": "BASE",
                "embedding": {"kind": "REAL", "root": "+"}}
    swapped = deepcopy(selected)
    swapped["embedding"]["root"] = "-"
    assert not E.compatible_point_context(selected, swapped).allowed


def _model(generator="x^2+1"):
    return {
        "id": "M", "about": "ANY_ORDERED", "compute_in": "Q",
        "coefficient_domain": "Q", "characteristic": 0,
        "point_universe": "BASE", "ring_vars": ["x"],
        "generators": [generator],
    }


def _certificate():
    return {
        "method": SOS.METHOD,
        "ring_vars": ["x"],
        "generators": ["x^2+1"],
        "squares": ["x"],
        "cofactors": ["-1"],
    }


def test_rational_sos_replays_without_search_and_earns_ordered_answer_key():
    receipt = SOS.verify(_model(), _certificate())
    assert receipt["method"] == SOS.METHOD
    assert receipt["squares"] == ["x"]
    assert E.instantiate({"kind": "ORDERED"}, "Q").allowed
    assert E.instantiate({"kind": "ORDERED"}, "R").allowed
    assert not E.instantiate({"kind": "ORDERED"}, "C").allowed


def test_false_or_detached_ordered_certificates_refuse():
    false = _certificate()
    false["cofactors"] = ["1"]
    with pytest.raises(SOS.OrderedSOSError, match="invalid"):
        SOS.verify(_model(), false)

    detached = _certificate()
    detached["generators"] = ["x^2+2"]
    with pytest.raises(SOS.OrderedSOSError, match="do not match"):
        SOS.verify(_model(), detached)


def test_ordered_replay_refuses_positive_characteristic_and_bad_shape():
    finite = _model()
    finite.update({"compute_in": "F_2", "coefficient_domain": "F_2",
                   "characteristic": 2})
    with pytest.raises(SOS.OrderedSOSError, match="over Q"):
        SOS.verify(finite, _certificate())

    extra = _certificate()
    extra["search_budget"] = 10
    with pytest.raises(SOS.OrderedSOSError, match="closed"):
        SOS.verify(_model(), extra)


def _typed_model(mid, about):
    return {
        "ev": "model", "id": mid, "about": about,
        "compute_in": "Q", "coefficient_domain": "Q",
        "characteristic": 0, "point_universe": "BASE",
        "ring_vars": ["x"], "generators": ["x^2+1"],
    }


def _typed_graph(events):
    return S.Graph().apply_all([
        (event, "epoch12-contract", index)
        for index, event in enumerate([F.meta_event()] + events, 1)
    ]).validate()


def test_ordered_reach_is_bound_only_after_current_exact_replay(tmp_path):
    claim = {
        "ev": "claim", "id": "C-ORDERED", "model": "M-ALL",
        "kind": K.EMPTY, "statement": "no ordered-field point",
        "certificate": "ORDERED_SOS_CERT", "scope": "ANY_ORDERED",
    }
    edge_r = {
        "ev": "edge", "id": "E-R", "src": "M-ALL", "dst": "M-R",
        "type": K.BASE_EXTENSION, "map_kind": K.IDENTITY_MAP,
        "why": "instantiate the ordered theorem at R",
    }
    edge_c = dict(edge_r, id="E-C", dst="M-C",
                  why="C is not ordered")
    events = [_typed_model("M-ALL", "ANY_ORDERED"),
              _typed_model("M-R", "R"), _typed_model("M-C", "C"),
              edge_r, edge_c, claim]
    S.append(events, str(tmp_path))
    before = S.load(S.graph_path(str(tmp_path)))
    assert not C.probe(before, "C-ORDERED", "E-R", K.ALONG).licensed

    results = V.verify_all(
        root=str(tmp_path), record=True,
        supplied_certificates={"C-ORDERED": _certificate()})
    assert [(subject, oid, verdict) for subject, oid, verdict, _ in results
            if subject == "certificate"] == [
        ("certificate", "C-ORDERED", "VERIFIED")]

    graph = S.load(S.graph_path(str(tmp_path)))
    assert graph.claims["C-ORDERED"]["certificate_reach"] == {
        "kind": "ORDERED"}
    assert C.probe(graph, "C-ORDERED", "E-R", K.ALONG).licensed
    c_ruling = C.probe(graph, "C-ORDERED", "E-C", K.ALONG)
    assert not c_ruling.licensed
    assert "ORDERED reach" in c_ruling.reason


def test_about_changes_endpoint_fingerprints_and_point_paths_refuse_mismatch():
    claim = {
        "ev": "claim", "id": "W", "model": "M-C", "kind": K.NONEMPTY,
        "statement": "the rational point exists", "witness_kind": K.EXHIBITED,
        "witness_point": {"x": "0"},
    }
    edge = {
        "ev": "edge", "id": "E", "src": "M-C", "dst": "M-R",
        "type": K.NECESSARY_CONDITION, "map_kind": K.IDENTITY_MAP,
        "why": "same equations under a field change",
    }
    graph = _typed_graph([
        _typed_model("M-Q", "Q"), _typed_model("M-C", "C"),
        _typed_model("M-R", "R"), edge, claim])
    assert (P.endpoint_fingerprint(graph.models["M-Q"])
            != P.endpoint_fingerprint(graph.models["M-C"]))
    ruling = C.probe(graph, "W", "E", K.ALONG)
    assert not ruling.licensed
    assert "field-context" in ruling.reason


def test_same_as_cannot_alias_distinct_or_missing_point_contexts():
    alias = {"ev": "same_as", "id": "A", "models": ["M-Q", "M-R"],
             "why": "purported duplicate"}
    with pytest.raises(S.GraphError, match="point-bearing object"):
        _typed_graph([_typed_model("M-Q", "Q"),
                      _typed_model("M-R", "R"), alias])

    missing = {"ev": "model", "id": "M-OLD", "field": "Q"}
    missing_alias = dict(alias, id="A-MISSING", models=["M-Q", "M-OLD"])
    with pytest.raises(S.GraphError, match="Missing context"):
        _typed_graph([_typed_model("M-Q", "Q"), missing, missing_alias])


@pytest.mark.parametrize("edge_type,direction", [
    (K.EQUIVALENCE, K.ALONG),
    (K.EQUIVALENCE, K.AGAINST),
    (K.NECESSARY_CONDITION, K.ALONG),
    (K.BASE_EXTENSION, K.ALONG),
    (K.IMAGE_CLOSURE, K.ALONG),
    (K.RESTRICTION, K.ALONG),
])
def test_no_point_licensing_edge_type_bypasses_field_context(
        edge_type, direction):
    src_about, dst_about = (("R", "C") if direction == K.AGAINST
                            else ("C", "R"))
    claim_model = "DST" if direction == K.AGAINST else "SRC"
    claim = {
        "ev": "claim", "id": "W", "model": claim_model,
        "kind": K.NONEMPTY, "statement": "an exhibited point",
        "witness_kind": K.EXHIBITED, "witness_point": {"x": "0"},
    }
    edge = {
        "ev": "edge", "id": "E", "src": "SRC", "dst": "DST",
        "type": edge_type, "map_kind": K.IDENTITY_MAP,
        "why": "exercise the otherwise licensed point cell",
    }
    graph = _typed_graph([
        _typed_model("SRC", src_about), _typed_model("DST", dst_about),
        edge, claim])
    ruling = C.probe(graph, "W", "E", direction)
    assert not ruling.licensed
    assert ruling.rule == "field_context"


def _family_events(decides="BOTH", proved=True):
    return [
        {"ev": "family", "id": "F", "count": 2,
         "desc": "two bounded cases", "members": ["E5", "E6"],
         "enumeration": "C-ENUM"},
        {"ev": "claim", "id": "C-ENUM", "family": "F",
         "kind": K.PREDICATE, "statement": "exactly two cases",
         "asserts_count": 2},
        {"ev": "evidence", "id": "EV-ENUM", "for": "C-ENUM",
         "method": "ENUMERATION", "ran": "bounded-enum",
         "what": "checked the complete input space", "decides": decides},
        {"ev": "claim", "id": "D", "family": "F", "kind": K.COUNT,
         "statement": "one proved and one open", "splits": "F",
         "groups": [
             {"id": "G-PROVED", "verdict": "proved", "settles": 1,
              "exhibited": ["E5"]},
             {"id": "G-OPEN", "verdict": "open", "settles": 1,
              "exhibited": ["E6"]},
         ],
         "method": "exact checker", "proves": ["G-PROVED"] if proved else [],
         "why": "the exact checker decides only the proved group"},
        {"ev": "claim", "id": "C-FAMILY", "family": "F",
         "kind": K.PREDICATE, "statement": "the proved member has P",
         "rests_on": "G-PROVED"},
        _typed_model("M-E5", "Q"),
        {"ev": "claim", "id": "C-MODEL", "model": "M-E5",
         "kind": K.PREDICATE, "statement": "the model side condition holds"},
        {"ev": "family_bridge", "id": "B-E5", "family": "F",
         "enumeration": "C-ENUM", "coverage": "D", "group": "G-PROVED",
         "member": "E5", "model": "M-E5",
         "why": "M-E5 is the exhibited E5 member"},
    ]


@pytest.mark.parametrize("order", [
    ("C-FAMILY", "C-MODEL"), ("C-MODEL", "C-FAMILY")])
def test_family_bridge_composes_independently_of_premise_order(order):
    inference = {
        "ev": "inference", "id": "I",
        "premises": [{"claim": claim_id, "path": []} for claim_id in order],
        "family_bridges": {"C-FAMILY": "B-E5"},
        "concludes_kind": K.PREDICATE, "asserted": "P holds at M-E5",
    }
    graph = _typed_graph(_family_events() + [inference])
    assert graph.inferences["I"]["concludes_at"] == "M-E5"
    assert C.audit_inference(graph, "I")[0]


@pytest.mark.parametrize("decides,proved,fragment", [
    ("EXCLUSIONS", True, "decides BOTH"),
    ("BOTH", False, "proved groups"),
])
def test_family_bridge_refuses_one_sided_evidence_or_open_group(
        decides, proved, fragment):
    inference = {
        "ev": "inference", "id": "I", "claim": "C-FAMILY", "path": [],
        "family_bridges": {"C-FAMILY": "B-E5"},
        "asserted": "P holds at M-E5",
    }
    with pytest.raises(S.GraphError, match=fragment):
        _typed_graph(_family_events(decides=decides, proved=proved)
                     + [inference])


def test_family_claim_without_bridge_keeps_the_phase_a_refusal():
    inference = {
        "ev": "inference", "id": "I", "claim": "C-FAMILY", "path": [],
        "asserted": "P holds somewhere unspecified",
    }
    with pytest.raises(S.GraphError, match="without an explicit family_bridge"):
        _typed_graph(_family_events()[:-1] + [inference])
