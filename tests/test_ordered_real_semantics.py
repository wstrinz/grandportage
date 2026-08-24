"""Unreleased v0.29 ordered-real contract and CFG23 replays."""

from copy import deepcopy

import pytest

from grandportage import cas
from grandportage import check as C
from grandportage import format as F
from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def _embedding(var, lo, hi):
    return {"var": var, "kind": "REAL",
            "isolating_interval": {"lo": lo, "hi": hi}}


def _model(mid="M", var="w", generator="w^2+8*w-20",
           interval=("2", "3"), universe=S.REAL_CLOSURE_POINT_UNIVERSE):
    return {
        "ev": "model", "id": mid, "what": mid,
        "coefficient_domain": "Q", "characteristic": 0,
        "point_universe": universe, "ring_vars": [var],
        "generators": [generator],
        "embedding": _embedding(var, *interval),
    }


def _claim(cid="P", model="M", relation="POSITIVE", expression="w"):
    return {
        "ev": "claim", "id": cid, "model": model,
        "kind": K.PREDICATE, "statement": "%s(%s)" % (relation, expression),
        "condition": {"all": [
            {"relation": relation, "expression": expression},
        ]},
    }


def _graph(events):
    graph = S.Graph()
    graph.apply_all([(event, "ordered-v0.29", index + 1)
                     for index, event in enumerate([F.meta_event()] + events)])
    return graph.validate()


@pytest.mark.parametrize("mutation,match", [
    (lambda model: model.pop("embedding"), "selected REAL embedding"),
    (lambda model: model["embedding"].update(kind="COMPLEX"),
     "selected REAL embedding"),
    (lambda model: model.update(point_universe="ALGEBRAIC_CLOSURE"),
     "point_universe REAL_CLOSURE"),
])
def test_ordered_models_and_atoms_are_coupled_to_selected_real_closure(
        mutation, match):
    model = _model()
    claim = _claim()
    mutation(model)
    with pytest.raises(S.GraphError, match=match):
        _graph([model, claim])


def test_ordered_claim_may_precede_its_model_in_a_merged_event_batch():
    graph = _graph([_claim(), _model()])
    assert graph.claims["P"]["model"] == "M"


@pytest.mark.parametrize("model,relation,expression", [
    (_model("PLUS"), "POSITIVE", "w"),
    (_model("MINUS", interval=("-10", "-9")), "NEGATIVE", "w"),
    (_model("F26", var="z", generator="z^3+3*z^2-z-7",
            interval=("1", "2")), "POSITIVE", "z"),
    (_model("ZERO"), "NONNEGATIVE", "w^2+8*w-20"),
    (_model("CMP"), "NEGATIVE", "w-5"),
])
def test_cfg23_22_26_and_exact_comparison_signs_verify(
        model, relation, expression):
    claim = _claim(model=model["id"], relation=relation,
                   expression=expression)
    graph = _graph([model, claim])
    verdict, why, representation = V.predicate_condition(graph, "P")
    assert verdict == V.CONDITION_VERIFIED, why
    assert representation["atoms"][0]["status"] == "VERIFIED_ORDERED_SIGN"
    assert (representation["atoms"][0]["cofactors"]["method"]
            == "selected_real_interval_v1")


def test_false_ordered_relation_is_computationally_refuted():
    graph = _graph([_model(), _claim(relation="NEGATIVE")])
    verdict, why, representation = V.predicate_condition(graph, "P")
    assert verdict == V.CONDITION_REFUTED
    assert "positive" in why
    assert representation["atoms"][0]["status"] == "REFUTED_ORDERED_SIGN"


def test_nonisolating_interval_is_inconclusive_not_authority():
    graph = _graph([
        _model(interval=("5", "6")),
        _claim(),
    ])
    verdict, why, representation = V.predicate_condition(graph, "P")
    assert verdict == V.UNVERIFIED
    assert "isolate exactly one real root" in why
    assert representation["atoms"][0] == {
        "relation": "POSITIVE", "expression": "w",
        "status": "ORDERED_SIGN_UNESTABLISHED", "cofactors": None,
    }


def test_ordered_degree_budget_fails_closed():
    graph = _graph([
        _model(generator="w^65-2", interval=("1", "2")),
        _claim(),
    ])
    verdict, why, representation = V.predicate_condition(graph, "P")
    assert verdict == V.UNVERIFIED
    assert "degree 65 exceeds" in why
    assert representation["atoms"][0]["cofactors"] is None


def test_ordered_receipt_replays_and_tampering_is_rejected():
    graph = _graph([_model(), _claim()])
    verdict, why, representation = V.predicate_condition(graph, "P")
    backend = cas.SingularBackend(binary_version="Singular replay-test")
    event = {
        "ev": "verdict", "id": "V", "subject": "condition", "of": "P",
        "verdict": verdict, "why": why, "representation": representation,
        **P.metadata(
            graph, "condition", "P", verdict=verdict,
            execution=backend.provenance(), representation=representation),
    }
    graph.apply(event, "ordered-v0.29", 99)
    assert graph.claims["P"]["condition_verdict"] == "VERIFIED"

    tampered_graph = _graph([_model(), _claim()])
    tampered = deepcopy(event)
    tampered["id"] = "V_BAD"
    tampered["representation"]["atoms"][0]["cofactors"]["sign"] = -1
    tampered.update(P.metadata(
        tampered_graph, "condition", "P", verdict=verdict,
        execution=backend.provenance(),
        representation=tampered["representation"]))
    with pytest.raises(S.GraphError, match="does not replay"):
        tampered_graph.apply(tampered, "ordered-v0.29", 99)


def test_incompatible_ordered_claims_create_visible_contradiction_debt():
    graph = _graph([
        _model(),
        _claim("P_POS", relation="POSITIVE", expression="w"),
        _claim("P_NONPOS", relation="NONPOSITIVE", expression="1*w"),
    ])
    findings = [finding for finding in C.run(graph)
                if finding.rule == C.R_CONDITION
                and "incompatible relations" in finding.detail]
    assert len(findings) == 1
    assert findings[0].severity == C.DEBT


def test_one_self_contradictory_conjunction_also_creates_debt():
    claim = _claim()
    claim["condition"]["all"].append({
        "relation": "NONPOSITIVE", "expression": "1*w"})
    graph = _graph([_model(), claim])
    findings = [finding for finding in C.run(graph)
                if "self-contradictory" in finding.detail]
    assert len(findings) == 1
    assert findings[0].subject == "P"


def test_real_closure_point_functor_mismatch_remains_structurally_refused():
    edge = {
        "ev": "edge", "id": "E", "src": "R", "dst": "A",
        "type": K.EQUIVALENCE, "map_kind": K.IDENTITY_MAP,
        "why": "same ring is not the same point functor", "ring_iso": True,
    }
    with pytest.raises(S.GraphError, match="different point functors"):
        _graph([
            _model("R"),
            _model("A", universe=S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE),
            edge,
        ])


def test_ordered_predicate_transports_only_with_selected_embedding_identity():
    same = deepcopy(_model("SAME"))
    identity = {
        "ev": "edge", "id": "E_SAME", "src": "M", "dst": "SAME",
        "type": K.EQUIVALENCE, "map_kind": K.IDENTITY_MAP,
        "why": "literal selected-root relabel", "ring_iso": True,
    }
    graph = _graph([_model(), same, identity, _claim()])
    assert C.probe(graph, "P", "E_SAME", K.ALONG).licensed

    plus = _model("PLUS", generator="w^2-2", interval=("1", "2"))
    minus = _model("MINUS", generator="w^2-2", interval=("-2", "-1"))
    conjugation = {
        "ev": "edge", "id": "E_SWAP", "src": "PLUS", "dst": "MINUS",
        "type": K.EQUIVALENCE, "map_kind": K.POLYNOMIAL,
        "why": "abstract field automorphism changes the selected root",
        "ring_iso": True, "forward": {"w": "-w"},
        "inverse": {"w": "-w"},
    }
    swapped = _graph([
        plus, minus, conjugation,
        _claim(model="PLUS", relation="POSITIVE"),
    ])
    ruling = C.probe(swapped, "P", "E_SWAP", K.ALONG)
    assert not ruling.licensed
    assert ruling.rule == "selected_embedding_identity"
