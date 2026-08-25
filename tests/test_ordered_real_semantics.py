"""Unreleased v0.29 ordered-real contract and CFG23 replays."""

from copy import deepcopy

import pytest

from grandportage import cas
from grandportage import check as C
from grandportage import format as F
from grandportage import kernel as K
from grandportage import ordered_receipt as ORC
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
            == "selected_real_interval_v2")


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


@pytest.mark.parametrize("dimension,mutate", [
    ("value", lambda receipt: receipt["sturm_chain"][0].__setitem__(0, "999")),
    ("value", lambda receipt: receipt["root_interval"].__setitem__("hi", "100")),
    ("ordering", lambda receipt: receipt["variations"].__setitem__("lo", 99)),
    ("embedding", lambda receipt: receipt["embedding"]["isolating_interval"]
     .__setitem__("hi", "100")),
    ("embedding", lambda receipt: receipt["embedding"].__setitem__(
        "var", "not-the-model-variable")),
])
def test_independent_ordered_checker_rejects_arithmetic_mutations(
        dimension, mutate):
    graph = _graph([_model(), _claim()])
    _verdict, _why, representation = V.predicate_condition(graph, "P")
    receipt = deepcopy(representation["atoms"][0]["cofactors"])
    mutate(receipt)
    with pytest.raises(ORC.OrderedReceiptError, match="does not replay"):
        ORC.verify(graph.models["M"], "w", receipt)


def test_independent_ordered_checker_rejects_reordered_root_interval():
    """A dedicated `ordering` mutation: swap `root_interval`'s lo/hi without
    changing either value, on a model whose isolation genuinely refines to a
    nontrivial [lo, hi] (unlike `_model()`'s default, which isolates its root
    exactly at an endpoint and so has lo == hi -- a swap there is a no-op)."""
    model = _model("F26", var="z", generator="z^3+3*z^2-z-7",
                   interval=("1", "2"))
    claim = _claim(model="F26", relation="POSITIVE", expression="z")
    graph = _graph([model, claim])
    _verdict, _why, representation = V.predicate_condition(graph, "P")
    receipt = deepcopy(representation["atoms"][0]["cofactors"])
    assert receipt["root_interval"]["lo"] != receipt["root_interval"]["hi"]
    receipt["root_interval"].update(
        lo=receipt["root_interval"]["hi"], hi=receipt["root_interval"]["lo"])
    with pytest.raises(ORC.OrderedReceiptError, match="does not replay"):
        ORC.verify(graph.models["F26"], "z", receipt)


def test_ordered_receipt_survives_implementation_drift_check_when_unchanged(
        tmp_path):
    """Companion to the drift test below: an UNCHANGED native implementation
    must keep its verdict current across a reload, so the drift test below is
    known to be exercising drift and not merely "every reload goes stale"."""
    S.append([_model(), _claim()], str(tmp_path))
    V.verify_all(root=str(tmp_path),
                 backend=cas.SingularBackend(binary_version="unavailable:test"),
                 record=True)
    graph = S.load(S.graph_path(str(tmp_path)))
    event = next(iter(graph.verdicts.values()))
    assert P.native_provenance(event["backend"]) is not None
    current, reason = P.current_verdict(graph, event, check_binary_version=True)
    assert current is True, reason


def test_ordered_receipt_native_verdict_goes_stale_under_implementation_drift(
        tmp_path, monkeypatch):
    """A recorded selected_real_interval_v2 verdict's authority is bound to
    the exact kernel implementation that decided it -- not merely to its
    arithmetic content. Once the recorded `implementation_version` no longer
    matches the reading build's, `native_provenance`/`current_verdict` must
    stop treating it as current native authority, the same discipline that
    keeps a Singular verdict from surviving an undisclosed backend upgrade.
    This is drift in WHO decided it, distinct from every mutation above,
    which is drift in WHAT was decided.
    """
    S.append([_model(), _claim()], str(tmp_path))
    V.verify_all(root=str(tmp_path),
                 backend=cas.SingularBackend(binary_version="unavailable:test"),
                 record=True)
    graph = S.load(S.graph_path(str(tmp_path)))
    event = next(iter(graph.verdicts.values()))
    assert P.native_provenance(event["backend"]) is not None

    monkeypatch.setattr(P, "NATIVE_IMPLEMENTATION_VERSION",
                        P.NATIVE_IMPLEMENTATION_VERSION + 1)
    assert P.native_provenance(event["backend"]) is None, (
        "a drifted implementation_version must stop decoding as current "
        "native provenance")

    drifted_graph = S.load(S.graph_path(str(tmp_path)))
    drifted_event = next(iter(drifted_graph.verdicts.values()))
    assert drifted_event["current"] is False
    assert "execution provenance is absent or invalid" in (
        drifted_event["stale_reason"])
    # A stale verdict must not license the claim; drift revokes CURRENT
    # AUTHORITY entirely rather than merely downgrading it.
    assert drifted_graph.claims["P"].get("condition_verdict") != "VERIFIED"


def test_solver_free_ordered_verdict_records_without_singular(tmp_path):
    S.append([_model(), _claim()], str(tmp_path))
    unavailable = cas.SingularBackend(binary_version="unavailable:test")

    results = V.verify_all(
        root=str(tmp_path), backend=unavailable, record=True)

    assert [(subject, oid, verdict)
            for subject, oid, verdict, _why in results] == [
                ("condition", "P", V.CONDITION_VERIFIED)]
    graph = S.load(S.graph_path(str(tmp_path)))
    event = next(iter(graph.verdicts.values()))
    assert event["current"] is True
    assert P.native_provenance(event["backend"]) is not None
    assert graph.claims["P"]["condition_verdict"] == V.CONDITION_VERIFIED


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
