"""CFG23 embedding-vocabulary v1.4, ported onto native GP contracts.

The accepted campaign checker remains design evidence.  These tests exercise
the GP fold, kernel gate, and provenance implementation independently: the
campaign script is not imported and its stored coverage manifest is not used
as an oracle.
"""

from copy import deepcopy

import pytest

from grandportage import check as C
from grandportage import format as F
from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S


def _model(mid, var, generator, embedding=None,
           point_universe=S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE):
    return {
        "ev": "model", "id": mid, "what": mid,
        "coefficient_domain": "Q", "characteristic": 0,
        "point_universe": point_universe,
        "ring_vars": [var], "generators": [generator],
        **({"embedding": embedding} if embedding is not ... else {}),
    }


def _real(var, lo, hi):
    return {"var": var, "kind": "REAL",
            "isolating_interval": {"lo": lo, "hi": hi}}


def _complex(var, re_lo, re_hi, im_lo, im_hi,
             verification="EXACT", conjugate_of=None):
    value = {
        "var": var, "kind": "COMPLEX",
        "isolating_box": {
            "re_lo": re_lo, "re_hi": re_hi,
            "im_lo": im_lo, "im_hi": im_hi,
        },
        "box_verification": verification,
    }
    if conjugate_of is not None:
        value["conjugate_of"] = conjugate_of
    return value


def _edge(eid, src, dst, map_kind=K.POLYNOMIAL,
          forward=None, inverse=None):
    event = {
        "ev": "edge", "id": eid, "src": src, "dst": dst,
        "type": K.EQUIVALENCE, "map_kind": map_kind,
        "why": "CFG23 selected-embedding replay", "ring_iso": True,
    }
    if forward is not None:
        event["forward"] = forward
        event["inverse"] = inverse
    return event


def _graph(events):
    graph = S.Graph()
    graph.apply_all([
        (event, "embedding-v1.4", index + 1)
        for index, event in enumerate([F.meta_event()] + events)
    ])
    return graph.validate()


W_PLUS = _real("w", "2", "3")
W_MINUS = _real("w", "-10", "-9")
QI_PLUS = _complex("x", "0", "0", "1", "1", conjugate_of="QI_MINUS")
QI_MINUS = _complex("x", "0", "0", "-1", "-1", conjugate_of="QI_PLUS")


def _fixture_22():
    return {
        "models": [
            _model("FIELD22_W_PLUS", "w", "w^2+7*w-26", W_PLUS),
            _model("FIELD22_W_MINUS", "w", "w^2+7*w-26", W_MINUS),
            _model("FIELD22_ABSTRACT", "w", "w^2+7*w-26", None),
            _model("FIELD22_W_PLUS_RELABEL", "w", "w^2+7*w-26", W_PLUS),
        ],
        "edges": [
            _edge("E_PLUS_MINUS_STRUCTURAL_REFUSAL", "FIELD22_W_PLUS",
                  "FIELD22_W_MINUS", K.IDENTITY_MAP,
                  {"w": "w"}, {"w": "w"}),
            _edge("E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM", "FIELD22_W_PLUS",
                  "FIELD22_W_MINUS", K.POLYNOMIAL,
                  {"w": "-7-w"}, {"w": "-7-w"}),
            _edge("E_PLUS_RELABEL_FULL_TRANSPORT", "FIELD22_W_PLUS",
                  "FIELD22_W_PLUS_RELABEL", K.IDENTITY_MAP,
                  {"w": "w"}, {"w": "w"}),
            _edge("E_ABSTRACT_TO_PLUS_FORGET", "FIELD22_ABSTRACT",
                  "FIELD22_W_PLUS", K.IDENTITY_MAP,
                  {"w": "w"}, {"w": "w"}),
        ],
    }


def _fixture_26():
    return {
        "models": [
            _model("FIELD26_CLOSURE", "z", "z^3+3*z^2-z-7", None),
            _model("FIELD26_REAL", "z", "z^3+3*z^2-z-7",
                   _real("z", "1", "2"), point_universe="REAL_CLOSURE"),
            _model("FIELD26_COMPLEX_A", "z", "z^3+3*z^2-z-7",
                   _complex("z", "-2.3", "-2.1", "0.4", "0.6",
                            "STRUCTURAL_ONLY", "FIELD26_COMPLEX_B")),
            _model("FIELD26_COMPLEX_B", "z", "z^3+3*z^2-z-7",
                   _complex("z", "-2.3", "-2.1", "-0.6", "-0.4",
                            "STRUCTURAL_ONLY", "FIELD26_COMPLEX_A")),
        ],
        "edges": [],
    }


def _fixture_qi():
    return {
        "models": [
            _model("QI_ABSTRACT", "x", "x^2+1", None),
            _model("QI_PLUS", "x", "x^2+1", QI_PLUS),
            _model("QI_MINUS", "x", "x^2+1", QI_MINUS),
        ],
        "edges": [
            _edge("E_QI_MISUSE_IDENTITY_MAP", "QI_PLUS", "QI_MINUS",
                  K.IDENTITY_MAP, {"x": "x"}, {"x": "x"}),
            _edge("E_QI_CONJUGATION_EQUIVALENCE", "QI_PLUS", "QI_MINUS",
                  K.POLYNOMIAL, {"x": "-x"}, {"x": "-x"}),
        ],
    }


def _fixture_translated():
    return {
        "models": [
            _model("TP_SRC", "w", "w^2-2", _real("w", "1", "2")),
            _model("TP_DST", "w", "w^2-2*w-1", _real("w", "2", "3")),
        ],
        "edges": [
            _edge("E_TRANSLATED_PRESENTATION_ISOMORPHISM", "TP_SRC", "TP_DST",
                  K.POLYNOMIAL, {"w": "w+1"}, {"w": "w-1"}),
        ],
    }


def _fixture_overlap():
    return {
        "models": [
            _model("OVERLAP_P1", "t", "t^2-5", _real("t", "2", "3")),
            _model("OVERLAP_P2", "t", "t^2-5", _real("t", "2.1", "2.3")),
            _model("OVERLAP_P3", "t", "t^2-5", _real("t", "-3", "2.1")),
        ],
        "edges": [],
    }


def _fixture_abstract():
    return {"models": [
        _model("FIELD22_RING_CONTROL", "w", "w^2+7*w-26", ...),
    ], "edges": []}


FIXTURES = {
    "22_4": _fixture_22,
    "26_4": _fixture_26,
    "qi": _fixture_qi,
    "translated_presentation": _fixture_translated,
    "overlap_policy": _fixture_overlap,
    "abstract_control": _fixture_abstract,
}


def _find(rows, identifier):
    return next(row for row in rows if row["id"] == identifier)


def _fixture_fingerprint(fixture):
    model_ids = [model["id"] for model in fixture["models"]]
    edge_ids = [edge["id"] for edge in fixture["edges"]]
    if len(model_ids) != len(set(model_ids)):
        raise S.GraphError("duplicate model id")
    if len(edge_ids) != len(set(edge_ids)):
        raise S.GraphError("duplicate edge id")
    return P.event_fingerprint({
        "models": [P.model_semantic_payload(model)
                   for model in fixture["models"]],
        "edges": [{
            key: edge.get(key) for key in
            ("id", "src", "dst", "type", "map_kind", "forward", "inverse")
        } for edge in fixture["edges"]],
    })


def test_all_six_rfc_fixtures_are_present_in_the_native_port():
    assert set(FIXTURES) == {
        "22_4", "26_4", "qi", "translated_presentation",
        "overlap_policy", "abstract_control",
    }


def test_embedding_schema_accepts_real_complex_null_and_omission():
    events = _fixture_22()["models"] + _fixture_qi()["models"]
    graph = _graph(events)
    assert S.declared_embedding(graph.models["FIELD22_ABSTRACT"]) is None
    assert S.declared_embedding(graph.models["QI_ABSTRACT"]) is None
    assert S.declared_embedding(
        _graph(_fixture_abstract()["models"]).models["FIELD22_RING_CONTROL"]
    ) is None


@pytest.mark.parametrize("embedding,match", [
    ({"var": "q", "kind": "REAL",
      "isolating_interval": {"lo": "1", "hi": "2"}}, "ring_vars"),
    ({"var": "w", "kind": "REAL",
      "isolating_interval": {"lo": "2", "hi": "1"}}, "lo < hi"),
    ({"var": "w", "kind": "COMPLEX",
      "isolating_box": {"re_lo": "0", "re_hi": "0",
                         "im_lo": "1", "im_hi": "1"}}, "box_verification"),
    ({"var": "w", "kind": "ORDERED",
      "isolating_interval": {"lo": "1", "hi": "2"}}, "REAL or COMPLEX"),
    ({"var": "w", "kind": "REAL",
      "isolating_interval": {"lo": "a", "hi": "2"}}, "exact rational"),
])
def test_embedding_schema_fails_closed(embedding, match):
    with pytest.raises(S.GraphError, match=match):
        _graph([_model("M", "w", "w^2-2", embedding)])


def test_identity_map_cannot_identify_different_selected_roots():
    fixture = _fixture_22()
    edge = _find(fixture["edges"], "E_PLUS_MINUS_STRUCTURAL_REFUSAL")
    with pytest.raises(S.GraphError, match="different serialized embeddings"):
        _graph(fixture["models"] + [edge])


def test_polynomial_automorphism_is_a_ring_map_not_selected_identity():
    fixture = _fixture_22()
    edge = _find(
        fixture["edges"], "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM")
    claim = {"ev": "claim", "id": "P", "model": "FIELD22_W_PLUS",
             "kind": K.PREDICATE, "statement": "w is positive"}
    graph = _graph(fixture["models"] + [edge, claim])
    ruling = C.probe(graph, "P", edge["id"], K.ALONG)
    assert not ruling.licensed
    assert ruling.rule == "selected_embedding_identity"


def test_exact_relabel_identity_retains_predicate_transport():
    fixture = _fixture_22()
    edge = _find(fixture["edges"], "E_PLUS_RELABEL_FULL_TRANSPORT")
    claim = {"ev": "claim", "id": "P", "model": "FIELD22_W_PLUS",
             "kind": K.PREDICATE, "statement": "w is positive"}
    graph = _graph(fixture["models"] + [edge, claim])
    assert C.probe(graph, "P", edge["id"], K.ALONG).licensed


def test_abstract_to_selected_forgetful_map_does_not_copy_predicate():
    fixture = _fixture_22()
    edge = _find(fixture["edges"], "E_ABSTRACT_TO_PLUS_FORGET")
    claim = {"ev": "claim", "id": "P", "model": "FIELD22_ABSTRACT",
             "kind": K.PREDICATE, "statement": "w is positive"}
    graph = _graph(fixture["models"] + [edge, claim])
    assert not C.probe(graph, "P", edge["id"], K.ALONG).licensed


def test_qi_conjugation_remains_a_polynomial_equivalence_not_identity():
    fixture = _fixture_qi()
    misuse = _find(fixture["edges"], "E_QI_MISUSE_IDENTITY_MAP")
    with pytest.raises(S.GraphError, match="different serialized embeddings"):
        _graph(fixture["models"] + [misuse])
    conjugation = _find(
        fixture["edges"], "E_QI_CONJUGATION_EQUIVALENCE")
    graph = _graph(fixture["models"] + [conjugation])
    assert graph.edges[conjugation["id"]]["forward"] == {"x": "-x"}


def test_26_real_closure_is_now_a_supported_selected_real_universe():
    real_model = _find(_fixture_26()["models"], "FIELD26_REAL")
    graph = _graph([real_model])
    assert (graph.models["FIELD26_REAL"]["point_universe"]
            == S.REAL_CLOSURE_POINT_UNIVERSE)


def test_endpoint_and_edge_fingerprints_bind_selected_payloads():
    fixture = _fixture_translated()
    graph = _graph(fixture["models"] + fixture["edges"])
    edge_id = "E_TRANSLATED_PRESENTATION_ISOMORPHISM"
    before = P.edge_endpoint_fingerprint(graph, edge_id)
    changed = _fixture_translated()
    _find(changed["models"], "TP_DST")["embedding"][
        "isolating_interval"]["hi"] = "4"
    changed_graph = _graph(changed["models"] + changed["edges"])
    assert P.endpoint_fingerprint(graph.models["TP_DST"]) != P.endpoint_fingerprint(
        changed_graph.models["TP_DST"])
    assert before != P.edge_endpoint_fingerprint(changed_graph, edge_id)
    assert P.input_fingerprint(graph, "ring_iso", edge_id) != P.input_fingerprint(
        changed_graph, "ring_iso", edge_id)


def test_conflicting_duplicate_ids_fail_before_overwrite_but_replay_is_idempotent():
    model = _model("M", "x", "x^2+1", QI_PLUS)
    graph = S.Graph()
    graph.apply(F.meta_event(), "dup", 1)
    graph.apply(model, "dup", 2)
    graph.apply(deepcopy(model), "dup", 3)
    changed = deepcopy(model)
    changed["embedding"] = QI_MINUS
    with pytest.raises(S.GraphError, match="conflicting redeclaration"):
        graph.apply(changed, "dup", 4)

    target = _model("N", "x", "x^2+1", QI_PLUS)
    edge = _edge("E", "M", "N", K.IDENTITY_MAP,
                 {"x": "x"}, {"x": "x"})
    edge_graph = S.Graph()
    edge_graph.apply(F.meta_event(), "dup-edge", 1)
    edge_graph.apply(model, "dup-edge", 2)
    edge_graph.apply(target, "dup-edge", 3)
    edge_graph.apply(edge, "dup-edge", 4)
    edge_graph.apply(deepcopy(edge), "dup-edge", 5)
    decoy = deepcopy(edge)
    decoy["map_kind"] = K.POLYNOMIAL
    decoy["forward"] = {"x": "-x"}
    decoy["inverse"] = {"x": "-x"}
    with pytest.raises(S.GraphError, match="conflicting redeclaration"):
        edge_graph.apply(decoy, "dup-edge", 6)


def _set_model(fixture, mid, field, value):
    _find(fixture["models"], mid)[field] = value


def _set_edge(fixture, eid, field, value):
    _find(fixture["edges"], eid)[field] = value


def _delete_edge(fixture, eid):
    fixture["edges"] = [edge for edge in fixture["edges"] if edge["id"] != eid]


def _rename_edge(fixture, eid, replacement):
    _find(fixture["edges"], eid)["id"] = replacement


def _mutate(name, operation):
    fixture = FIXTURES[name]()
    operation(fixture)
    return fixture


def _coherent_22_generator_swap(fixture):
    for model in fixture["models"]:
        if model["id"].startswith("FIELD22_"):
            model["generators"] = ["w^2+8*w-20"]


def _semantic_substitution(fixture, real_id, decoy_id):
    _rename_edge(fixture, real_id, real_id + "_RENAMED_AWAY")
    _rename_edge(fixture, decoy_id, real_id)


def _coherent_tp_root_swap(fixture):
    _find(fixture["models"], "TP_SRC")["embedding"] = _real("w", "-2", "-1")
    _find(fixture["models"], "TP_DST")["embedding"] = _real("w", "-1", "0")


def _coherent_tp_ideal_swap(fixture):
    _find(fixture["models"], "TP_SRC")["generators"] = ["w^2-3"]
    _find(fixture["models"], "TP_DST")["generators"] = ["w^2-2*w-2"]


def _duplicate_tp_models(fixture):
    for mid in ("TP_SRC", "TP_DST"):
        decoy = deepcopy(_find(fixture["models"], mid))
        decoy["generators"] = ["w^2-5"]
        fixture["models"].append(decoy)


MUTATIONS = [
    ("22_4", lambda f: _find(f["models"], "FIELD22_W_MINUS")["embedding"]["isolating_interval"].update(hi="-8")),
    ("22_4", lambda f: _find(f["models"], "FIELD22_W_MINUS")["embedding"]["isolating_interval"].update(lo="2", hi="3")),
    ("26_4", lambda f: _find(f["models"], "FIELD26_REAL")["embedding"]["isolating_interval"].update(lo="5", hi="6")),
    ("qi", lambda f: _find(f["models"], "QI_MINUS")["embedding"]["isolating_box"].update(im_lo="-2", im_hi="-2")),
    ("22_4", lambda f: _set_model(f, "FIELD22_W_PLUS", "generators", ["w^2+7*w-25"])),
    ("22_4", lambda f: _set_edge(f, "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM", "inverse", {"w": "w"})),
    ("22_4", _coherent_22_generator_swap),
    ("qi", lambda f: _set_edge(f, "E_QI_CONJUGATION_EQUIVALENCE", "forward", {"x": "x+1"})),
    ("overlap_policy", lambda f: _find(f["models"], "OVERLAP_P2")["embedding"]["isolating_interval"].update(lo="-3", hi="-2")),
    ("22_4", lambda f: _set_edge(f, "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM", "forward", {"q": "-7-q"})),
    ("22_4", lambda f: _delete_edge(f, "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM")),
    ("22_4", lambda f: _rename_edge(f, "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM", "E_RENAMED")),
    ("qi", lambda f: _delete_edge(f, "E_QI_CONJUGATION_EQUIVALENCE")),
    ("qi", lambda f: _rename_edge(f, "E_QI_CONJUGATION_EQUIVALENCE", "E_RENAMED")),
    ("translated_presentation", lambda f: _set_edge(f, "E_TRANSLATED_PRESENTATION_ISOMORPHISM", "forward", {"w": "w+2"})),
    ("translated_presentation", lambda f: _set_edge(f, "E_TRANSLATED_PRESENTATION_ISOMORPHISM", "inverse", {"w": "w+1"})),
    ("translated_presentation", lambda f: _delete_edge(f, "E_TRANSLATED_PRESENTATION_ISOMORPHISM")),
    ("translated_presentation", lambda f: _rename_edge(f, "E_TRANSLATED_PRESENTATION_ISOMORPHISM", "E_RENAMED")),
    ("22_4", lambda f: _semantic_substitution(f, "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM", "E_PLUS_RELABEL_FULL_TRANSPORT")),
    ("22_4", lambda f: _rename_edge(f, "E_PLUS_MINUS_STRUCTURAL_REFUSAL", "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM")),
    ("qi", lambda f: _semantic_substitution(f, "E_QI_CONJUGATION_EQUIVALENCE", "E_QI_MISUSE_IDENTITY_MAP")),
    ("qi", lambda f: _rename_edge(f, "E_QI_MISUSE_IDENTITY_MAP", "E_QI_CONJUGATION_EQUIVALENCE")),
    ("22_4", lambda f: _set_edge(f, "E_PLUS_MINUS_POLYNOMIAL_AUTOMORPHISM", "forward", {"w": "q+1"})),
    ("translated_presentation", _coherent_tp_root_swap),
    ("translated_presentation", _coherent_tp_ideal_swap),
    ("translated_presentation", _duplicate_tp_models),
]


@pytest.mark.parametrize("case,operation", MUTATIONS)
def test_all_26_rfc_mutations_change_custody_or_hit_duplicate_guard(case, operation):
    assert len(MUTATIONS) == 26
    baseline = FIXTURES[case]()
    expected = _fixture_fingerprint(baseline)
    mutated = _mutate(case, operation)
    try:
        observed = _fixture_fingerprint(mutated)
    except S.GraphError as exc:
        assert "duplicate" in str(exc)
    else:
        assert observed != expected
