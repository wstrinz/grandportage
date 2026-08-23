import json

import pytest

from grandportage import check as C
from grandportage import cas
from grandportage import cli
from grandportage import format as F
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


def _current_graph(events):
    graph = S.Graph()
    graph.apply_all([
        (event, "fixture", index)
        for index, event in enumerate([F.meta_event()] + events, 1)
    ])
    return graph.validate()


def test_format4_is_readable_but_append_requires_audited_migration(tmp_path):
    path = tmp_path / "graph.jsonl"
    events = [
        {"ev": "meta", "graph_format": 4, "kernel_epoch": 10,
         "created_with": "grandportage/0.23.0"},
        {"ev": "model", "id": "M", "what": "historical model"},
    ]
    path.write_text("".join(
        json.dumps(event, sort_keys=True) + "\n" for event in events),
        encoding="utf-8")
    before = path.read_bytes()

    graph = S.load(str(path))
    assert graph.graph_format == 4
    assert graph.implementation is None
    assert graph.compatibility_mode is True

    with pytest.raises(S.GraphError, match="HISTORICAL NATIVE GRAPH") as exc:
        S.append([{"ev": "note", "id": "N", "text": "do not write"}],
                 graph=str(path))
    assert "migrate --to-current-kernel" in str(exc.value)
    assert path.read_bytes() == before


def test_explicit_graph_routes_verify_and_doctor(tmp_path, capsys):
    path = tmp_path / "selected.jsonl"
    path.write_text(json.dumps(F.meta_event(), sort_keys=True) + "\n",
                    encoding="utf-8")

    assert cli.main([
        "--root", str(tmp_path / "wrong-root"), "--graph", str(path),
        "verify", "--dry-run",
    ]) == 0
    assert "nothing to verify" in capsys.readouterr().out

    cli.main([
        "--root", str(tmp_path / "wrong-root"), "--graph", str(path),
        "doctor", "--json",
    ])
    report = json.loads(capsys.readouterr().out)
    assert report["graph"]["path"] == str(path.resolve())
    assert report["graph"]["header"]["graph_format"] == F.GRAPH_FORMAT


def test_evidence_decides_wrong_shape_is_a_graph_error_not_type_error():
    graph = S.Graph()
    graph.apply({"ev": "claim", "id": "C", "model": "M",
                 "kind": K.PREDICATE, "statement": "p"})
    with pytest.raises(S.GraphError, match="the values are BOTH"):
        graph.apply({
            "ev": "evidence", "id": "EV", "for": "C",
            "method": "ENUMERATION", "ran": True, "what": "counted",
            "decides": [],
        })


def test_ring_free_identity_restriction_is_rejected_in_current_format():
    with pytest.raises(S.GraphError, match="Missing algebraic metadata"):
        _current_graph([
            {"ev": "model", "id": "A", "what": "combinatorial A"},
            {"ev": "model", "id": "B", "what": "combinatorial B"},
            {"ev": "edge", "id": "E", "src": "A", "dst": "B",
             "type": K.RESTRICTION, "map_kind": K.IDENTITY_MAP,
             "why": "incorrect algebraic transport"},
        ])


class _ExactGeneratorBackend:
    def membership(self, ring_vars, target, generators, characteristic=0,
                   timeout=300):
        target = G.canonical_polynomial(target, ring_vars, characteristic)
        known = {
            G.canonical_polynomial(value, ring_vars, characteristic)
            for value in generators
        }
        return {
            "is_member": target == "0" or target in known,
            "cofactors": None,
            "reduced": "0" if target == "0" or target in known else target,
        }


def _cross_ring_graph(target_generator="y^2-2"):
    return _current_graph([
        {"ev": "model", "id": "X", "what": "source",
         "characteristic": 0, "ring_vars": ["x"],
         "generators": ["x^2-2"]},
        {"ev": "model", "id": "Y", "what": "target",
         "characteristic": 0, "ring_vars": ["y"],
         "generators": [target_generator]},
        {"ev": "edge", "id": "E", "src": "X", "dst": "Y",
         "type": K.EQUIVALENCE, "map_kind": K.POLYNOMIAL,
         "why": "rename the generator", "ring_iso": True,
         "forward": {"x": "y"}, "inverse": {"y": "x"},
         "converse_witness": "the displayed inverse"},
    ])


def test_cross_ring_variable_rename_verifies():
    verdict, why = V.ring_iso(
        _cross_ring_graph(), "E", _backend=_ExactGeneratorBackend())
    assert verdict == V.ISO_VERIFIED, why
    assert "differently named coordinate rings" in why


def test_cross_ring_wrong_target_is_refuted_not_shape_refused():
    verdict, why = V.ring_iso(
        _cross_ring_graph("y^2-3"), "E", _backend=_ExactGeneratorBackend())
    assert verdict == V.ISO_NOT_ISO
    assert "not a coordinate-ring homomorphism" in why


def test_cross_ring_condition_rewrite_uses_generator_image_orientation():
    graph = _cross_ring_graph()
    graph.edges["E"]["ring_iso_verdict"] = V.ISO_VERIFIED

    along, along_why = C.rewrite_condition_across_equivalence(
        graph,
        {"all": [{"relation": "NONZERO", "expression": "x+1"}]},
        graph.edges["E"], K.ALONG)
    against, against_why = C.rewrite_condition_across_equivalence(
        graph,
        {"all": [{"relation": "ZERO", "expression": "y-1"}]},
        graph.edges["E"], K.AGAINST)

    assert along == {
        "all": [{"relation": "NONZERO", "expression": "y+1"}]}
    assert against == {
        "all": [{"relation": "ZERO", "expression": "x-1"}]}
    assert "forward source-image" in along_why
    assert "inverse source-image" in against_why


def test_cross_ring_rational_map_reaches_localization_boundary():
    graph = _current_graph([
        {"ev": "model", "id": "P", "what": "paper",
         "characteristic": 0, "ring_vars": ["a1", "a2"],
         "generators": ["a1*a2-1"]},
        {"ev": "model", "id": "D", "what": "database",
         "characteristic": 0, "ring_vars": ["u", "a6", "a9"],
         "generators": ["u*a6+1", "a6*a9-1"]},
        {"ev": "edge", "id": "E", "src": "P", "dst": "D",
         "type": K.EQUIVALENCE, "map_kind": K.RATIONAL,
         "why": "localized presentation", "ring_iso": True,
         "forward": {"a1": "a6", "a2": "a9"},
         "inverse": {"u": "-1/a1", "a6": "a1", "a9": "a2"},
         "converse_witness": "inverse after localizing at a1"},
    ])
    verdict, why = V.ring_iso(graph, "E", _backend=_ExactGeneratorBackend())
    assert verdict == V.UNVERIFIED
    assert "localization certificate" in why
    assert "variable-name shape refusal" in why


class _ConditionBackend:
    def membership(self, ring_vars, target, generators, characteristic=0,
                   timeout=300):
        target = G.canonical_polynomial(target, ring_vars, characteristic)
        generators = [
            G.canonical_polynomial(value, ring_vars, characteristic)
            for value in generators
        ]
        member = target in generators or target == "0"
        return {"is_member": member,
                "cofactors": ["1" if value == target else "0"
                              for value in generators] if member else None,
                "reduced": "0" if member else target}

    def check_membership(self, *args, **kwargs):
        return True, "0"

    def unit_ideal(self, ring_vars, generators, characteristic=0, timeout=300):
        return {"is_unit": True, "cofactors": ["0"] * len(generators),
                "basis": ["1"]}

    def check_unit_ideal(self, *args, **kwargs):
        return True, "1"


def test_structured_predicate_is_reported_then_verified():
    graph = _current_graph([
        {"ev": "model", "id": "M", "what": "slice",
         "characteristic": 0, "ring_vars": ["x"],
         "generators": ["x^2+1"]},
        {"ev": "claim", "id": "C", "model": "M",
         "kind": K.PREDICATE, "statement": "one zero and one nonzero minor",
         "condition": {"all": [
             {"relation": "ZERO", "expression": "x^2+1"},
             {"relation": "NONZERO", "expression": "x-1"},
         ]}},
    ])
    findings = [finding for finding in C.run(graph)
                if finding.rule == C.R_CONDITION]
    assert len(findings) == 1
    assert "nothing has checked" in findings[0].detail

    verdict, why, representation = V.predicate_condition(
        graph, "C", _backend=_ConditionBackend())
    assert verdict == V.CONDITION_VERIFIED, why
    assert [row["status"] for row in representation["atoms"]] == [
        "VERIFIED_IDEAL_MEMBERSHIP", "VERIFIED_NOWHERE_ZERO"]

    graph.claims["C"]["condition_verdict"] = verdict
    graph.claims["C"]["condition_why"] = why
    assert not [finding for finding in C.run(graph)
                if finding.rule == C.R_CONDITION]


@pytest.mark.live
def test_cross_ring_variable_rename_against_real_singular():
    verdict, why = V.ring_iso(
        _cross_ring_graph(), "E", _backend=cas.SingularBackend(), timeout=120)
    assert verdict == V.ISO_VERIFIED, why


@pytest.mark.live
@pytest.mark.parametrize("target_var,generator", [
    ("a11", "a11^2+1"),
    ("a8", "a8^2-a8-1"),
    ("a5", "2*a5^2-2*a5+1"),
    ("a5", "2*a5^2+2*a5+1"),
])
def test_m13_literal_renames_against_real_singular(target_var, generator):
    paper_generator = generator.replace(target_var, "a")
    graph = _current_graph([
        {"ev": "model", "id": "P", "what": "paper",
         "characteristic": 0, "ring_vars": ["a"],
         "generators": [paper_generator]},
        {"ev": "model", "id": "D", "what": "database",
         "characteristic": 0, "ring_vars": [target_var],
         "generators": [generator]},
        {"ev": "edge", "id": "E", "src": "P", "dst": "D",
         "type": K.EQUIVALENCE, "map_kind": K.POLYNOMIAL,
         "why": "M13 presentation rename", "ring_iso": True,
         "forward": {"a": target_var},
         "inverse": {target_var: "a"},
         "converse_witness": "literal inverse rename"},
    ])
    verdict, why = V.ring_iso(
        graph, "E", _backend=cas.SingularBackend(), timeout=120)
    assert verdict == V.ISO_VERIFIED, why


@pytest.mark.live
@pytest.mark.parametrize("ring_vars,generators,zero,nonzero", [
    (["a2", "a6", "a9"],
     ["a2*a9+a9^2-2*a9+1", "a2*a6+1",
      "a6*a9^2-2*a6*a9+a6-a9"],
     "a6*a9^2-2*a6*a9+a6-a9", "a6*a9-a6+a9"),
    (["a11"], ["a11^2+1"], "-a11^2-1", "-a11+1"),
    (["a8"], ["a8^2-a8-1"], "-a8^2+a8+1", "-a8"),
    (["a5"], ["2*a5^2-2*a5+1"], "2*a5^2-2*a5+1", "2*a5"),
    (["a5"], ["2*a5^2+2*a5+1"], "2*a5^2+2*a5+1", "-a5"),
])
def test_m13_structured_predicates_against_real_singular(
        ring_vars, generators, zero, nonzero):
    graph = _current_graph([
        {"ev": "model", "id": "M", "what": "slice",
         "characteristic": 0, "ring_vars": ring_vars,
         "generators": generators},
        {"ev": "claim", "id": "C", "model": "M",
         "kind": K.PREDICATE, "statement": "checked atoms",
         "condition": {"all": [
             {"relation": "ZERO", "expression": zero},
             {"relation": "NONZERO", "expression": nonzero},
         ]}},
    ])
    verdict, why, representation = V.predicate_condition(
        graph, "C", _backend=cas.SingularBackend(), timeout=120)
    assert verdict == V.CONDITION_VERIFIED, why
    assert len(representation["atoms"]) == 2


@pytest.mark.live
def test_verify_reload_check_consumes_structured_condition(tmp_path):
    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "M", "what": "M13^2 slice",
         "characteristic": 0, "ring_vars": ["a11"],
         "generators": ["a11^2+1"]},
        {"ev": "claim", "id": "C", "model": "M",
         "kind": K.PREDICATE, "statement": "two checked minors",
         "condition": {"all": [
             {"relation": "ZERO", "expression": "-a11^2-1"},
             {"relation": "NONZERO", "expression": "-a11+1"},
         ]}},
    ], root)
    results = V.verify_all(root=root, timeout=120, record=True)
    assert [(subject, oid, verdict)
            for subject, oid, verdict, _why in results] == [
                ("condition", "C", V.CONDITION_VERIFIED)]
    reloaded = S.load(S.graph_path(root))
    assert reloaded.claims["C"]["condition_verdict"] == V.CONDITION_VERIFIED
    assert not [finding for finding in C.run(reloaded)
                if finding.rule == C.R_CONDITION]
