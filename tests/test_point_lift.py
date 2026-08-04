import copy
import json

import pytest

from grandportage import artifacts as A
from grandportage import backend as B
from grandportage import check as C
from grandportage import cli
from grandportage import format as F
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import mcp
from grandportage import store as S
from grandportage import verify as V


class _CuspMembershipBackend:
    """Deterministic membership search double; exact expansion stays real."""

    def membership(self, ring, expression, generators, **_kw):
        assert ring == ["y", "x"]
        table = {
            (("2*y^2-2*x^3",), "y^2-x^3"): ["1/2"],
            (("2*y^2-2*x^3",), "y^3-y*x^3"): ["1/2*y"],
            (("2*y^2-2*x^3", "x"), "-x"): ["0", "-1"],
            (("2*y^2-2*x^3", "x"), "y^2"): ["1/2", "x^2"],
        }
        cofactors = table.get((tuple(generators), expression))
        return {
            "is_member": cofactors is not None,
            "cofactors": cofactors,
            "reduced": "0" if cofactors is not None else expression,
        }


def _cusp_graph():
    return S.Graph().apply_all([
        (F.meta_event(), "test", 0),
        ({"ev": "model", "id": "SOURCE", "what": "cusp normalization",
          "characteristic": 0, "ring_vars": ["u", "y", "x"],
          "generators": ["u^2-x", "u^3-y"]}, "test", 0),
        ({"ev": "model", "id": "TARGET", "what": "cusp",
          "characteristic": 0, "ring_vars": ["y", "x"],
          "generators": ["2*y^2-2*x^3"], "eliminated": ["u"]},
         "test", 1),
        ({"ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
          "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
          "why": "eliminate u", "built_by_operation": "Eliminate"},
         "test", 2),
    ]).validate()


def _cusp_certificate():
    return {
        "charts": [{
            "guard": "x",
            "lift": {
                "u": {"numerator": "y", "denominator_power": 1},
            },
        }],
        "fallback": {"lift": {"u": "0"}},
    }


def test_guarded_rational_substitution_is_exact_and_cross_ring():
    images = {
        "u": {"numerator": "y", "denominator_power": 1},
        "y": {"numerator": "y", "denominator_power": 0},
        "x": {"numerator": "x", "denominator_power": 0},
    }
    assert G.guarded_rational_substitute(
        "u^2-x", ["u", "y", "x"], ["y", "x"], images, "x"
    ) == ("y^2-x^3", 2)
    assert G.guarded_rational_substitute(
        "u^3-y", ["u", "y", "x"], ["y", "x"], images, "x"
    ) == ("y^3-y*x^3", 3)
    assert G.check_membership_identity(
        "y^2", ["2*y^2-2*x^3", "x"], ["1/2", "x^2"],
        ["y", "x"],
    )["generator_count"] == 2


def test_piecewise_cusp_lift_earns_point_authority_without_exact_contraction():
    graph = _cusp_graph()
    verdict, why, representation = V.elimination_piecewise_lift(
        graph, "E", _cusp_certificate(), _backend=_CuspMembershipBackend()
    )

    assert verdict == V.POINT_LIFT_VERIFIED, why
    assert representation["method"] == "piecewise_rational_lift_v1"
    assert representation["charts"][0]["rows"][0]["cofactors"] == ["1/2"]
    assert representation["fallback"]["rows"][1]["vanishing_power"] == 2
    edge = graph.edges["E"]
    edge["output_verdict"] = V.OP_SOUND
    edge["point_lift_verdict"] = verdict
    assert C.effective_point_surjective(edge)
    assert C.effective_geometric_closure(edge)
    assert not C.effective_exact_contraction(edge)


def test_piecewise_lift_refuses_a_false_fallback():
    graph = _cusp_graph()
    bad = copy.deepcopy(_cusp_certificate())
    bad["fallback"]["lift"]["u"] = "1"

    verdict, why, representation = V.elimination_piecewise_lift(
        graph, "E", bad, _backend=_CuspMembershipBackend()
    )

    assert verdict == V.POINT_LIFT_REJECTED
    assert "fallback" in why
    assert representation is None


def test_piecewise_lift_refuses_hyperbola_fallback_at_missing_point():
    graph = S.Graph().apply_all([
        (F.meta_event(), "test", 0),
        ({"ev": "model", "id": "SOURCE", "what": "hyperbola",
          "characteristic": 0, "ring_vars": ["y", "x"],
          "generators": ["x*y-1"]}, "test", 1),
        ({"ev": "model", "id": "TARGET", "what": "closure line",
          "characteristic": 0, "ring_vars": ["x"], "generators": [],
          "eliminated": ["y"]}, "test", 2),
        ({"ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
          "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
          "why": "project the hyperbola", "built_by_operation": "Eliminate"},
         "test", 3),
    ]).validate()

    class Backend:
        def membership(self, _ring, expression, generators, **_kw):
            assert generators == ["x"]
            return {"is_member": False, "cofactors": None,
                    "reduced": expression}

    verdict, why, representation = V.elimination_piecewise_lift(
        graph, "E", {
            "charts": [{
                "guard": "x",
                "lift": {
                    "y": {"numerator": "1", "denominator_power": 1},
                },
            }],
            "fallback": {"lift": {"y": "0"}},
        }, _backend=Backend(),
    )

    assert verdict == V.POINT_LIFT_REJECTED
    assert "fallback" in why
    assert representation is None

def test_membership_certificate_rejects_wrong_cofactor():
    with pytest.raises(G.CertificateError, match="wrong polynomial"):
        G.check_membership_identity(
            "y^2-x^3", ["2*y^2-2*x^3"], ["1"], ["y", "x"]
        )


def test_point_lift_cli_passes_typed_certificate(tmp_path, monkeypatch, capsys):
    seen = {}

    def fake(root, edge, certificate, timeout, record):
        seen.update(root=root, edge=edge, certificate=certificate,
                    timeout=timeout, record=record)
        return V.POINT_LIFT_VERIFIED, "checked finite cover", {"charts": []}

    monkeypatch.setattr(V, "verify_elimination_point_lift", fake)
    certificate = _cusp_certificate()
    rc = cli.main([
        "--root", str(tmp_path), "verify-elimination-point-lift", "E",
        "--certificate", json.dumps(certificate), "--timeout", "23",
        "--dry-run",
    ])

    assert rc == 0
    assert "VERIFIED_POINT_LIFT" in capsys.readouterr().out
    assert seen == {
        "root": str(tmp_path), "edge": "E", "certificate": certificate,
        "timeout": 23, "record": False,
    }


def test_point_lift_mcp_surface_is_typed_and_dispatches(
        tmp_path, monkeypatch):
    root = str(tmp_path)
    S.append([{"ev": "model", "id": "M", "what": "placeholder"}], root)
    seen = {}

    def fake(root, edge, certificate, timeout, record):
        seen.update(root=root, edge=edge, certificate=certificate,
                    timeout=timeout, record=record)
        return V.POINT_LIFT_VERIFIED, "checked finite cover", {"charts": []}

    monkeypatch.setattr(V, "verify_elimination_point_lift", fake)
    certificate = _cusp_certificate()
    result = mcp.h_portage_verify_elimination_point_lift({
        "edge": "E", "certificate": certificate,
        "timeout": 29, "dry_run": True,
    }, root)

    assert not result.get("isError")
    assert "VERIFIED_POINT_LIFT" in result["content"][0]["text"]
    assert seen == {
        "root": root, "edge": "E", "certificate": certificate,
        "timeout": 29, "record": False,
    }
    tools = {tool["name"]: tool for tool in mcp.TOOLS}
    schema = tools["portage_verify_elimination_point_lift"]["inputSchema"]
    assert set(schema["required"]) == {"edge", "certificate"}
    assert schema["properties"]["certificate"]["type"] == "object"

def _execution():
    trace = [{
        "semantic_input_fingerprint": B.semantic_fingerprint("point_lift", []),
        "program_fingerprint": B.text_fingerprint("membership search"),
        "stdout_fingerprint": B.text_fingerprint("certificate"),
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
        "binary_version": "Singular 4.4.1",
        "executions": trace,
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", trace
        ),
    }


def test_point_lift_verdict_replays_exact_certificate_on_fold():
    graph = _cusp_graph()
    verdict, why, representation = V.elimination_piecewise_lift(
        graph, "E", _cusp_certificate(), _backend=_CuspMembershipBackend()
    )
    event = V._verdict_event(
        graph, "point_lift", "E", verdict, why, representation,
        execution=_execution(), verifier="verify.elimination_point_lift",
    )

    graph.apply(event, source="test", lineno=3)

    edge = graph.edges["E"]
    assert edge["point_lift_verdict"] == V.POINT_LIFT_VERIFIED
    assert edge["point_lift_representation"] == representation
    assert graph.verdicts[event["id"]]["current"] is True

    corrupted_graph = _cusp_graph()
    corrupted = copy.deepcopy(representation)
    corrupted["fallback"]["rows"][1]["cofactors"][0] = "1"
    forged = V._verdict_event(
        corrupted_graph, "point_lift", "E", verdict, why, corrupted,
        execution=_execution(), verifier="verify.elimination_point_lift",
    )
    with pytest.raises(S.GraphError, match="fails exact replay"):
        corrupted_graph.apply(forged, source="test", lineno=3)

@pytest.mark.live
def test_real_piecewise_lift_persists_and_unlocks_predicate_transport(tmp_path):
    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "SOURCE", "what": "cusp normalization",
         "characteristic": 0, "ring_vars": ["u", "y", "x"],
         "generators": ["u^2-x", "u^3-y"]},
        {"ev": "model", "id": "TARGET", "what": "cusp",
         "characteristic": 0, "ring_vars": ["y", "x"],
         "generators": ["2*y^2-2*x^3"], "eliminated": ["u"]},
        {"ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
         "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
         "why": "eliminate u", "built_by_operation": "Eliminate"},
    ], root)
    V.verify_all(root=root, timeout=120, record=True)
    verdict, why, representation = V.verify_elimination_point_lift(
        root, "E", _cusp_certificate(), timeout=120, record=True
    )

    assert verdict == V.POINT_LIFT_VERIFIED, why
    assert representation["fallback"]["rows"][1]["vanishing_power"] == 2
    S.append([
        {"ev": "claim", "id": "P", "model": "SOURCE",
         "kind": K.PREDICATE, "statement": "x is nonzero",
         "condition": {"all": [
             {"relation": "NONZERO", "expression": "x"},
         ]}},
        {"ev": "inference", "id": "I", "claim": "P",
         "path": [["E", K.ALONG]], "concludes_kind": K.PREDICATE,
         "asserted": "x is nonzero on the cusp target"},
    ], root)
    graph = S.load(S.graph_path(root))
    edge = graph.edges["E"]
    assert edge["output_verdict"] == V.OP_SOUND
    assert edge["point_lift_verdict"] == V.POINT_LIFT_VERIFIED
    assert C.effective_point_surjective(edge)
    assert not C.effective_exact_contraction(edge)
    licensed, trace = C.audit_inference(graph, "I")
    assert licensed
    assert "closedness is not required" in trace[0][3]
    assert A.audit_graph(root, graph) == []

@pytest.mark.live
def test_real_singular_checks_piecewise_cusp_point_lift():
    verdict, why, representation = V.elimination_piecewise_lift(
        _cusp_graph(), "E", _cusp_certificate(), timeout=120
    )

    assert verdict == V.POINT_LIFT_VERIFIED, why
    assert representation["charts"][0]["rows"][1]["cofactors"] == ["1/2*y"]
    assert representation["fallback"]["rows"][1]["cofactors"] == [
        "1/2", "x^2",
    ]