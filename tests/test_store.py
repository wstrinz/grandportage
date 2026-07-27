"""The fold, the merge, and the checks that make a malformed graph loud."""

import json
import os

import pytest

from grandportage import kernel as K
from grandportage import store as S

import helpers as H


MODEL_A = {"ev": "model", "id": "A", "desc": "a"}
MODEL_B = {"ev": "model", "id": "B", "desc": "b"}
EDGE_AB = {"ev": "edge", "id": "E", "src": "A", "dst": "B",
           "type": "NECESSARY_CONDITION", "why": "drops equations"}


def test_both_fixtures_fold():
    for d in H.DOMAINS:
        g = H.load(d)
        assert g.models and g.edges and g.claims


def test_counts_match_the_answer_key():
    for d in H.DOMAINS:
        g, exp = H.load(d), H.expected(d)
        assert {"models": len(g.models), "edges": len(g.edges),
                "claims": len(g.claims),
                "inferences": len(g.inference_order)} == exp["counts"], d


# -- merge semantics --------------------------------------------------------

def test_identical_redeclaration_is_idempotent():
    """Two branches that both declare a shared model merge silently.  Without
    this, every fan-out would need a hand-maintained list of who owns what."""
    g = H.fold([MODEL_A, MODEL_B, dict(MODEL_A), EDGE_AB])
    assert len(g.models) == 2


def test_conflicting_redeclaration_is_a_hard_error():
    """The whole safe-fan-out story is this test.  Merging twenty untyped agent
    branches is how you generate the error class this project shipped an
    erratum for; a merge must compose or fail, never blend."""
    with pytest.raises(S.GraphError) as exc:
        H.fold([MODEL_A, {"ev": "model", "id": "A", "desc": "SOMETHING ELSE"}])
    assert "conflicting redeclaration" in str(exc.value)


def test_merging_the_two_domains_is_just_concatenation():
    g = S.load(H.graph_file("jc2"), H.graph_file("matroid"))
    assert len(g.models) == 37
    assert "GERM" in g.models and "ML8_R" in g.models


def test_merge_order_does_not_change_the_result():
    a = S.load(H.graph_file("jc2"), H.graph_file("matroid"))
    b = S.load(H.graph_file("matroid"), H.graph_file("jc2"))
    assert set(a.models) == set(b.models)
    assert set(a.edges) == set(b.edges)
    assert sorted(a.inference_order) == sorted(b.inference_order)


# -- referential integrity --------------------------------------------------

def test_claim_in_an_undeclared_model_is_refused():
    with pytest.raises(S.GraphError):
        H.fold([MODEL_A, {"ev": "claim", "id": "C", "model": "NOPE",
                          "kind": "NONEMPTY", "witness_kind": "EXHIBITED", "statement": "x"}])


def test_disconnected_inference_path_is_refused():
    """Not in the prototype, and it matters: a path whose edges do not join is
    not a lossy inference, it is a nonexistent one.  Typing it would produce a
    confident verdict about a route nobody can walk."""
    events = [
        MODEL_A, MODEL_B, {"ev": "model", "id": "C", "desc": "c"},
        EDGE_AB,
        {"ev": "claim", "id": "CL", "model": "C", "kind": "NONEMPTY", "witness_kind": "EXHIBITED",
         "statement": "a point of C"},
        {"ev": "inference", "id": "I", "claim": "CL", "path": [["E", "ALONG"]],
         "asserted": "therefore a point of B"},
    ]
    with pytest.raises(S.GraphError) as exc:
        H.fold(events)
    assert "not connected" in str(exc.value)


def test_the_prototypes_fano_control_really_was_disconnected():
    """The port found this, and it is worth keeping as a regression.

    matroid_transfer.py routes IM-FANO-NO-SAT (a claim about the Fano ideal
    over Q) across M-E4, the NON-Fano saturation edge over F_2.  Re-introducing
    that route must fail the fold.
    """
    with pytest.raises(S.GraphError) as exc:
        H.mutate("matroid", _reroute_fano_over_the_nonfano_edge)
    assert "not connected" in str(exc.value)


def _reroute_fano_over_the_nonfano_edge(ev):
    if ev.get("ev") == "inference" and ev.get("id") == "IM-FANO-NO-SAT":
        ev["path"] = [["M-E4", "AGAINST"]]
    return ev


def test_inference_endpoints_are_derived_not_declared():
    for d in H.DOMAINS:
        g = H.load(d)
        for iid in g.inference_order:
            i = g.inferences[iid]
            assert i["concludes_at"] in g.models
            assert i["concludes_kind"] in K.CLAIM_KINDS


# -- events that must carry their justification -----------------------------

def test_untyped_edge_requires_a_stated_debt():
    """An UNTYPED edge is a recorded hole.  A hole with no reason is just a
    missing row again, which is what the type exists to prevent."""
    bad = dict(EDGE_AB, type="UNTYPED")
    with pytest.raises(S.GraphError):
        H.fold([MODEL_A, MODEL_B, bad])
    ok = dict(bad, debt_why="exploratory sweep; relation to the germ unknown")
    assert H.fold([MODEL_A, MODEL_B, ok]).edges["E"]["type"] == "UNTYPED"


def test_severity_override_requires_a_reason():
    events = [MODEL_A, MODEL_B, EDGE_AB,
              {"ev": "claim", "id": "CL", "model": "B", "kind": "NONEMPTY", "witness_kind": "EXHIBITED",
               "statement": "a point of B"},
              {"ev": "inference", "id": "I", "claim": "CL",
               "path": [["E", "AGAINST"]], "asserted": "a point of A",
               "severity_override": "TRIAGE"}]
    with pytest.raises(S.GraphError) as exc:
        H.fold(events)
    assert "severity_why" in str(exc.value)


def test_certificate_registration_requires_a_base_change_verdict_and_why():
    for bad in ({"ev": "certificate", "id": "X", "why": "..."},
                {"ev": "certificate", "id": "X", "base_changes": True}):
        with pytest.raises(S.GraphError):
            H.fold([bad])


def test_edge_requires_why():
    with pytest.raises(S.GraphError):
        H.fold([MODEL_A, MODEL_B,
                {"ev": "edge", "id": "E", "src": "A", "dst": "B",
                 "type": "NECESSARY_CONDITION"}])


def test_scope_error_surfaces_at_fold_time():
    events = [MODEL_A,
              {"ev": "claim", "id": "CL", "model": "A", "kind": "EMPTY",
               "statement": "empty", "certificate": "NONSQUARE_CLASS",
               "scope": "SCHEME"}]
    with pytest.raises(K.ScopeError):
        H.fold(events)


def test_domain_certificates_extend_the_registry_without_editing_the_kernel():
    g = H.load("matroid")
    assert g.certificates["FINITE_FIELD_EXHAUSTION"] is False
    assert g.certificates["PAPPUS_IDENTITY"] is True
    assert "FINITE_FIELD_EXHAUSTION" not in K.BUILTIN_CERTIFICATES


# -- round trip -------------------------------------------------------------

def test_append_refuses_to_write_a_log_it_cannot_fold(tmp_path):
    root = str(tmp_path)
    S.append([MODEL_A, MODEL_B], root=root)
    with pytest.raises(S.GraphError):
        S.append([{"ev": "claim", "id": "C", "model": "GHOST",
                   "kind": "EMPTY", "statement": "x",
                   "certificate": "UNIT_IDEAL_CERT"}], root=root)
    # the rejected write left nothing behind
    with open(S.graph_path(root), encoding="utf-8") as fh:
        assert "GHOST" not in fh.read()


def test_fold_is_deterministic():
    for d in H.DOMAINS:
        a, b = H.load(d), H.load(d)
        assert json.dumps(sorted(a.models), sort_keys=True) == \
            json.dumps(sorted(b.models), sort_keys=True)
        assert a.inference_order == b.inference_order


def test_comments_and_blank_lines_survive_the_reader():
    for d in H.DOMAINS:
        with open(H.graph_file(d), encoding="utf-8") as fh:
            assert fh.readline().startswith("#")
        assert H.load(d).models
