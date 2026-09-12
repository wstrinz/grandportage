"""Characterize the fold-time boundary from verdict history to authority.

These tests intentionally exercise the store before the v0.33 extraction.  They
freeze which current verdicts project computed authority fields, which current
negative proof-object verdicts remain history only, and the rule that stale
evidence projects nothing.
"""

import pytest

from grandportage import authority as A
from grandportage import provenance as P
from grandportage import store as S


PROJECTION_CASES = (
    ("claim", "VERIFIED_AMBIENT", "claims", "identity_verdict"),
    ("condition", "VERIFIED", "claims", "condition_verdict"),
    ("edge", "VERIFIED", "edges", "containment"),
    ("certificate", "VERIFIED", "claims", "certificate_verdict"),
    ("ring_iso", "VERIFIED", "edges", "ring_iso_verdict"),
    ("witness", "VERIFIED", "claims", "witness_verdict"),
    ("operation", "VERIFIED", "edges", "output_verdict"),
    ("partition", "VERIFIED", "partitions", "exhaustive_verdict"),
    ("elimination", "CERTIFICATE_REJECTED", "edges", None),
    ("point_lift", "POINT_LIFT_CERTIFICATE_REJECTED", "edges", None),
)


def _graph_with_target(collection):
    graph = S.Graph()
    getattr(graph, collection)["OBJECT"] = {}
    return graph


def _event(subject, verdict, representation=None):
    event = {
        "ev": "verdict",
        "id": "V",
        "subject": subject,
        "of": "OBJECT",
        "verdict": verdict,
        "why": "characterization",
        "input_fingerprint": "sha256:" + "0" * 64,
        "verifier": "characterization.verifier",
        "verifier_version": 1,
        "kernel_epoch": 11,
        "backend": "characterization execution provenance",
    }
    if representation is not None:
        event["representation"] = representation
    return event


@pytest.mark.parametrize(
    "subject,verdict,collection,projected_field", PROJECTION_CASES)
def test_current_verdict_projection_matrix(
        monkeypatch, subject, verdict, collection, projected_field):
    graph = _graph_with_target(collection)
    monkeypatch.setattr(
        P, "current_verdict",
        lambda *_args, **_kwargs: (True, "current"))
    event = _event(subject, verdict)

    graph._apply_verdict(event, "<characterization>")

    assert graph.verdicts["V"]["current"] is True
    assert graph.verdicts["V"]["stale_reason"] is None
    target = getattr(graph, collection)["OBJECT"]
    if projected_field is None:
        assert target == {}
        assert graph.authority_receipts == {}
    else:
        spec = graph._VERDICTS[subject]
        assert target == {
            projected_field: verdict,
            spec["why_field"]: "characterization",
        }
        receipt = graph.authority_receipts["V"]
        assert receipt.evidence.context.subject == subject
        assert receipt.evidence.context.object_id == "OBJECT"
        assert dict(receipt.projections) == target


@pytest.mark.parametrize(
    "subject,verdict,collection,_projected_field", PROJECTION_CASES)
def test_stale_verdicts_are_history_only(
        monkeypatch, subject, verdict, collection, _projected_field):
    graph = _graph_with_target(collection)
    monkeypatch.setattr(
        P, "current_verdict",
        lambda *_args, **_kwargs: (False, "characterized stale"))
    event = _event(subject, verdict)

    graph._apply_verdict(event, "<characterization>")

    assert graph.verdicts["V"]["current"] is False
    assert graph.verdicts["V"]["stale_reason"] == "characterized stale"
    assert getattr(graph, collection)["OBJECT"] == {}
    assert graph.authority_receipts == {}


def test_checked_evidence_and_receipts_cannot_be_caller_minted():
    with pytest.raises(TypeError):
        A.CheckedEvidence("V", "VERIFIED", "why", None, object())
    with pytest.raises(TypeError):
        A.AuthorityReceipt(None, (), object())


def test_binding_happens_only_after_subject_specific_replay(monkeypatch):
    graph = _graph_with_target("claims")
    monkeypatch.setattr(
        P, "current_verdict",
        lambda *_args, **_kwargs: (True, "current"))
    called = []
    original = A.bind

    def observed(*args, **kwargs):
        called.append(True)
        return original(*args, **kwargs)

    monkeypatch.setattr(A, "bind", observed)
    event = _event(
        "claim", "VERIFIED_DERIVED", representation={"not": "a proof"})

    with pytest.raises(S.GraphError, match="does not replay"):
        graph._apply_verdict(event, "<characterization>")

    assert called == []
    assert graph.claims["OBJECT"] == {}
    assert graph.authority_receipts == {}
