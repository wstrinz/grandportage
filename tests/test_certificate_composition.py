"""Interpretation, path composition, and receipt custody for one SOS fixture."""

from copy import deepcopy
import json
from pathlib import Path

import pytest

from grandportage import check as C
from grandportage import kernel as K
from grandportage import ordered_sos as SOS
from grandportage import store as S
from grandportage import verify as V
from scripts import check_interpreter_parity as parity


def model(mid, about, universe="BASE"):
    value = dict(parity.fixture()["model"], ev="model", id=mid,
                 about=about, point_universe=universe)
    if about == "F_2":
        value.update(compute_in="F_2", characteristic=2)
    return value


def edge(eid, src, dst, kind=K.BASE_EXTENSION):
    return {"ev": "edge", "id": eid, "src": src, "dst": dst,
            "type": kind, "map_kind": K.IDENTITY_MAP,
            "why": "exercise certificate interpretation along a composed route"}


def prepare(root):
    path = [["E-R", K.ALONG], ["E-QR", K.AGAINST]]
    events = [model("ALL", "ANY_ORDERED"), model("R", "R"), model("Q", "Q"),
              model("C", "C"), model("F2", "F_2"),
              edge("E-R", "ALL", "R"), edge("E-QR", "Q", "R"),
              edge("E-C", "Q", "C"),
              edge("E-F2", "Q", "F2", K.SPECIALIZATION),
              {"ev": "claim", "id": "EMPTY", "model": "ALL", "kind": K.EMPTY,
               "statement": "x^2+1 has no ordered-field zero",
               "certificate": "ORDERED_SOS_CERT", "scope": "ANY_ORDERED"},
              {"ev": "claim", "id": "POINT-P", "model": "R", "kind": K.PREDICATE,
               "statement": "every point satisfies the predicate x^2 >= 0"}]
    for target in ("Q", "C", "F2"):
        route = path if target == "Q" else path + [["E-" + target, K.ALONG]]
        events.append({"ev": "inference", "id": "TO-" + target,
                       "claim": "EMPTY", "path": route,
                       "asserted": "the emptiness result reaches " + target})
    S.append(events, str(root))
    return S.load(S.graph_path(str(root)))


def replay(root, certificate=None):
    results = V.verify_all(root=str(root), record=True,
                           supplied_certificates={"EMPTY": certificate or
                                                  parity.fixture()["certificate"]})
    graph = S.load(S.graph_path(str(root)))
    return graph, results


def test_declaration_then_replay_controls_the_whole_composed_path(tmp_path):
    before = prepare(tmp_path)
    assert not C.audit_inference(before, "TO-Q")[0]
    graph, results = replay(tmp_path)
    assert [(subject, oid, verdict) for subject, oid, verdict, _ in results
            if subject == "certificate"] == [
        ("certificate", "EMPTY", "VERIFIED")]
    allowed, trace = C.audit_inference(graph, "TO-Q")
    assert allowed
    assert [(eid, direction, ok) for eid, direction, ok, _ in trace] == [
        ("E-R", K.ALONG, True), ("E-QR", K.AGAINST, True)]
    assert graph.claims["EMPTY"]["certificate_reach"] == {"kind": "ORDERED"}
    # The same R -> Q step does not acquire a concrete point-transport licence.
    point_ruling = C.probe(graph, "POINT-P", "E-QR", K.AGAINST)
    assert not point_ruling.licensed
    assert point_ruling.rule == "field_context"


@pytest.mark.parametrize("target", ["C", "F2"])
def test_a_successful_prefix_does_not_license_an_invalid_interpretation(tmp_path, target):
    prepare(tmp_path)
    graph, _ = replay(tmp_path)
    allowed, trace = C.audit_inference(graph, "TO-" + target)
    assert not allowed
    assert [ok for _, _, ok, _ in trace] == [True, True, False]


def test_point_universe_change_is_refused_before_extending_a_valid_path(tmp_path):
    prepare(tmp_path)
    graph, _ = replay(tmp_path)
    assert C.audit_inference(graph, "TO-Q")[0]
    with pytest.raises(S.GraphError, match="different point functors"):
        S.append([model("RC", "R", "ALGEBRAIC_CLOSURE"),
                  edge("E-RC", "Q", "RC")], str(tmp_path))
    assert "RC" not in S.load(S.graph_path(str(tmp_path))).models


def test_a_rejected_certificate_never_opens_the_composed_path(tmp_path):
    prepare(tmp_path)
    bad = deepcopy(parity.fixture()["certificate"])
    bad["cofactors"] = ["1"]
    graph, results = replay(tmp_path, bad)
    assert [verdict for subject, oid, verdict, _ in results
            if subject == "certificate" and oid == "EMPTY"] == ["UNVERIFIED"]
    assert graph.claims["EMPTY"]["certificate_reach"] == {"kind": "NONE"}
    assert not C.audit_inference(graph, "TO-Q")[0]


def test_changed_model_cannot_reuse_an_old_receipt_for_a_composed_path(tmp_path):
    prepare(tmp_path)
    graph, _ = replay(tmp_path)
    assert C.audit_inference(graph, "TO-Q")[0]
    # Adversarially replay the history against a different model presentation.
    # The old receipt is retained; only its bound input is changed.
    events = [json.loads(line) for line in
              Path(S.graph_path(str(tmp_path))).read_text(encoding="utf-8").splitlines()
              if line.strip() and not line.lstrip().startswith("#")]
    for event in events:
        if event.get("ev") == "model" and event.get("id") == "ALL":
            event["generators"] = ["x^2+2"]
    changed = S.Graph().apply_all([(event, "changed-input", index)
                                   for index, event in enumerate(events, 1)]).validate()
    assert "certificate_reach" not in changed.claims["EMPTY"]
    assert not C.audit_inference(changed, "TO-Q")[0]


def test_interpreter_parity_binds_the_example_not_just_any_valid_certificate():
    payload = parity.fixture()["certificate"]
    assert parity.compare(payload)["squares"] == ["x"]
    different = deepcopy(payload)
    different["squares"] = ["-x"]
    assert SOS.verify(parity.fixture()["model"], different)
    with pytest.raises(ValueError, match="differs from the graph fixture"):
        parity.compare(different)
