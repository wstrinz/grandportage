"""Native producer, exact replay, and a second interpreter on composed routes."""
import json
from pathlib import Path

import pytest

from grandportage import check as C
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


def prepare(root):
    events = []
    for mid, about, ch in [("Q", "Q", 0), ("R", "R", 0),
                           ("C", "C", 0), ("F2", "F_2", 2)]:
        events.append({"ev": "model", "id": mid, "about": about,
                       "compute_in": "F_2" if ch else "Q", "characteristic": ch,
                       "point_universe": "BASE", "ring_vars": ["x"],
                       "generators": ["x", "1-x"]})
    for eid, src, dst, kind in [("QR", "Q", "R", K.BASE_EXTENSION),
                                ("QC", "Q", "C", K.BASE_EXTENSION),
                                ("QF", "Q", "F2", K.SPECIALIZATION)]:
        events.append({"ev": "edge", "id": eid, "src": src, "dst": dst,
                       "type": kind, "map_kind": K.IDENTITY_MAP,
                       "why": "compare unit and ordered certificate interpreters"})
    events.append({"ev": "claim", "id": "U", "model": "Q", "kind": K.EMPTY,
                   "certificate": "UNIT_IDEAL_CERT", "statement": "x and 1-x cannot both vanish"})
    prefix = [["QR", K.ALONG], ["QR", K.AGAINST]]
    for target, final in [("C", "QC"), ("F2", "QF")]:
        events.append({"ev": "inference", "id": target, "claim": "U",
                       "path": prefix + [[final, K.ALONG]],
                       "asserted": "composed unit certificate emptiness"})
    S.append(events, str(root))
    return S.load(S.graph_path(str(root)))


@pytest.mark.live
def test_unit_interpreter_reuses_routes_but_has_different_reach(tmp_path):
    prepare(tmp_path)
    before = S.load(S.graph_path(str(tmp_path)))
    assert not C.audit_inference(before, "C")[0]
    V.verify_all(root=str(tmp_path), record=True)
    graph = S.load(S.graph_path(str(tmp_path)))
    assert graph.claims["U"]["certificate_reach"] == {"kind": "CHAR_0"}
    assert C.audit_inference(graph, "C")[0]
    ok, trace = C.audit_inference(graph, "F2")
    assert not ok
    assert [row[2] for row in trace] == [True, True, False]
    # Fresh arithmetic over F2 can succeed, but it cannot inherit Q's receipt.
    S.append([{"ev": "claim", "id": "UF", "model": "F2", "kind": K.EMPTY,
               "certificate": "UNIT_IDEAL_CERT", "statement": "fresh finite-field replay"}], str(tmp_path))
    V.verify_all(root=str(tmp_path), record=True)
    refreshed = S.load(S.graph_path(str(tmp_path)))
    assert refreshed.claims["UF"]["certificate_reach"] == {
        "kind": "FIELD_SPECIFIC", "field": "F_2"}
    assert not C.audit_inference(refreshed, "F2")[0]
    events = [json.loads(line) for line in Path(S.graph_path(str(tmp_path))).read_text(
        encoding="utf-8").splitlines() if line.strip() and not line.lstrip().startswith("#")]
    for event in events:
        if event.get("ev") == "model" and event.get("id") == "Q":
            event["generators"] = ["x", "-x"]
    changed = S.Graph().apply_all([(event, "mutated", i) for i, event in enumerate(events, 1)]).validate()
    assert "certificate_reach" not in changed.claims["U"]
    assert not C.audit_inference(changed, "C")[0]


def test_rational_cofactor_requirements_are_not_integer_identity_requirements():
    from grandportage import groebner as G
    assert G.check_membership_identity("1", ["x", "1-x"], ["1", "1"], ["x"], 2)
    assert G.check_membership_identity("1", ["2"], ["1/2"], ["x"], 0)
    with pytest.raises(G.CertificateError):
        G.check_membership_identity("1", ["2"], ["1/2"], ["x"], 2)
