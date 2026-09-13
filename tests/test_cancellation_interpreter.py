"""Existing replay paths for the third interpreter; no new verifier."""
import pytest
from grandportage import format as F
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


def test_cancellation_sample_replays_but_nonzero_is_separate():
    assert G.check_membership_identity("2*x", ["2*x"], ["1"], ["x"], 0)
    assert G.check_membership_identity("x", ["2*x"], ["1/2"], ["x"], 0)
    with pytest.raises(G.CertificateError):
        G.check_membership_identity("x", ["2*x"], ["1/2"], ["x"], 2)


@pytest.mark.live
def test_native_identity_path_cancels_over_q_but_not_characteristic_two(tmp_path):
    for mid, ch, field in [("Q", 0, "Q"), ("F2", 2, "F_2")]:
        S.append([{"ev": "model", "id": mid, "about": field, "coefficient_domain": field,
                   "point_universe": "BASE", "characteristic": ch, "ring_vars": ["x"],
                   "generators": ["2*x"]},
                  {"ev": "claim", "id": "C-" + mid, "model": mid, "kind": K.IDENTITY,
                   "statement": "x vanishes by cancelling 2", "lhs": "x", "rhs": "0",
                   "ring_vars": ["x"], "identity_origin": K.DERIVED}], str(tmp_path))
    V.verify_all(root=str(tmp_path), record=True)
    graph = S.load(S.graph_path(str(tmp_path)))
    assert graph.claims["C-Q"]["identity_verdict"] == "VERIFIED_DERIVED"
    assert graph.claims["C-F2"]["identity_verdict"] != "VERIFIED_DERIVED"
