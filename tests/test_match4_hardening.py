"""Within-v0.32 diagnostics earned by the Match4 miniature and W1 runs."""
import json

import pytest

from grandportage import cas
from grandportage import cli
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V
from helpers import fold


def test_review_is_the_cold_reader_safe_full_history_surface(tmp_path, capsys):
    S.append([
        {"ev": "model", "id": "M", "what": "the only member"},
        {"ev": "family", "id": "F-OLD", "count": 1,
         "desc": "old census", "members": ["M"]},
        {"ev": "family", "id": "F-NEW", "count": 1,
         "desc": "new census", "members": ["M"], "supersedes": "F-OLD",
         "discharge_kind": K.RESTATE},
    ], str(tmp_path))

    assert cli.main(["--root", str(tmp_path), "review", "--json"]) == 1
    report = json.loads(capsys.readouterr().out)

    assert report["mode"] == "review"
    assert any(item["lifecycle"] == "HISTORICAL_SUPERSEDED"
               for item in report["findings"])


def test_review_text_names_its_full_historical_contract(tmp_path, capsys):
    S.append([{"ev": "model", "id": "M", "what": "a model"}], str(tmp_path))

    assert cli.main(["--root", str(tmp_path), "review"]) == 0
    text = capsys.readouterr().out

    assert text.startswith(
        "REVIEW: current authority debt plus historical/superseded findings.")


def test_verified_unit_anchor_makes_derived_identity_vacuity_loud():
    graph = fold([
        {"ev": "model", "id": "M", "what": "empty affine model",
         "characteristic": 0, "ring_vars": ["x"],
         "generators": ["x", "1-x"]},
        {"ev": "claim", "id": "EMPTY", "model": "M", "kind": K.EMPTY,
         "statement": "the anchor ideal is unit",
         "certificate": "UNIT_IDEAL_CERT"},
        {"ev": "claim", "id": "IDENTITY", "model": "M",
         "kind": K.IDENTITY, "statement": "x = 0", "lhs": "x", "rhs": "0",
         "ring_vars": ["x"], "identity_origin": K.DERIVED},
    ])
    graph.claims["EMPTY"]["certificate_verdict"] = V.CERT_VERIFIED

    class Backend:
        def classify_identity(self, *_args, **_kwargs):
            return K.DERIVED, {"reduced_modulo_ideal": "0"}

        def membership(self, *_args, **_kwargs):
            return {"is_member": True, "cofactors": ["1", "0"]}

        def check_membership(self, *_args, **_kwargs):
            return True, "0"

    verdict, why, _certificate = V.identity(
        graph, "IDENTITY", _backend=Backend())

    assert verdict == V.DERIVED
    assert "DEGENERATE_MODEL" in why
    assert "zero ring" in why
    assert "certified unit by EMPTY" in why
    assert "ambient-ring model" in why


def test_unverified_unit_label_does_not_claim_model_degeneracy():
    graph = fold([
        {"ev": "model", "id": "M", "what": "a model",
         "characteristic": 0, "ring_vars": ["x"], "generators": ["x"]},
        {"ev": "claim", "id": "EMPTY", "model": "M", "kind": K.EMPTY,
         "statement": "claimed empty", "certificate": "UNIT_IDEAL_CERT"},
        {"ev": "claim", "id": "IDENTITY", "model": "M",
         "kind": K.IDENTITY, "statement": "x = 0", "lhs": "x", "rhs": "0",
         "ring_vars": ["x"], "identity_origin": K.DERIVED},
    ])

    class Backend:
        def classify_identity(self, *_args, **_kwargs):
            return K.DERIVED, {"reduced_modulo_ideal": "0"}

        def membership(self, *_args, **_kwargs):
            return {"is_member": True, "cofactors": ["1"]}

        def check_membership(self, *_args, **_kwargs):
            return True, "0"

    verdict, why, _certificate = V.identity(
        graph, "IDENTITY", _backend=Backend())

    assert verdict == V.DERIVED
    assert "DEGENERATE_MODEL" not in why


def test_free_witness_parameter_refuses_before_crossing_cas_boundary():
    def runner(*_args):
        pytest.fail("a syntactically non-point witness reached the CAS")

    with pytest.raises(cas.CASError, match=r"undeclared symbol\(s\) t"):
        cas.check_witness(
            ["x", "y"], ["x", "y^2"], {"x": "0", "y": "t"},
            _runner=runner)
