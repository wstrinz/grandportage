"""Conditional JC original-pair to reduced E-system seam binding."""

import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

from grandportage import evidence as EV


ROOT = Path(__file__).parents[1]
ADAPTER_PATH = (ROOT / "experiments" / "jc_h3_source_depth6" /
                "original_pair_seam_adapter.py")
FIXTURE_PATH = (ROOT / "fixtures" / "jc_source_depth6" /
                "original_pair_to_esystem_v1.json")

_spec = importlib.util.spec_from_file_location(
    "jc_original_pair_seam_adapter", ADAPTER_PATH)
ADAPTER = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ADAPTER)


def _fixture():
    return json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))


def _repin(monkeypatch, tmp_path, fixture):
    raw = (json.dumps(
        fixture, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode(
            "utf-8")
    path = tmp_path / "mutated_original_pair_seam.json"
    path.write_bytes(raw)
    monkeypatch.setattr(
        ADAPTER, "EXPECTED_FIXTURE_SHA256", hashlib.sha256(raw).hexdigest())
    return path


def _stage(fixture, identifier):
    return next(stage for stage in fixture["manifest"]["stages"]
                if stage["id"] == identifier)


def test_conditional_seam_welds_native_rows_without_graph_authority():
    report = ADAPTER.verify_fixture()

    assert report["verdict"] == "VERIFIED_CONDITIONAL_ESYSTEM_SEAM"
    assert report["rows"] == 5
    assert report["strict_original_source_supported"] is False
    assert report["missing_stage"] == (
        "target_pair_to_normalized_laurent_root")
    envelope = report["evidence_envelope"]
    assert envelope["graph_effect"] == EV.GRAPH_EFFECT_NONE
    assert "native_row_commitments_welded_to_gp_exact_source_rows" in (
        envelope["licenses"])
    assert any("coefficient-level" in premise
               for premise in envelope["outstanding_premises"])
    assert all("H3" not in license for license in envelope["licenses"])


def test_current_native_seam_files_and_all_transitive_bindings_match():
    if not ADAPTER.NATIVE_ROOT.exists():
        pytest.skip("the sibling JC research checkout is not present")
    report = ADAPTER.verify_fixture(check_native_bindings=True)
    assert report["native_commit"] == ADAPTER.EXPECTED_NATIVE_COMMIT


def test_frozen_projection_rebuilds_from_the_landed_native_manifest():
    if not ADAPTER.NATIVE_ROOT.exists():
        pytest.skip("the sibling JC research checkout is not present")
    assert ADAPTER.build_fixture() == _fixture()


def test_promoting_the_missing_source_map_is_rejected(
        monkeypatch, tmp_path):
    fixture = _fixture()
    _stage(fixture, "target_pair_to_normalized_laurent_root").update(
        status="COMPLETE", implementation="invented.py")
    path = _repin(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.SeamAdapterError,
                       match="missing source map was promoted"):
        ADAPTER.verify_fixture(path)


def test_claiming_an_exact_serialized_pair_is_rejected(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["manifest"]["source_problem"]["exact_pair_serialized"] = True
    path = _repin(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.SeamAdapterError,
                       match="unmaterialized source pair was promoted"):
        ADAPTER.verify_fixture(path)


def test_promoting_strict_original_source_authority_is_rejected(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["manifest"]["authority"]["strict_original_source_supported"] = True
    path = _repin(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.SeamAdapterError,
                       match="strict original-source authority was promoted"):
        ADAPTER.verify_fixture(path)


def test_changed_native_row_commitment_breaks_the_gp_weld(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["manifest"]["reduced_rows"][0]["sha256"] = "0" * 64
    path = _repin(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.SeamAdapterError,
                       match="native reduced-row commitments changed"):
        ADAPTER.verify_fixture(path)


def test_moving_the_t_pin_into_row_derivation_is_rejected(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["manifest"]["normalized_root_contract"][
        "pin_semantics"]["part_of_reduced_row_derivation"] = True
    path = _repin(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.SeamAdapterError,
                       match="downstream pin semantics changed"):
        ADAPTER.verify_fixture(path)


def test_dropping_an_authority_refusal_is_rejected(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["manifest"]["authority"]["refusals"].remove("H3 promotion")
    path = _repin(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.SeamAdapterError,
                       match="required authority refusal was dropped"):
        ADAPTER.verify_fixture(path)


def test_changing_the_native_commit_binding_is_rejected(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["native_commit"] = "0" * 40
    path = _repin(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.SeamAdapterError,
                       match="native seam commit binding changed"):
        ADAPTER.verify_fixture(path)
