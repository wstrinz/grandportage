"""Bounded graded extraction from reduced JC E-system rows to chain faces."""

import hashlib
import importlib.util
import json
from pathlib import Path

import pytest


pytestmark = pytest.mark.replay

from grandportage import evidence as EV


ROOT = Path(__file__).parents[1]
ADAPTER_PATH = (ROOT / "experiments" / "jc_h3_source_depth6" /
                "face_extraction_adapter.py")
FIXTURE_PATH = (ROOT / "fixtures" / "jc_source_depth6" /
                "graded_face_extraction_v1.json")

_spec = importlib.util.spec_from_file_location(
    "jc_source_depth6_face_extraction_adapter", ADAPTER_PATH)
ADAPTER = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ADAPTER)


def _fixture():
    return json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))


def _repin_mutation(monkeypatch, tmp_path, fixture):
    raw = (json.dumps(fixture, indent=2, sort_keys=True,
                      ensure_ascii=True) + "\n").encode("utf-8")
    path = tmp_path / "mutated_face_extraction.json"
    path.write_bytes(raw)
    monkeypatch.setattr(ADAPTER, "EXPECTED_FIXTURE_SHA256",
                        hashlib.sha256(raw).hexdigest())
    return path


def test_fast_face_extraction_welds_all_landed_faces_without_graph_effect():
    report = ADAPTER.verify_fixture()

    assert report["verdict"] == "VERIFIED_GRADED_FACE_EXTRACTION"
    assert report["source_rows"] == 5
    assert report["faces"] == 25
    assert report["sparse_products"] == 67868
    envelope = report["evidence_envelope"]
    assert envelope["graph_effect"] == EV.GRAPH_EFFECT_NONE
    assert "all_25_outputs_welded_to_landed_chain_faces" in envelope["licenses"]
    assert "selected_face_equations_are_necessary_under_declared_root_supports" in (
        envelope["licenses"])
    assert all("H3" not in license for license in envelope["licenses"])
    assert any("original polynomial-pair" in premise
               for premise in envelope["outstanding_premises"])


@pytest.mark.exhaustive
def test_full_source_formula_replay_rederives_all_five_rows():
    report = ADAPTER.verify_fixture(full_source_replay=True)

    assert report["verdict"] == (
        "VERIFIED_GRADED_FACE_EXTRACTION_WITH_SOURCE_REPLAY")
    assert "reduced_esystem_rows_rederived_from_defining_formula" in (
        report["evidence_envelope"]["licenses"])
    assert report["evidence_envelope"]["graph_effect"] == EV.GRAPH_EFFECT_NONE


def test_current_native_source_files_match_frozen_bindings():
    if not ADAPTER.NATIVE_ROOT.exists():
        pytest.skip("the sibling JC research checkout is not present")
    report = ADAPTER.verify_fixture(check_native_bindings=True)
    assert report["faces"] == 25


def test_source_row_coefficient_mutation_breaks_its_digest(monkeypatch, tmp_path):
    fixture = _fixture()
    term = fixture["source_rows"][0]["sparse"]["terms"][0]
    term[1] = str(ADAPTER.Q(term[1]) + 1)
    path = _repin_mutation(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.FaceExtractionError,
                       match="source row digest"):
        ADAPTER.verify_fixture(path)


def test_resigned_source_row_mutation_breaks_face_weld(monkeypatch, tmp_path):
    fixture = _fixture()
    record = fixture["source_rows"][0]
    term = record["sparse"]["terms"][0]
    term[1] = str(ADAPTER.Q(term[1]) + 1)
    record["sha256"] = ADAPTER.CHAIN._sparse_digest(record["sparse"])
    path = _repin_mutation(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.FaceExtractionError,
                       match="extracted face digest mismatch"):
        ADAPTER.verify_fixture(path)


def test_root_support_mutation_is_rejected_after_resigning(monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["root_supports"]["2"][0] += 1
    path = _repin_mutation(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.FaceExtractionError,
                       match="root-support table changed"):
        ADAPTER.verify_fixture(path)


def test_coordinate_series_mutation_is_rejected_after_resigning(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["coordinate_series"]["7"][0] = "c7_10"
    path = _repin_mutation(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.FaceExtractionError,
                       match="coordinate-series manifest changed"):
        ADAPTER.verify_fixture(path)


def test_formula_mutation_is_rejected_after_resigning(monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["formula"]["p_side_rows"] = 13
    path = _repin_mutation(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.FaceExtractionError,
                       match="formula manifest changed"):
        ADAPTER.verify_fixture(path)


def test_output_face_mutation_is_rejected_after_resigning(monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["output_faces"][0]["sha256"] = "0" * 64
    path = _repin_mutation(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.FaceExtractionError,
                       match="extracted face digest mismatch"):
        ADAPTER.verify_fixture(path)


def test_dropped_authority_refusal_is_rejected_after_resigning(
        monkeypatch, tmp_path):
    fixture = _fixture()
    fixture["refusals"].remove("H3 promotion")
    path = _repin_mutation(monkeypatch, tmp_path, fixture)

    with pytest.raises(ADAPTER.FaceExtractionError,
                       match="required authority refusal"):
        ADAPTER.verify_fixture(path)


def test_sparse_work_budget_fails_closed():
    source_rows = {
        record["row"]: ADAPTER.CHAIN._decode_sparse(
            record["sparse"], "test source row")
        for record in _fixture()["source_rows"]
    }
    original_budget = ADAPTER._Budget

    class ZeroBudget(original_budget):
        def __init__(self):
            super().__init__(max_products=0)

    ADAPTER._Budget = ZeroBudget
    try:
        with pytest.raises(ADAPTER.FaceExtractionError,
                           match="work budget exceeded"):
            ADAPTER._build_faces(source_rows)
    finally:
        ADAPTER._Budget = original_budget
