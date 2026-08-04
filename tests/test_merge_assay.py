"""Real two-log fan-out cases from the v0.19 consolidation assay."""

import importlib.util
from pathlib import Path


ROOT = Path(__file__).parents[1]
ASSAY_PATH = ROOT / "experiments" / "consolidation" / "merge_assay.py"
_spec = importlib.util.spec_from_file_location("merge_assay", ASSAY_PATH)
ASSAY = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ASSAY)


def test_real_fanout_merge_assay(tmp_path):
    report = ASSAY.run_assay(tmp_path)
    cases = report["cases"]

    assert report["authority"] == "DERIVED_ASSAY_ONLY"
    assert cases["same_object_different_ids"] == {
        "merge": "COMPOSES",
        "duplicate_affine_signatures": [["FIBER-A", "FIBER-B"]],
        "finding": "UNRESOLVED_ALIAS",
    }
    normalized = cases["same_id_equivalent_normalization"]
    assert normalized["merge"] == "REFUSES"
    assert normalized["exactly_equivalent"] is True
    assert normalized["conflict_fields"] == ["generators"]

    supersession = cases["superseded_object_consumed_elsewhere"]
    assert supersession["merge"] == "COMPOSES"
    assert [item["subject"] for item in supersession["stale_model_findings"]] == [
        "USES-OLD"]

    verdicts = cases["stale_and_current_verdicts"]
    assert verdicts["merge"] == "COMPOSES"
    assert verdicts["active_identity_verdict"] == "VERIFIED_DERIVED"
    assert sorted(value["current"] for value in verdicts["verdicts"].values()) \
        == [False, True]
