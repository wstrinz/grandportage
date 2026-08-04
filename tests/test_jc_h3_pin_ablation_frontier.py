import importlib.util
import json
import shutil
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_pin_ablation" / "frontier_adapter.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_pin_ablation_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _items(report):
    return {item["id"]: item for item in report["items"]}


def test_ranked_task_resolves_without_closing_b0_or_open_relaxations():
    report = _load().build()
    items = _items(report)

    assert items["JC.H3.C79.SOURCE.FACE81.PIN_ABLATION"]["effective_status"] == "RESOLVED_TO_SCOPED_RESULTS"
    assert items["JC.H3.C22.UNIFORM_SOURCE_EXCLUSION"]["effective_status"] == "CLOSED"
    assert "JC.H3.B0.SOURCE.EXCLUSION" in report["open_items"]
    assert "JC.H3.C21.RELAXATION" in report["open_items"]
    assert report["graph_effect"] == "NONE"


def test_joint_line_keeps_finite_remainder_and_transport_separate():
    report = _load().build()
    items = _items(report)

    assert items["JC.H3.C22_C710.JOINT_CONFINEMENT"]["frontier_state"] == "CLOSED"
    assert items["JC.H3.C22_C710.NORMALIZED_LINE.RESULTANT_ROOTS"]["frontier_state"] == "OPEN"
    assert items["JC.H3.C22_C710.NONNORMALIZED_TRANSPORT"]["frontier_state"] == "OPEN"
    assert "degree-130" in items["JC.H3.C22_C710.NORMALIZED_LINE.RESULTANT_ROOTS"]["proposition"]


def test_c21_failure_is_not_promoted_to_source_incidence():
    item = _items(_load().build())["JC.H3.C21.RELAXATION"]

    assert item["effective_status"] == "OPEN_EXPLICIT_CERTIFICATE_FAILURE"
    assert "not a source witness" in item["proposition"]
    assert "(-(15/2)*t,(15/2)*t^2)" in item["scope"]["description"]


def test_native_digest_mutation_refuses(tmp_path):
    module = _load()
    lane = tmp_path / module.LANE
    lane.mkdir(parents=True)
    for source in module.SOURCES:
        src = module.NATIVE_ROOT / source["path"]
        shutil.copyfile(src, tmp_path / source["path"])
    target = lane / "f2_h3_c22_exceptional_control_certificate.json"
    target.write_text(target.read_text(encoding="utf-8") + "\n", encoding="utf-8")

    with pytest.raises(module.PinAblationError, match="digest changed"):
        module.build(tmp_path)


def test_checked_review_receipt_regenerates_exactly():
    module = _load()
    expected = json.loads((ROOT / "review" /
                           "jc-h3-pin-ablation-frontier-v1.json").read_text(
                               encoding="utf-8"))

    assert expected == module.review_receipt(module.build())
