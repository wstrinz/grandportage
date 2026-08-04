"""Adversarial checks for the gauge-aware source-target first-value handback."""

import copy
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT / "experiments" / "jc_h3_source_depth6" / "source_target_first_value_handback_adapter.py"
SPEC = importlib.util.spec_from_file_location("source_target_first_value", PATH)
ADAPTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ADAPTER)


@pytest.fixture
def handback():
    return ADAPTER.validate_handback_value(ADAPTER.load_fixture())


def by_id(report):
    return {item["id"]: item for item in report["items"]}


def test_parent_is_split_not_falsely_closed(handback):
    report = ADAPTER.build_report(handback)
    items = by_id(report)
    assert items[ADAPTER.PARENT]["effective_status"] == "RESOLVED_TO_PARTIAL_VALUE_AND_REMAINDER"
    assert items[ADAPTER.PARTIAL]["effective_status"] == "SIGMA_TOP_FACE_PARTIALLY_MATERIALIZED"
    assert items[ADAPTER.REMAINDER]["effective_status"] == "OPEN_REMAINING_COEFFICIENT_MAP"
    assert report["open_items"] == [ADAPTER.REMAINDER]
    assert report["source_authority_ceiling"] == "FORWARD_GAUGE_AWARE_COEFFICIENT_SEAM_ONLY"


@pytest.mark.parametrize("field", ["reverse_lift_licensed", "source_sufficiency_licensed",
                                    "pair_existence_licensed", "r5_licensed", "r7_licensed", "h3_licensed"])
def test_promotion_mutations_refuse(handback, field):
    value = copy.deepcopy(handback); value["seam"][field] = True
    with pytest.raises(ADAPTER.FirstValueHandbackError, match="was promoted"):
        ADAPTER.validate_handback_value(value)


def test_ratio_mutation_refuses(handback):
    value = copy.deepcopy(handback); value["seam"]["ratios"]["Q_(8,1)/p"] = "2"
    with pytest.raises(ADAPTER.FirstValueHandbackError, match="ratio data changed"):
        ADAPTER.validate_handback_value(value)


def test_native_bindings_match_current_sibling_checkout(handback):
    ADAPTER.check_native_bindings(handback)


def test_checked_review_receipt_regenerates_exactly(handback):
    expected = json.loads(ADAPTER.REVIEW_RECEIPT.read_text(encoding="utf-8"))
    assert expected == ADAPTER.review_receipt(ADAPTER.build_report(handback))
