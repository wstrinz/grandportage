"""Adversarial checks for the exact all-J c7_10 closeout handback."""

import copy
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
PATH = (ROOT / "experiments" / "jc_h3_source_depth6" /
        "c710_all_j_closeout_handback_adapter.py")
SPEC = importlib.util.spec_from_file_location("c710_all_j_closeout", PATH)
ADAPTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ADAPTER)


@pytest.fixture
def handback():
    return ADAPTER.validate_handback_value(ADAPTER.load_fixture())


def by_id(report):
    return {item["id"]: item for item in report["items"]}


def test_exact_all_j_closeout_replaces_only_finite_remainder(handback):
    report = ADAPTER.build_report(handback)
    items = by_id(report)

    assert report["open_items"] == []
    assert items[ADAPTER.ALL_J]["effective_status"] == "CLOSED"
    assert items[ADAPTER.EXCEPTIONAL]["effective_status"] == (
        "RESOLVED_BY_ALL_J_CLOSEOUT")
    assert items[ADAPTER.EXCEPTIONAL]["replacement_ids"] == [ADAPTER.ALL_J]
    assert report["source_authority_ceiling"] == (
        "ON_WALL_S2_C710_DIVISOR_SOURCE_FACE_EXCLUSION_ONLY")


@pytest.mark.parametrize("field", [
    "source_witness_licensed", "source_sufficiency_licensed",
    "global_b0_licensed", "sigma_kappa_nonzero_licensed",
])
def test_scope_promotion_mutations_refuse(handback, field):
    mutated = copy.deepcopy(handback)
    mutated["closeout"][field] = True

    with pytest.raises(ADAPTER.CloseoutHandbackError, match="was promoted"):
        ADAPTER.validate_handback_value(mutated)


def test_missing_all_j_license_refuses(handback):
    mutated = copy.deepcopy(handback)
    mutated["closeout"]["all_j_licensed"] = False

    with pytest.raises(ADAPTER.CloseoutHandbackError, match="all-J closeout"):
        ADAPTER.validate_handback_value(mutated)


def test_native_bindings_match_current_sibling_checkout(handback):
    ADAPTER.check_native_bindings(handback)


def test_checked_review_receipt_regenerates_exactly(handback):
    expected = json.loads(ADAPTER.REVIEW_RECEIPT.read_text(encoding="utf-8"))
    assert expected == ADAPTER.review_receipt(ADAPTER.build_report(handback))
