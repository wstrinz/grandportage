"""Focused adversarial checks for the current JC support-seam handback."""

import copy
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
PATH = (ROOT / "experiments" / "jc_h3_source_depth6" /
        "support_seam_handback_adapter.py")
SPEC = importlib.util.spec_from_file_location("support_handback", PATH)
ADAPTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ADAPTER)


@pytest.fixture
def handback():
    return ADAPTER.validate_handback_value(ADAPTER.load_fixture())


def by_id(report):
    return {item["id"]: item for item in report["items"]}


def discharge(identifier, premise, scope):
    return {
        "id": identifier,
        "premise_id": premise,
        "status": "DISCHARGED",
        "applies_to_scopes": [scope],
        "evidence": ["focused exact-scope test receipt"],
        "does_not_discharge": ["coefficient values", "source sufficiency"],
    }


def test_r7_prime_and_r6_are_premise_free_while_r7_stays_open(handback):
    report = ADAPTER.build_report(handback)
    items = by_id(report)

    assert items[ADAPTER.R7P]["effective_status"] == (
        "PROVED_NATIVE_UNCONDITIONAL")
    assert items[ADAPTER.R7P]["premises"] == []
    assert items[ADAPTER.R6]["effective_status"] == (
        "DISCHARGED_PREMISE_FREE_AS_CONSUMED")
    assert items[ADAPTER.R6]["premises"] == []
    assert ADAPTER.R7 in report["open_items"]
    assert ADAPTER.R7P not in report["open_items"]
    assert ADAPTER.R6 not in report["open_items"]
    assert items[ADAPTER.PARENT]["effective_status"] == "UNMATERIALIZED_OPEN"


def test_no_overlay_is_needed_for_r7_prime_or_r6(handback):
    overlay = discharge(
        "JC.H3.TEST.R7_PRIME.DISCHARGE", ADAPTER.R7P, ADAPTER.SCOPE_D6)
    report = ADAPTER.build_report(handback, [overlay])
    items = by_id(report)

    assert items[ADAPTER.R7P]["premise_updates"] == []
    assert items[ADAPTER.R6]["effective_status"] == (
        "DISCHARGED_PREMISE_FREE_AS_CONSUMED")
    assert items[ADAPTER.PARENT]["effective_status"] == "UNMATERIALIZED_OPEN"


def test_r7_overlay_does_not_control_r7_prime_or_r6(handback):
    overlay = discharge(
        "JC.H3.TEST.R7.DISCHARGE", ADAPTER.R7, ADAPTER.SCOPE_D6)
    report = ADAPTER.build_report(handback, [overlay])
    items = by_id(report)

    assert items[ADAPTER.R7P]["effective_status"] == (
        "PROVED_NATIVE_UNCONDITIONAL")
    assert items[ADAPTER.R6]["effective_status"] == (
        "DISCHARGED_PREMISE_FREE_AS_CONSUMED")
    assert items[ADAPTER.PARENT]["effective_status"] == "UNMATERIALIZED_OPEN"


def test_unrelated_overlay_cannot_promote_value_seam(handback):
    overlay = discharge(
        "JC.H3.TEST.WRONG_SCOPE", ADAPTER.R7P,
        "JC.H3.D6.UNRELATED_SCOPE")
    report = ADAPTER.build_report(handback, [overlay])

    assert by_id(report)[ADAPTER.R6]["effective_status"] == (
        "DISCHARGED_PREMISE_FREE_AS_CONSUMED")
    assert by_id(report)[ADAPTER.PARENT]["effective_status"] == (
        "UNMATERIALIZED_OPEN")


def test_reintroducing_r7_prime_as_an_r6_premise_refuses(handback):
    mutated = copy.deepcopy(handback)
    mutated["support_seam"]["r6_premises"] = [ADAPTER.R7P]

    with pytest.raises(ADAPTER.SupportHandbackError,
                       match="regained a ladder premise"):
        ADAPTER.validate_handback_value(mutated)


def test_generic_j_does_not_close_full_chart(handback):
    report = ADAPTER.build_report(handback)
    items = by_id(report)

    assert items[ADAPTER.GENERIC]["effective_status"] == "CLOSED"
    assert items[ADAPTER.GENERIC]["scope"]["id"] == ADAPTER.SCOPE_GENERIC_J
    assert items[ADAPTER.GENERIC]["exports_to_scopes"] == []
    assert items[ADAPTER.FULL]["effective_status"] == (
        "RESOLVED_TO_GENERIC_AND_FINITE_REMAINDER")
    assert items[ADAPTER.FULL]["replacement_ids"] == [
        ADAPTER.GENERIC, ADAPTER.EXCEPTIONAL]
    assert ADAPTER.EXCEPTIONAL in report["open_items"]
    assert ADAPTER.PARENT in report["open_items"]


def test_generic_to_all_fibres_mutation_refuses(handback):
    mutated = copy.deepcopy(handback)
    mutated["generic_j"]["all_fibers_licensed"] = True

    with pytest.raises(ADAPTER.SupportHandbackError,
                       match="all-fibre authority"):
        ADAPTER.validate_handback_value(mutated)


def test_exceptional_zero_to_source_witness_mutation_refuses(handback):
    mutated = copy.deepcopy(handback)
    mutated["generic_j"]["exceptional_fiber_semantics"] = (
        "SOURCE_WITNESS")
    mutated["generic_j"]["source_witness_licensed"] = True

    with pytest.raises(ADAPTER.SupportHandbackError,
                       match="exceptional zero"):
        ADAPTER.validate_handback_value(mutated)


def test_native_bindings_match_current_sibling_checkout(handback):
    ADAPTER.check_native_bindings(handback)


def test_checked_review_receipt_regenerates_exactly(handback):
    expected = json.loads(ADAPTER.REVIEW_RECEIPT.read_text(encoding="utf-8"))
    assert expected == ADAPTER.review_receipt(ADAPTER.build_report(handback))
