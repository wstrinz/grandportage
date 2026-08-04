"""Deterministic internal and live-oracle exact-polynomial attacks."""

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).parents[1]
ASSAY_PATH = (ROOT / "experiments" / "consolidation" /
              "differential_affine.py")
_spec = importlib.util.spec_from_file_location("differential_affine", ASSAY_PATH)
ASSAY = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ASSAY)


def test_differential_corpus_and_internal_round_trips_are_deterministic():
    first = ASSAY.build_corpus()
    second = ASSAY.build_corpus()
    report = ASSAY.report()

    assert first == second
    assert len(first["normalizations"]) == 8
    assert len(first["substitutions"]) == 3
    assert report["authority"] == "DERIVED_ASSAY_ONLY"
    assert report["all_internal_checks_pass"] is True


@pytest.mark.live
def test_real_singular_agrees_with_exact_checker_corpus():
    report = ASSAY.report(live=True)

    assert report["oracle"].startswith("Singular")
    assert report["all_agree"] is True
