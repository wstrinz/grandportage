"""Standing independent-oracle and differential checker lane."""

import copy
import json
import os
from pathlib import Path
import random
import time

import pytest

from grandportage import cas
from grandportage import groebner as fast
from grandportage import reference_oracle as reference


CORPUS = Path(__file__).parent / "fixtures" / "reference_oracle" / \
    "corpus_v1.json"


def _cases():
    return json.loads(CORPUS.read_text(encoding="utf-8"))["cases"]


@pytest.mark.parametrize("case", _cases(), ids=lambda case: case["id"])
def test_retained_corpus_agrees_under_both_exact_engines(case):
    arguments = (
        case["target"], case["generators"], case["cofactors"],
        case["variables"], case["characteristic"],
    )
    assert fast.check_membership_identity(*arguments)[
        "reference_oracle"] == reference.REFERENCE_CHECKED
    assert reference.reduce_by_explicit_cofactors(
        *arguments) == reference.REFERENCE_CHECKED


@pytest.mark.parametrize("mutation", ["drop", "sign", "variable"])
def test_adversarial_certificate_mutations_are_refused_by_both_engines(
        mutation):
    case = copy.deepcopy(_cases()[0])
    if mutation == "drop":
        case["cofactors"].pop()
    elif mutation == "sign":
        case["cofactors"][0] = "-1"
    else:
        case["cofactors"][0] = "y"
    arguments = (
        case["target"], case["generators"], case["cofactors"],
        case["variables"], case["characteristic"],
    )
    with pytest.raises(fast.CertificateError):
        fast.check_membership_identity(*arguments)
    with pytest.raises(reference.ReferenceError):
        reference.reduce_by_explicit_cofactors(*arguments)


def test_oracle_substitution_is_simultaneous_and_sparse_round_trips():
    swapped = reference.substitute(
        "x-y", ["x", "y"], {"x": "y", "y": "x"})
    assert swapped == reference.parse("y-x", ["x", "y"])
    sparse = fast.encode_sparse_polynomial(
        fast.parse_polynomial("7/3*x^2*y-5", ["x", "y"]))
    assert reference.canonical_form(sparse, ["x", "y"]) == \
        reference.canonical_form("7/3*x^2*y-5", ["x", "y"])


def test_historical_sequential_substitution_bug_is_caught_when_reintroduced():
    expression = "x-y"
    historical = expression.replace("x", "y").replace("y", "x")
    anchored = reference.substitute(
        expression, ["x", "y"], {"x": "y", "y": "x"})
    assert reference.parse(historical, ["x", "y"]) != anchored
    assert anchored == reference.parse("y-x", ["x", "y"])


def test_reference_budget_declines_explicitly_and_fast_report_records_it():
    sparse = {"schema": "sparse_polynomial_v1", "terms": [
        {"coefficient": "1", "powers": [["x", exponent]]}
        for exponent in range(2100, 0, -1)
    ]}
    with pytest.raises(reference.ReferenceUnchecked):
        reference.parse(sparse, ["x"])
    report = fast.check_membership_identity(
        sparse, [sparse], ["1"], ["x"])
    assert report["reference_oracle"] == reference.REFERENCE_UNCHECKED


def test_inadmissible_denominator_is_refused_in_prime_characteristic():
    with pytest.raises(reference.ReferenceError, match="denominator"):
        reference.parse("x/3", ["x"], characteristic=3)
    with pytest.raises(fast.CertificateError):
        fast.parse_polynomial("x/3", ["x"], characteristic=3)


def test_seeded_small_exact_differential_lane():
    rng = random.Random(270027)
    for _ in range(200):
        variables = ["x", "y"]
        if rng.randrange(2):
            variables.reverse()
        characteristic = rng.choice([0, 2, 3, 5])
        a, b = rng.randint(-20, 20), rng.randint(-20, 20)
        exponent = rng.randint(0, 8)
        generator = "%d*%s^%d+%d" % (
            a, variables[0], exponent, b)
        cofactor = rng.choice(["1", "-1", variables[1], "2"])
        budget = fast._ArithmeticBudget()
        target = fast.render_polynomial(
            fast.parse_polynomial(
                generator, variables, characteristic, budget)
            * fast.parse_polynomial(
                cofactor, variables, characteristic, budget)
        )
        report = fast.check_membership_identity(
            target, [generator], [cofactor], variables, characteristic)
        assert report["reference_oracle"] == reference.REFERENCE_CHECKED


@pytest.mark.live
@pytest.mark.reference_fuzz
def test_seeded_live_differential_lane_uses_singular_as_untrusted_ground_truth():
    seconds = float(os.environ.get("GP_REFERENCE_FUZZ_SECONDS", "2"))
    rng = random.Random(270027)
    deadline = time.monotonic() + max(0.1, seconds)
    checked = 0
    while time.monotonic() < deadline:
        variables = rng.sample(["x", "y", "z"], 3)
        characteristic = rng.choice([0, 2, 3, 5])
        generator = "%d*%s^%d+%s" % (
            rng.randint(1, 12), variables[0], rng.randint(1, 6), variables[1])
        cofactor = rng.choice(["1", "-1", variables[2], "2"])
        budget = fast._ArithmeticBudget()
        target = fast.render_polynomial(
            fast.parse_polynomial(
                generator, variables, characteristic, budget)
            * fast.parse_polynomial(
                cofactor, variables, characteristic, budget)
        )
        assert fast.check_membership_identity(
            target, [generator], [cofactor], variables, characteristic)[
                "reference_oracle"] == reference.REFERENCE_CHECKED
        accepted, difference = cas.check_membership_representation(
            variables, target, [generator], [cofactor],
            characteristic=characteristic, timeout=60)
        assert accepted and difference == "0"
        checked += 1
    print("reference_fuzz_checked=%d seed=270027 seconds=%s" % (
        checked, seconds))
    assert checked > 0
