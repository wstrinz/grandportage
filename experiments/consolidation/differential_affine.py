"""Deterministic exact-polynomial differential assay.

Grand Portage's bounded parser and arithmetic remain authoritative. Singular is
used only as an untrusted disagreement oracle. The report is derived test data
and carries no graph authority.
"""

import argparse
import json
from pathlib import Path
import random

from grandportage import cas
from grandportage import groebner as G
from grandportage import kernel as K


SCHEMA = "grand-portage-differential-affine/v1"


def _random_terms(rng, variables, count):
    terms = []
    for _ in range(count):
        coefficient = rng.choice([-5, -3, -2, -1, 1, 2, 3, 5])
        powers = [rng.randrange(4) for _ in variables]
        if not any(powers):
            powers[rng.randrange(len(variables))] = 1
        factors = []
        for variable, power in zip(variables, powers):
            if power == 1:
                factors.append(variable)
            elif power:
                factors.append("%s^%d" % (variable, power))
        terms.append("(%d)*%s" % (coefficient, "*".join(factors)))
    return terms


def build_corpus(seed=19019):
    rng = random.Random(seed)
    variables = ["x", "y", "z"]
    normalizations = []
    for index, characteristic in enumerate((0, 5, 0, 7, 0, 5, 0, 7)):
        terms = _random_terms(rng, variables, 4 + index % 3)
        cancellation = "x*y^2"
        lhs = "+".join(terms + [cancellation, "-(%s)" % cancellation])
        rhs = "+".join(reversed(terms))
        normalizations.append({
            "id": "normalize-%02d" % index,
            "characteristic": characteristic,
            "ring_vars": list(reversed(variables)) if index % 2 else variables,
            "lhs": lhs,
            "rhs": rhs,
        })
    substitutions = [
        {
            "id": "swap",
            "characteristic": 0,
            "ring_vars": variables,
            "expression": "x^2*y-y*z+3*x",
            "images": {"x": "y", "y": "x", "z": "z+x"},
        },
        {
            "id": "affine-prime",
            "characteristic": 5,
            "ring_vars": variables,
            "expression": "3*x^2+2*y*z-z",
            "images": {"x": "x+y", "y": "z-1", "z": "x"},
        },
        {
            "id": "triangular",
            "characteristic": 0,
            "ring_vars": variables,
            "expression": "x*y*z+x-y+z",
            "images": {"x": "x-y", "y": "y+z", "z": "z+2"},
        },
    ]
    return {
        "seed": seed,
        "normalizations": normalizations,
        "substitutions": substitutions,
    }


def run_internal(corpus=None):
    corpus = corpus or build_corpus()
    normalization_rows = []
    for case in corpus["normalizations"]:
        left = G.canonical_polynomial(
            case["lhs"], case["ring_vars"], case["characteristic"])
        right = G.canonical_polynomial(
            case["rhs"], case["ring_vars"], case["characteristic"])
        parsed = G.parse_polynomial(
            left, case["ring_vars"], case["characteristic"])
        sparse = G.encode_sparse_polynomial(parsed)
        round_trip = G.canonical_polynomial_value(
            sparse, case["ring_vars"], case["characteristic"])
        normalization_rows.append({
            "id": case["id"],
            "equal": left == right,
            "sparse_round_trip": sparse == round_trip,
            "canonical": left,
        })
    substitution_rows = []
    for case in corpus["substitutions"]:
        result = G.substitute_polynomial(
            case["expression"], case["ring_vars"], case["images"],
            case["characteristic"])
        substitution_rows.append({"id": case["id"], "canonical": result})
    return {
        "normalizations": normalization_rows,
        "substitutions": substitution_rows,
    }


def run_live(corpus=None, backend=None):
    corpus = corpus or build_corpus()
    internal = run_internal(corpus)
    backend = backend or cas.SingularBackend()
    normalization_rows = []
    for case, checked in zip(corpus["normalizations"],
                             internal["normalizations"]):
        origin, evidence = backend.classify_identity(
            case["ring_vars"], case["lhs"], case["rhs"],
            characteristic=case["characteristic"], timeout=60)
        normalization_rows.append({
            "id": case["id"],
            "internal_equal": checked["equal"],
            "singular_origin": origin,
            "agree": checked["equal"] and origin == K.AMBIENT,
            "singular_difference": evidence["difference"],
        })
    substitution_rows = []
    for case, checked in zip(corpus["substitutions"],
                             internal["substitutions"]):
        got, _zero = backend.pullback_reduce(
            case["ring_vars"], case["expression"], case["images"],
            characteristic=case["characteristic"], timeout=60)
        singular = G.canonical_polynomial(
            got, case["ring_vars"], case["characteristic"])
        substitution_rows.append({
            "id": case["id"],
            "internal": checked["canonical"],
            "singular": singular,
            "agree": singular == checked["canonical"],
        })
    return {
        "schema": SCHEMA,
        "authority": "DERIVED_ASSAY_ONLY",
        "seed": corpus["seed"],
        "oracle": "Singular (untrusted disagreement oracle)",
        "normalizations": normalization_rows,
        "substitutions": substitution_rows,
        "all_agree": all(row["agree"] for row in
                         normalization_rows + substitution_rows),
    }


def report(live=False):
    corpus = build_corpus()
    if live:
        return run_live(corpus)
    internal = run_internal(corpus)
    return {
        "schema": SCHEMA,
        "authority": "DERIVED_ASSAY_ONLY",
        "seed": corpus["seed"],
        "oracle": None,
        "normalizations": internal["normalizations"],
        "substitutions": internal["substitutions"],
        "all_internal_checks_pass": (
            all(row["equal"] and row["sparse_round_trip"]
                for row in internal["normalizations"])
            and len(internal["substitutions"]) == len(corpus["substitutions"])
        ),
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--output")
    args = parser.parse_args(argv)
    payload = json.dumps(report(args.live), sort_keys=True, indent=2) + "\n"
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
