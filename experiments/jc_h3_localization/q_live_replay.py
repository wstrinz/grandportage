#!/usr/bin/env python3
"""Replay one real JC q-window pivot through the isolated GP adapter.

The JC publication deliberately keeps the 12-step pivot block sparse and does
not serialize its large equation/substitution bodies.  This bridge imports the
producer read-only, reconstructs one exact sparse equation, and immediately
hands it to the narrow localization adapter.  It writes neither repository.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import importlib
import json
from pathlib import Path
import sys

from grandportage import groebner as G
import sympy as sp

import adapter


def gp_sparse(qmod, polynomial):
    variables = [qmod.name(index) for index in range(qmod.NVARS)]
    terms = {}
    for sparse_monomial, coefficient in polynomial.items():
        monomial = [0] * qmod.NVARS
        for index, exponent in sparse_monomial:
            monomial[index] = exponent
        terms[tuple(monomial)] = coefficient
    return G.encode_sparse_polynomial(G.Polynomial(variables, 0, terms))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--math-stuff",
        type=Path,
        default=Path(__file__).resolve().parents[3] / "math-stuff",
    )
    parser.add_argument("--row", type=int, default=1)
    parser.add_argument("--lift", type=int, default=11)
    args = parser.parse_args()

    producer_dir = (
        args.math_stuff.resolve() / "d2_plane_72_108"
    )
    sys.path.insert(0, str(producer_dir))
    if "--quiet" not in sys.argv:
        sys.argv.append("--quiet")
    qmod = importlib.import_module("f2_h3_q_window_elimination")

    key = (args.row, args.lift)
    candidates = [
        item for item in qmod.INVENTORY
        if item[0] == key and item[1] != qmod.P_IDX
    ]
    if len(candidates) != 1:
        raise RuntimeError(
            "expected one non-p q pivot at %r, found %d"
            % (key, len(candidates))
        )
    _key, variable, rest, rational = candidates[0]
    polynomial = qmod.EQS[key]
    equation = gp_sparse(qmod, polynomial)
    coefficient = sp.sstr(qmod.to_sympy(rest, rational))
    powers = {
        qmod.name(index): power
        for index, power in rest
    }
    inverse = Fraction(1, 1) / rational
    inverse_text = str(inverse)
    for guard, power in powers.items():
        inverse_text += "*%s^-%d" % (guard, power)

    envelope = {
        "schema": adapter.SCHEMA,
        "chart": "q",
        "model_digest": qmod.contract.model_digest(
            qmod.contract.CHARTS["q"]
        ),
        "characteristic": 0,
        "ring_vars": [qmod.name(index) for index in range(qmod.NVARS)],
        "current_generators": [equation],
        "guards": ["q", "t"],
        "equation_id": "E[%d,%d]" % key,
        "equation_polynomial": equation,
        "pivot": qmod.name(variable),
        "coefficient": coefficient,
        "unit_witness": {
            "coefficient": str(rational),
            "powers": powers,
            "inverse": inverse_text,
        },
        # The adapter derives the substitution from the checked equation.
        # This producer-native field is display-only and explicitly untrusted.
        "substitution": "sparse producer substitution (%d terms)" % len(
            qmod.solve_for(polynomial, variable, rest, rational)
        ),
    }
    report = adapter.translate(envelope)
    numerator = report["derived_substitution"]["numerator"]
    replay_summary = {
        "authority": report["authority"],
        "verdict": report["gp_report"]["verdict"],
        "denominator_powers": report[
            "derived_substitution"
        ]["denominator_powers"],
        "checked_numerator_terms": len(G.parse_polynomial(
            numerator, envelope["ring_vars"]
        ).terms),
        "source_fingerprint": report["source_fingerprint"],
    }
    print(json.dumps({
        "producer": {
            "equation": envelope["equation_id"],
            "equation_terms": len(polynomial),
            "equation_characters": len(json.dumps(equation)),
            "pivot": envelope["pivot"],
            "coefficient": coefficient,
            "substitution_terms": qmod.PIVOT_BLOCK[
                args.lift - 11
            ]["substitution_terms"],
        },
        "replay": replay_summary,
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
