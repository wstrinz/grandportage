#!/usr/bin/env python3
"""Replay all 12 JC q-window pivots once, without dense substitution."""

from __future__ import annotations

import argparse
from fractions import Fraction
import importlib
import json
from pathlib import Path
import sys

import sympy as sp

import adapter
from grandportage import groebner as G


def gp_sparse(qmod, polynomial):
    variables = [qmod.name(index) for index in range(qmod.NVARS)]
    terms = {}
    for sparse_monomial, coefficient in polynomial.items():
        monomial = [0] * qmod.NVARS
        for index, exponent in sparse_monomial:
            monomial[index] = exponent
        terms[tuple(monomial)] = coefficient
    return G.encode_sparse_polynomial(G.Polynomial(variables, 0, terms))


def replay(qmod, key, variable, rest, rational):
    polynomial = qmod.EQS[key]
    equation = gp_sparse(qmod, polynomial)
    coefficient = sp.sstr(qmod.to_sympy(rest, rational))
    powers = {qmod.name(index): power for index, power in rest}
    inverse = Fraction(1, 1) / rational
    inverse_text = str(inverse) + "".join(
        "*%s^-%d" % (guard, power) for guard, power in powers.items()
    )
    substitution = qmod.solve_for(polynomial, variable, rest, rational)
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
        "substitution": "sparse producer substitution (%d terms)"
                        % len(substitution),
    }
    report = adapter.translate(envelope)
    numerator = report["derived_substitution"]["numerator"]
    numerator_terms = len(G.parse_polynomial(
        numerator, envelope["ring_vars"]
    ).terms)
    return {
        "equation": envelope["equation_id"],
        "pivot": envelope["pivot"],
        "coefficient": coefficient,
        "equation_terms": len(polynomial),
        "substitution_terms": len(substitution),
        "checked_numerator_terms": numerator_terms,
        "denominator_powers": report[
            "derived_substitution"
        ]["denominator_powers"],
        "verdict": report["gp_report"]["verdict"],
        "authority": report["authority"],
        "source_fingerprint": report["source_fingerprint"],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--math-stuff",
        type=Path,
        default=Path(__file__).resolve().parents[3] / "math-stuff",
    )
    args = parser.parse_args()
    producer_dir = args.math_stuff.resolve() / "d2_plane_72_108"
    sys.path.insert(0, str(producer_dir))
    if "--quiet" not in sys.argv:
        sys.argv.append("--quiet")
    qmod = importlib.import_module("f2_h3_q_window_elimination")

    results = []
    used = set()
    for key, variable, rest, rational in qmod.INVENTORY:
        if variable == qmod.P_IDX or variable in used:
            continue
        used.add(variable)
        results.append(replay(qmod, key, variable, rest, rational))
    if len(results) != 12:
        raise RuntimeError("expected 12 independent pivots, got %d" % len(results))
    print(json.dumps({
        "schema": "jc_h3_gp_q_pivot_batch_replay_v1",
        "model_digest": qmod.contract.model_digest(qmod.contract.CHARTS["q"]),
        "dense_back_substitution": False,
        "verified_pivots": len(results),
        "results": results,
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
