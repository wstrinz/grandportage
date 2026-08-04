#!/usr/bin/env python3
"""Replay the two rows 7--8 bare-family unit-ideal certificates."""

from __future__ import annotations

import argparse
import copy
import json
import tempfile

from grandportage import check as C
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import localization as L
from grandportage import store as S
from grandportage import verify as V


def family_spec(chart):
    if chart == "q":
        # Row 8, y^-43: -5*q^3*t^2.  Since q and t are units, its
        # vanishing puts 1 in the localized ideal.
        guards = ["q", "t"]
        generator = "-5*q^3*t^2"
        powers = [3, 2]
        target = "q^3*t^2"
        cofactor = "-1/5"
        receipt = "row 8 coefficient y^-43"
    elif chart == "p":
        # Row 7, y^-38: 5*p^4*t^2.
        guards = ["p", "t"]
        generator = "5*p^4*t^2"
        powers = [4, 2]
        target = "p^4*t^2"
        cofactor = "1/5"
        receipt = "row 7 coefficient y^-38"
    else:
        raise ValueError("chart must be q or p")
    return receipt, {
        "schema": L.SCHEMA,
        "characteristic": 0,
        "ring_vars": ["p", "q", "t"],
        "generators": [generator],
        "guards": guards,
        "expression": {
            "numerator": "1",
            "denominator_powers": [0, 0],
        },
        "certificate": {
            "localization_powers": powers,
            "membership_target": target,
            "cofactors": [cofactor],
        },
    }


def replay(chart):
    receipt, spec = family_spec(chart)
    report = L.verify(spec)
    return {
        "chart": chart,
        "source_receipt": receipt,
        "verdict": report["verdict"],
        "checked_target": report["checked"]["target"],
        "spec_fingerprint": report["spec_fingerprint"],
        "runtime_authority": report["licenses"],
        "certified_coordinate_statement":
            "1 = 0 in the declared localized quotient",
        "lean_bridge": "localized_unit_ideal_has_no_point",
        "standalone_point_emptiness_is_not_graph_bound": True,
        "source_membership_authority": False,
        "h3_authority": False,
    }


def graph_bound_replay(chart):
    """Run the production producer/verdict/fold loop in a disposable graph."""
    receipt, spec = family_spec(chart)
    model_id = "%s-BARE-OPEN" % chart.upper()
    claim_id = "%s-BARE-EMPTY" % chart.upper()
    with tempfile.TemporaryDirectory(
            prefix="gp-jc-rows78-", dir=".") as root:
        S.append([{
            "ev": "model", "id": model_id,
            "what": "%s on its declared principal-open chart" % receipt,
            "characteristic": spec["characteristic"],
            "coefficient_domain": "Q",
            "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
            "ring_vars": spec["ring_vars"],
            "generators": spec["generators"],
            "open_conditions": spec["guards"],
        }, {
            "ev": "claim", "id": claim_id, "model": model_id,
            "kind": K.EMPTY,
            "statement": "%s bare family has no points on this chart" % chart,
            "certificate": "LOCALIZED_UNIT_IDEAL_CERT",
            "established_by": "RAN", "ladder": "exact-checked",
        }], root=root)
        results = V.verify_all(root=root)
        graph = S.load(S.graph_path(root))
        claim = graph.claims[claim_id]
        debts = [
            finding.fid for finding in C.run(graph)
            if "localized-unit" in finding.fid
        ]
        if claim.get("certificate_verdict") != V.CERT_VERIFIED or debts:
            raise AssertionError(
                "graph-bound localized EMPTY did not promote: %r / %r"
                % (claim.get("certificate_verdict"), debts))
        return {
            "chart": chart,
            "claim": claim_id,
            "verdict": claim["certificate_verdict"],
            "verifier": next(
                verdict["verifier"] for verdict in graph.verdicts.values()
                if verdict.get("of") == claim_id),
            "method": claim["representation"]["method"],
            "local_empty_authority": True,
            "parent_empty_authority": False,
            "results": [list(result[:3]) for result in results],
        }

def mutation_controls():
    _receipt, base = family_spec("q")
    mutations = []
    cases = []

    changed = copy.deepcopy(base)
    changed["certificate"]["localization_powers"] = [2, 2]
    cases.append(("wrong localization power", changed))

    changed = copy.deepcopy(base)
    changed["guards"] = ["q"]
    changed["expression"]["denominator_powers"] = [0]
    changed["certificate"]["localization_powers"] = [3]
    cases.append(("removed t guard", changed))

    changed = copy.deepcopy(base)
    changed["guards"] = ["q^2", "t"]
    cases.append(("changed guard exponent", changed))

    changed = copy.deepcopy(base)
    changed["certificate"]["cofactors"] = ["1/5"]
    cases.append(("wrong cofactor sign", changed))

    changed = copy.deepcopy(base)
    changed["guards"] = ["p", "t"]
    cases.append(("cross-chart guards", changed))

    changed = copy.deepcopy(base)
    changed["generators"] = ["-5*q^2*t^2"]
    cases.append(("changed source receipt", changed))

    for label, spec in cases:
        try:
            L.verify(spec)
        except (L.LocalizationError, G.CertificateError):
            mutations.append(label)
    if len(mutations) != len(cases):
        raise AssertionError("a rows 7--8 mutation survived: %r" % mutations)
    return mutations


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--graph-bound", action="store_true",
        help="also run real Singular and persist/reload local EMPTY verdicts")
    args = parser.parse_args(argv)
    report = {
        "schema": "jc_h3_rows78_bare_family_replay_v2",
        "reports": [replay("q"), replay("p")],
        "refused_mutations": mutation_controls(),
    }
    if args.graph_bound:
        report["graph_bound_reports"] = [
            graph_bound_replay("q"), graph_bound_replay("p")]
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
