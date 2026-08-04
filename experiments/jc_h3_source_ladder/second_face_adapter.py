"""Replay the second actual-source ladder modulo its scalar-gauge equation."""

import argparse
import hashlib
import json
from pathlib import Path
import re

from grandportage import groebner as G
from grandportage import triangular as TRI


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE = (ROOT.parent / "math-stuff" / "d2_plane_72_108" /
                  "f2_h3_source_second_face.json")
DEFAULT_FIXTURE = (ROOT / "fixtures" / "jc_source_ladder" /
                   "localized_triangular_solve_chain_v2_second_face.json")
ORDER = [
    (2, "c3_4"),
    (5, "c6_8"),
    (1, "c9_13"),
    (4, "c5_6"),
    (3, "c4_4"),
]
CONTEXT = ["15*t^3+1"]


def _sha256(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _variables(expressions):
    names = set()
    for expression in expressions:
        names.update(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", expression))
    names.add("r")
    return ["t"] + sorted(name for name in names if name != "t")


def build_spec(native, source_bytes):
    if native.get("id") != "f2_h3_source_second_face":
        raise ValueError("unexpected native receipt id")
    checks = native.get("checks", {})
    if checks.get("passed") != checks.get("total"):
        raise ValueError("native source receipt does not report all checks passed")
    faces = native["second_faces"]
    solved = native["ladder2"]["solved_polynomial_forms"]
    coefficients = native["ladder2"]["pivot_coefficients"]
    generators = [faces[str(row)]["post_ladder_face"]
                  for row, _pivot in ORDER]
    generators.append("r+" + "+".join(pivot for _row, pivot in ORDER))
    variables = _variables(
        generators + list(solved.values()) + list(coefficients.values())
        + CONTEXT
    )
    spec = {
        "schema": TRI.SCHEMA_V2,
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": "ALGEBRAIC_CLOSURE",
        "source_receipt": {
            "id": native["id"],
            "sha256": _sha256(source_bytes),
        },
        "ring_vars": variables,
        "unit_generators": ["t"],
        "normalization_generators": CONTEXT,
        "initial_generators": generators,
        "steps": [],
    }

    budget = G._ArithmeticBudget()
    current = list(generators)
    for row, pivot in ORDER:
        solution = solved[pivot]
        coefficient = coefficients[pivot]
        input_fingerprint = TRI.state_fingerprint(
            0, "Q", "ALGEBRAIC_CLOSURE", variables, ["t"], current,
            CONTEXT,
        )
        equation = G.parse_polynomial(current[0], variables, 0, budget)
        pivot_polynomial = G.Polynomial.variable(
            variables, 0, pivot, budget
        )
        solution_polynomial = G.parse_polynomial(
            solution, variables, 0, budget
        )
        coefficient_polynomial = G.parse_polynomial(
            coefficient, variables, 0, budget
        )
        difference = equation - coefficient_polynomial * (
            pivot_polynomial - solution_polynomial
        )
        cofactors = G.standard_representation(
            G.render_polynomial(difference), CONTEXT, variables, 0, budget
        )

        images = dict((name, name) for name in variables)
        images[pivot] = solution
        output = []
        for position, generator in enumerate(current):
            if position == 0:
                continue
            value = G.substitute_polynomial(
                generator, variables, images, 0, budget
            )
            if not G.parse_polynomial(value, variables, 0, budget).is_zero:
                output.append(value)
        output_fingerprint = TRI.state_fingerprint(
            0, "Q", "ALGEBRAIC_CLOSURE", variables, ["t"], output,
            CONTEXT,
        )
        spec["steps"].append({
            "id": "second-r%d" % row,
            "input_state_fingerprint": input_fingerprint,
            "equation_index": 0,
            "equation": current[0],
            "pivot": pivot,
            "coefficient": coefficient,
            "solution": solution,
            "normalization_cofactors": cofactors,
            "output_generators": output,
            "output_state_fingerprint": output_fingerprint,
        })
        current = output
    return spec


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--write-fixture", action="store_true")
    args = parser.parse_args(argv)

    source_bytes = args.source.read_bytes()
    native = json.loads(source_bytes.decode("utf-8"))
    spec = build_spec(native, source_bytes)
    report = TRI.verify(spec)
    encoded = json.dumps(spec, indent=2, sort_keys=True) + "\n"
    if args.write_fixture:
        args.fixture.write_text(encoded, encoding="utf-8")
    elif args.fixture.read_text(encoding="utf-8") != encoded:
        raise SystemExit("frozen GP fixture differs from native adapter output")

    print("%s: %d/%d native checks; %d ordered GP steps" % (
        report["verdict"], native["checks"]["passed"],
        native["checks"]["total"], report["checked_steps"],
    ))
    print("normalization: %s = 0" % CONTEXT[0])
    print("authority: %s" % report["authority_boundary"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
