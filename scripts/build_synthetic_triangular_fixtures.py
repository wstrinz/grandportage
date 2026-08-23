"""Regenerate the domain-neutral localized triangular-chain fixtures."""

from __future__ import annotations

import json
from pathlib import Path

from grandportage import triangular as TRI


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "fixtures" / "algebraic_contracts"


def _generators(start, *, normalized):
    equations = []
    for index in range(start, 6):
        equation = "u*(x%d-%d)" % (index, index)
        if normalized:
            equation += "+(u-1)"
        equations.append(equation)
    tail = "y+%d" % sum(range(1, start))
    if start <= 5:
        tail += "+" + "+".join("x%d" % index
                               for index in range(start, 6))
    return equations + [tail]


def build(schema):
    normalized = schema == TRI.SCHEMA_V2
    variables = ["u", "y"] + ["x%d" % index for index in range(1, 6)]
    context = ["u-1"] if normalized else None
    states = [_generators(index, normalized=normalized)
              for index in range(1, 7)]
    fingerprints = [TRI.state_fingerprint(
        0, "Q", "ALGEBRAIC_CLOSURE", variables, ["u"], state, context,
    ) for state in states]
    steps = []
    for index in range(1, 6):
        step = {
            "id": "step-%d" % index,
            "input_state_fingerprint": fingerprints[index - 1],
            "equation_index": 0,
            "equation": states[index - 1][0],
            "pivot": "x%d" % index,
            "coefficient": "u",
            "solution": str(index),
            "output_generators": states[index],
            "output_state_fingerprint": fingerprints[index],
        }
        if normalized:
            step["normalization_cofactors"] = ["1"]
        steps.append(step)
    result = {
        "schema": schema,
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": "ALGEBRAIC_CLOSURE",
        "ring_vars": variables,
        "unit_generators": ["u"],
        "source_receipt": {
            "id": "synthetic-triangular-chain",
            "sha256": "sha256:" + "2" * 64,
        },
        "initial_generators": states[0],
        "steps": steps,
    }
    if normalized:
        result["normalization_generators"] = context
    return result


def main():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    for schema, filename in (
        (TRI.SCHEMA, "localized_triangular_solve_chain_v1.json"),
        (TRI.SCHEMA_V2, "localized_triangular_solve_chain_v2.json"),
    ):
        path = OUTPUT / filename
        path.write_text(json.dumps(build(schema), indent=2, sort_keys=True) + "\n",
                        encoding="utf-8")
        TRI.verify(json.loads(path.read_text(encoding="utf-8")))


if __name__ == "__main__":
    main()
