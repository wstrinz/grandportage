"""Translate the frozen native JC top-face receipt into GP chain evidence.

This adapter reads ``math-stuff`` but never writes it.  JC remains responsible
for source extraction and its native replay; GP independently recomputes the
ordered polynomial substitutions over the exact five top-face equations.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

from grandportage import groebner as G
from grandportage import triangular as TRI


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE = (ROOT.parent / "math-stuff" / "d2_plane_72_108" /
                  "f2_h3_q_receipt_probe.json")
DEFAULT_FIXTURE = (ROOT / "fixtures" / "jc_source_ladder" /
                   "localized_triangular_solve_chain_v1.json")
ORDER = [
    (2, "I4"),
    (5, "c[6,9]"),
    (1, "c[9,14]"),
    (4, "I1"),
    (3, "Im1"),
]
VARIABLES = [
    "t", "c2_3", "c3_5", "c4_5", "c5_7", "c8_12",
    "I4", "c6_9", "c9_14", "I1", "Im1", "a2", "r",
]


def _gp_name(value):
    return re.sub(r"c\[(\d+),(\d+)\]", r"c\1_\2", value)


def _sha256(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def build_spec(native, source_bytes):
    if native.get("id") != "f2_h3_q_receipt_probe":
        raise ValueError("unexpected native receipt id")
    checks = native.get("checks", {})
    if checks.get("passed") != checks.get("total"):
        raise ValueError("native source receipt does not report all checks passed")
    replacement = native["replacement"]
    faces = native["row_windows"]
    solutions = replacement["top_face_ladder"]
    coefficients = replacement["pivot_coefficients"]

    generators = [_gp_name(faces[str(row)]["top_face"])
                  for row, _pivot in ORDER]
    generators.append("r+I4+c6_9+c9_14+I1+Im1")
    spec = {
        "schema": TRI.SCHEMA,
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": "ALGEBRAIC_CLOSURE",
        "source_receipt": {
            "id": native["id"],
            "sha256": _sha256(source_bytes),
        },
        "ring_vars": VARIABLES,
        "unit_generators": ["t"],
        "initial_generators": generators,
        "steps": [],
    }

    current = list(generators)
    for row, native_pivot in ORDER:
        pivot = _gp_name(native_pivot)
        solution = _gp_name(solutions[native_pivot])
        coefficient = coefficients[pivot]
        input_fingerprint = TRI.state_fingerprint(
            0, "Q", "ALGEBRAIC_CLOSURE", VARIABLES, ["t"], current,
        )
        images = dict((name, name) for name in VARIABLES)
        images[pivot] = solution
        output = []
        for position, generator in enumerate(current):
            if position == 0:
                continue
            value = G.substitute_polynomial(generator, VARIABLES, images)
            if not G.parse_polynomial(value, VARIABLES).is_zero:
                output.append(value)
        output_fingerprint = TRI.state_fingerprint(
            0, "Q", "ALGEBRAIC_CLOSURE", VARIABLES, ["t"], output,
        )
        spec["steps"].append({
            "id": "top-r%d" % row,
            "input_state_fingerprint": input_fingerprint,
            "equation_index": 0,
            "equation": current[0],
            "pivot": pivot,
            "coefficient": coefficient,
            "solution": solution,
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
        args.fixture.parent.mkdir(parents=True, exist_ok=True)
        args.fixture.write_text(encoded, encoding="utf-8")
    else:
        frozen = args.fixture.read_text(encoding="utf-8")
        if frozen != encoded:
            raise SystemExit("frozen GP fixture differs from native adapter output")

    print("%s: %d/%d native checks; %d ordered GP steps" % (
        report["verdict"], native["checks"]["passed"],
        native["checks"]["total"], report["checked_steps"],
    ))
    print("source %s" % report["source_receipt"]["sha256"])
    print("authority: %s" % report["authority_boundary"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
