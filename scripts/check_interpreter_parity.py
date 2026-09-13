"""Bind the Lean example's serialized expressions to the Python/graph fixture.

This executable correspondence is not a proof of the Python parser or checker.
"""

import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from grandportage import ordered_sos as SOS  # noqa: E402
from grandportage import groebner as G  # noqa: E402

FIXTURE = ROOT / "tests" / "fixtures" / "atlas" / "ordered_certificate.json"


def fixture():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def compare(payload):
    expected = fixture()
    model = expected["model"]
    # The renderer uses multiplication where the fixture uses powers. Normalize
    # only this syntactic difference before the closed, model-bound SOS replay.
    candidate = dict(payload)
    candidate["generators"] = [G.canonical_polynomial(p, model["ring_vars"], 0)
                               for p in candidate["generators"]]
    actual = SOS.verify(model, candidate)
    wanted = SOS.verify(model, expected["certificate"])
    if actual != wanted:
        raise ValueError("Lean certificate differs from the graph fixture")
    return actual


def main():
    run = subprocess.run(["lake", "env", "lean", "--run", "InterpreterParity.lean"],
                         cwd=ROOT / "lean", capture_output=True, text=True,
                         encoding="utf-8", timeout=120)
    if run.returncode:
        sys.stderr.write(run.stdout + run.stderr)
        return run.returncode
    try:
        compare(json.loads(run.stdout))
    except (ValueError, TypeError, KeyError) as exc:
        sys.stderr.write("Interpreter parity failed: %s\n" % exc)
        return 1
    print("Interpreter parity: Lean expressions replay and match the graph fixture.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
