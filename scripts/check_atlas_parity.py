"""Compare independently implemented Lean reach semantics with Python.

Run after `lake build` in lean/. No dependencies beyond Python and Lean.
This gate covers the bounded canonical field vocabulary and representative
distinct primes, not Python parsing, primality, or graph authority binding.
"""

from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from grandportage import field  # noqa: E402


def expected_rows():
    fields = ("Q", "R", "C", "F_2", "F_3", "F_5", "F_7")
    reaches = [(kind, {"kind": kind})
               for kind in ("NONE", "ORDERED", "CHAR_0")]
    reaches.extend(("FIELD_SPECIFIC:" + name,
                    {"kind": "FIELD_SPECIFIC", "field": name})
                   for name in fields)
    rows = {}
    for label, reach in reaches:
        for target in fields + ("ANY_ORDERED", "ANY_CHAR_0"):
            rows[("reach", label, target)] = field.instantiate(
                reach, target).allowed
    for source in fields:
        for target in fields:
            rows[("extension", source, target)] = field.concrete_extension(
                source, target).allowed
    return rows


def compare(output):
    observed = {}
    for line in output.splitlines():
        parts = line.split("\t")
        if len(parts) != 4 or parts[-1] not in ("true", "false"):
            raise ValueError("unexpected Lean parity output: %r" % line)
        key = tuple(parts[:3])
        if key in observed:
            raise ValueError("duplicate Lean parity row: %r" % (key,))
        observed[key] = parts[-1] == "true"
    expected = expected_rows()
    differences = ["%s: Python=%r Lean=%r" % (
        "/".join(key), expected.get(key), observed.get(key))
        for key in sorted(set(expected) | set(observed))
        if key not in expected or key not in observed
        or expected[key] != observed[key]]
    if differences:
        raise ValueError("atlas parity failed:\n" + "\n".join(differences))
    return len(expected)


def main():
    run = subprocess.run(
        ["lake", "env", "lean", "--run", "AtlasParity.lean"],
        cwd=str(ROOT / "lean"), capture_output=True, text=True,
        encoding="utf-8", timeout=120)
    if run.returncode:
        sys.stderr.write(run.stdout + run.stderr)
        return run.returncode
    try:
        count = compare(run.stdout)
    except ValueError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1
    print("Atlas parity: %d reach/extension decisions agree." % count)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
