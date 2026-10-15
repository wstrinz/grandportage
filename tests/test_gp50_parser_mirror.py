"""The Python mirror of the runner's polynomial grammar must agree with the runner (0.51).

`tools/gp.py` checks polynomial text at filing (`poly_syntax_error`) and tests guards for zero
(`guard_canonical`) with a mirror of `GPProfile.Poly.parse`, so a claim is refused before it can stop a fold.
A mirror can drift from what it mirrors. This test runs one corpus through both: the runner (a one-claim
plan, where a parse failure is a fold error) and the mirror. They must agree on every text the mirror decides.
"""
from fractions import Fraction
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_parser_mirror", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

VARS = ["x", "y", "z_1"]

# Texts the runner reads, among them every operator, precedence and unary-minus case the mirror implements.
PARSES = [
    "0", "1", "x", "-x", "+x", "x + y", "x - -y", "x - -y^2", "x*y - z_1", "2*x^3 - 3/4*y",
    "(x + 1)^2 - x^2 - 2*x - 1", "x**2 + y**2", "-(x - y)^3", "x/2 + y/3", "((x))", "z_1^0",
    "3/4", "x - y - z_1", "-x^2",
]
# Texts the runner refuses; the mirror must refuse each too (a division by a nonconstant is left to the runner).
REFUSES = [
    "x + w", "x +", "(x + y", "x + y)", "x ^ y", "x @ y", "1.5*x", "x y", "", "x^", "*x", "@target.txt", "x^2^1",
]
# The mirror's canonical form over Q: zero exactly when the polynomial is zero.
ZERO = ["0", "(x + 1)^2 - x^2 - 2*x - 1", "x - -y^2 + y^2 - x", "-(-(x)) - x", "x/2 - x/2", "x^0 - 1"]
NONZERO = ["1", "x", "x - -y^2", "(x + 1)^2 - x^2", "-1/2", "z_1^0"]


def runner_parses(text):
    plan = {"claims": [{"key": 1, "variables": VARS, "equations": [text], "nonzero": [], "kind": "EMPTY",
                        "inputs": ["system:0"]}], "requested": [1], "frames": []}
    out = gp.run_profile(plan)
    return not gp.fold_failure(out)


class ParserMirror(unittest.TestCase):
    def test_runner_and_mirror_agree(self):
        for text in PARSES + REFUSES:
            with self.subTest(text=text):
                mirror = gp.poly_syntax_error(VARS, text) is None
                self.assertEqual(runner_parses(text), mirror,
                                 f"runner and mirror disagree on {text!r} (mirror: {gp.poly_syntax_error(VARS, text)})")
        self.assertTrue(all(gp.poly_syntax_error(VARS, t) is None for t in PARSES))
        self.assertTrue(all(gp.poly_syntax_error(VARS, t) for t in REFUSES))

    def test_zero_test(self):
        for text in ZERO:
            with self.subTest(text=text):
                self.assertEqual(gp.guard_canonical(VARS, text), {})
        for text in NONZERO:
            with self.subTest(text=text):
                self.assertNotEqual(gp.guard_canonical(VARS, text), {})
        self.assertEqual(gp.guard_canonical(VARS, "-1/2"), {(0, 0, 0): Fraction(-1, 2)})


if __name__ == "__main__":
    unittest.main()
