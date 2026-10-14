"""N6a (DECISIONS 2026-10-13): `gp` refuses a claim whose guard is the zero polynomial.

A zero guard holds nowhere, so an EMPTY claim over it is vacuously true and reads like a refutation. The
refusal comes at filing (`claim`, characteristic-scoped and over a field) and at submission (a claim filed
before N6a), and names the guard by its index. Zero is decided on the canonical form over Q, as the runner
parses the text: a literal `0` and a polynomial that expands to zero are both refused. Controls: a nonzero
constant guard and an ordinary guard are still filed. None of these tests needs a runner build, except the
one control over a field, which runs only when `gp_ledger3` is already fresh.
"""
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_cli_zero_guard", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

EXPANDS_TO_ZERO = "(T1+1)^2 - T1^2 - 2*T1 - 1"
RUNNER3_FRESH = not gp.stale(gp.EXE3)  # checked once; filing over a field would otherwise build it


class ZeroGuardRefusals(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp())
        shutil.copy(ROOT / "campaigns/3p-matroids/campaign.json", self.dir / "campaign.json")
        code, out = self.gp("init")
        self.assertEqual(code, 0, out)

    def tearDown(self):
        shutil.rmtree(self.dir, ignore_errors=True)

    def gp(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(self.dir), *args])
        return code, out.getvalue() + err.getvalue()

    def system(self, name, body):
        path = self.dir / f"{name}.json"
        path.write_text(json.dumps(body), encoding="utf-8")
        return str(path)

    def ledger_lines(self):
        return (self.dir / "ledger.jsonl").read_text(encoding="utf-8").splitlines()

    def assert_refused(self, code, out, where_index, text):
        self.assertEqual(code, 1, out)
        self.assertIn(f"refused: {where_index} ({text}) is the zero polynomial", out)
        self.assertIn("[rule: nonzero guards;", out)
        self.assertIn(f"smallest fix: drop {where_index}", out)

    # --- refusals at filing ---

    def test_literal_zero_guard_refused(self):
        before = self.ledger_lines()
        code, out = self.gp("claim", "lit", "--system", self.system("lit", {
            "variables": ["x"], "equations": ["x - 1"], "nonzero": ["0"]}), "--kind", "EMPTY", "--char0")
        self.assert_refused(code, out, "guard 0", "0")
        self.assertEqual(self.ledger_lines(), before, "a refused claim is not filed")

    def test_guard_expanding_to_zero_refused(self):
        code, out = self.gp("claim", "expands", "--system", self.system("expands", {
            "variables": ["T1", "x"], "equations": ["x^2 - T1"], "nonzero": ["T1 - 1", EXPANDS_TO_ZERO]}),
            "--kind", "EMPTY", "--char0")
        self.assert_refused(code, out, "guard 1", EXPANDS_TO_ZERO)
        self.assertIn("scope: characteristic 0]", out)

    def test_zero_guard_refused_for_every_kind(self):
        code, out = self.gp("claim", "point", "--system", self.system("point", {
            "variables": ["x", "y"], "equations": ["x - 1"], "nonzero": ["y", "x*(y - y)"]}),
            "--kind", "NONEMPTY", "--char", "5")
        self.assert_refused(code, out, "guard 1", "x*(y - y)")
        self.assertIn("scope: characteristic 5]", out)

    def test_zero_guard_refused_over_a_field(self):
        # Refused before any runner is asked to elaborate the claim.
        code, out = self.gp("claim", "real", "--system", self.system("real", {
            "variables": ["x"], "equations": ["x^2 - 2"], "nonzero": ["x - x"]}), "--kind", "EMPTY", "--real")
        self.assert_refused(code, out, "guard 0", "x - x")
        self.assertIn("scope: the field ℝ]", out)

    def test_zero_guard_in_a_cover_branch_refused(self):
        code, out = self.gp("claim", "cov", "--system", self.system("cov", {
            "variables": ["x"], "equations": ["x^2 - 2"], "nonzero": [],
            "branches": [{"signs": [["x", 1]]}, {"nonzero": ["x", "(x - 1)^2 - x^2 + 2*x - 1"]}]}),
            "--kind", "COVER", "--real")
        self.assert_refused(code, out, "branch 1 guard 1", "(x - 1)^2 - x^2 + 2*x - 1")

    def test_every_zero_guard_counted(self):
        code, out = self.gp("claim", "many", "--system", self.system("many", {
            "variables": ["x"], "equations": ["x"], "nonzero": ["x + 1", "0", "x - x", "2*x - x - x"]}),
            "--kind", "EMPTY", "--char0")
        self.assert_refused(code, out, "guard 1", "0")
        self.assertIn("(2 more guards are zero too)", out)

    # --- refusal at submission, for a claim filed before N6a ---

    def test_submission_for_a_pre_n6a_claim_refused(self):
        body = {"label": "legacy", "matroid": None, "system": {"variables": ["T1"], "equations": [],
                "nonzero": [EXPANDS_TO_ZERO]}, "kind": "EMPTY", "target": None, "scope": {},
                "inputs": ["system:legacy"], "named_premises": []}
        with (self.dir / "ledger.jsonl").open("a", encoding="utf-8", newline="\n") as f:
            f.write(json.dumps(dict({"op": "claim", "key": 4242}, **body)) + "\n")
        receipt = self.system("receipt", {"certificate": {"type": "ideal", "cofactors": [], "m": 0, "k": 1}})
        before = self.ledger_lines()
        code, out = self.gp("submit", "legacy", receipt)
        self.assert_refused(code, out, "guard 0", EXPANDS_TO_ZERO)
        self.assertEqual(self.ledger_lines(), before, "nothing is logged and nothing folds")

    # --- controls: still filed ---

    def test_nonzero_constant_guard_filed(self):
        code, out = self.gp("claim", "const", "--system", self.system("const", {
            "variables": ["x"], "equations": ["x - 1"], "nonzero": ["2", "-1/2", "(x+1) - x"]}),
            "--kind", "EMPTY", "--char0")
        self.assertEqual(code, 0, out)
        self.assertIn("claim const", out)
        self.assertIn("filed: EMPTY at characteristic 0; open", out)

    def test_ordinary_guard_filed(self):
        code, out = self.gp("claim", "plain", "--system", self.system("plain", {
            "variables": ["T1", "x"], "equations": ["x^2 - T1"], "nonzero": ["T1 - 1", "x", "(T1+1)^2 - T1^2"]}),
            "--kind", "EMPTY", "--char0")
        self.assertEqual(code, 0, out)
        self.assertIn("filed: EMPTY at characteristic 0; open", out)

    @unittest.skipUnless(RUNNER3_FRESH, "gp_ledger3 is not built for this tree (the filing would build it)")
    def test_ordinary_guard_filed_over_a_field(self):
        code, out = self.gp("claim", "real-ok", "--system", self.system("real-ok", {
            "variables": ["x"], "equations": ["x^2 - 2"], "nonzero": ["x", "3"]}), "--kind", "EMPTY", "--real")
        self.assertEqual(code, 0, out)
        self.assertIn("filed: EMPTY at the field ℝ", out)


class ZeroTestReading(unittest.TestCase):
    """The zero test reads guards as the runner's parser does (`GPProfile.Poly.parse`)."""

    def zero(self, text, variables=("x", "y")):
        return gp.guard_canonical(list(variables), text) == {}

    def test_zero_forms(self):
        for text in ["0", "0*x", "x - x", "x^0 - 1", "0^3", "((((0))))", "x/2 - x/2", "x/(1+1) - x/2",
                     "(x+y)**3 - x^3 - 3*x^2*y - 3*x*y^2 - y^3", "-(-(x)) - x"]:
            self.assertTrue(self.zero(text), text)

    def test_nonzero_forms(self):
        for text in ["1", "-1/2", "0^0", "x", "x - y", "(x+1)^2 - x^2", "x - -y^2"]:
            self.assertFalse(self.zero(text), text)

    def test_unary_minus_binds_as_in_the_runner(self):
        # In the runner's grammar a unary minus after an operator negates the atom before ^ applies:
        # x - -y^2 is x - (-y)^2 = x - y^2, so this sum is zero (a Python-style reading would give 2*y^2).
        self.assertTrue(self.zero("x - -y^2 + y^2 - x"))
        self.assertTrue(self.zero("x + -y^2 - x - y^2"))
        self.assertFalse(self.zero("2*-x^2 + 2*x^2"))

    def test_unread_guards_are_left_to_the_runner(self):
        for text in ["z", "1.5", "x^2^2", "x/y", "", "x/0", "(x+1)^5000 - 1"]:
            with self.assertRaises(gp._Unread, msg=text):
                gp.guard_canonical(["x", "y"], text)
        self.assertEqual(gp.zero_guards({"variables": ["x"], "nonzero": ["z - z", "x"]}), [])

    def test_systems_without_guards(self):
        self.assertEqual(gp.zero_guards({"n": 4, "m": 5, "value": True}), [])
        self.assertEqual(gp.zero_guards({"variables": ["x"], "equations": ["x"]}), [])


if __name__ == "__main__":
    unittest.main()
