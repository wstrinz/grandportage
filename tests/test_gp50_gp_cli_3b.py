"""Phase 5 preparation: 3b claims in the `gp` CLI, filed end to end and decided by `gp_ledger3` (`Plan3.run`).

A small campaign over ℝ, ℚ, semireal fields and a number field: a √2 point over ℝ, an SOS EMPTY in
every semireal field (and its narrowing to ℝ), an ordered EMPTY with sign conditions, a rational-root
EMPTY over ℚ, a selected-root cover, a number-field point, an algPoint NOT_IN_IDEAL(1), K1a from a 3a
EMPTY, a refused ℂ → ℝ attempt, and a Kummer-premised claim that stays OPEN. 3a claims in the same
ledger are still decided by `gp_ledger`.
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
spec = importlib.util.spec_from_file_location("gp_cli_3b", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

GOAL = {"kind": "DECIDE", "name": "Q", "statement": "some real x > 0 has x^2 = 2",
        "negation": "no real x > 0 has x^2 = 2", "readings": ["Euclidean reals", "exact equality"]}
SQRT2 = {"type": "real_point", "symbol": "w", "polynomial": "w^2 - 2", "interval": ["1", "2"], "point": {"x": "w"}}


class GpCli3b(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = Path(tempfile.mkdtemp())
        (cls.dir / "campaign.json").write_text(json.dumps({"name": "3b CLI controls", "family": [], "goal": GOAL}))
        cls.gp("init")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    @classmethod
    def gp(cls, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(cls.dir), *args])
        return code, out.getvalue() + err.getvalue()

    def file(self, name, body):
        path = self.dir / f"{name}.json"
        path.write_text(json.dumps(body), encoding="utf-8")
        return str(path)

    def held(self, label, receipt):
        code, out = self.gp("submit", label, self.file(label + "-receipt", receipt))
        self.assertEqual(code, 0, out)
        self.assertIn(f"held: {label}", out)
        return out

    def refused(self, label, receipt, *needles):
        code, out = self.gp("submit", label, self.file(label + "-refused", receipt))
        self.assertEqual(code, 1, out)
        for n in needles:
            self.assertIn(n, out)
        return out

    def test_1_sqrt2_over_r(self):
        sys_ = self.file("sqrt2", {"variables": ["x"], "equations": ["x^2 - 2"], "signs": [["x", ">0"]]})
        code, out = self.gp("claim", "sqrt2", "--system", sys_, "--kind", "NONEMPTY", "--real")
        self.assertEqual(code, 0, out)
        self.assertIn("NONEMPTY at the field ℝ; open", out)
        # The interval [2, 3] selects no root of w^2 - 2: the point replay refuses, and says why.
        self.refused("sqrt2", {"certificate": dict(SQRT2, interval=["2", "3"])}, "point receipt is refused",
                     "point replay refused", "the interval must hold exactly one root")
        self.held("sqrt2", {"certificate": SQRT2})

    def test_2_sos_empty_semireal_and_narrowing(self):
        sys_ = self.file("x2p1", {"variables": ["x"], "equations": ["x^2 + 1"]})
        self.gp("claim", "x2p1-semireal", "--system", sys_, "--kind", "EMPTY", "--semireal")
        # 1 + x^2 + (-1)(x^2 + 1) = 0: -1 is a sum of squares on the locus.
        self.refused("x2p1-semireal", {"certificate": {"type": "sos", "cofactors": ["1"], "squares": ["x"]}},
                     "the exact identity leaves a nonzero residual")
        self.held("x2p1-semireal", {"certificate": {"type": "sos", "cofactors": ["-1"], "squares": ["x"]}})
        self.gp("claim", "x2p1-real", "--system", sys_, "--kind", "EMPTY", "--real")
        self.held("x2p1-real", {"rule": {"type": "narrow"}, "premises": ["x2p1-semireal"]})

    def test_3_alg_point_and_refused_c_to_r(self):
        sys_ = self.file("x2p3", {"variables": ["x"], "equations": ["x^2 + 3"], "nonzero": []})
        # A 3a claim; its algPoint receipt routes it to gp_ledger3.
        self.gp("claim", "x2p3-complex", "--system", sys_, "--kind", "NOT_IN_IDEAL", "--target", "1", "--char0")
        self.held("x2p3-complex", {"certificate": {"type": "alg_point", "symbol": "t", "polynomial": "t^2 + 3",
                                                   "point": {"x": "t"}}})
        # ℂ → ℝ: no scope order and no rule carries a complex point to a real one.
        self.gp("claim", "x2p3-real-point", "--system", sys_, "--kind", "NONEMPTY", "--real")
        self.refused("x2p3-real-point", {"rule": {"type": "narrow"}, "premises": ["x2p3-complex"]},
                     "no scope order from characteristic 0 to real", "nothing narrows from a characteristic")
        self.refused("x2p3-real-point", {"rule": {"type": "k1b"}, "premises": ["x2p3-complex"]},
                     "rule K1b", "a complex point (NOT_IN_IDEAL(1)) does not give a real one")

    def test_4_k1a_from_3a_empty(self):
        sys_ = self.file("lin", {"variables": ["x"], "equations": ["x - 1", "x - 2"], "nonzero": []})
        self.gp("claim", "lin-empty-0", "--system", sys_, "--kind", "EMPTY", "--char0")
        self.held("lin-empty-0", {"certificate": {"type": "ideal", "cofactors": ["1", "-1"], "m": 0, "k": 0}})
        self.gp("claim", "lin-empty-semireal", "--system", sys_, "--kind", "EMPTY", "--semireal")
        self.held("lin-empty-semireal", {"rule": {"type": "k1a"}, "premises": ["lin-empty-0"]})
        # The 3a claim is still decided by gp_ledger: it keeps its earned reach.
        ledger = gp.Ledger(self.dir)
        keys = {c["label"]: c["key"] for c in ledger.claims()}
        # 3b claims get the merge guard's content-hashed keys (>= 2^32); gp_ledger3 reads them as Nat.
        self.assertGreaterEqual(keys["lin-empty-semireal"], 1 << 32)
        routed = gp.routed_3b(ledger)
        self.assertNotIn(keys["lin-empty-0"], routed)
        self.assertIn(keys["lin-empty-semireal"], routed)
        self.assertIn(keys["x2p3-complex"], routed)

    def test_5_ordered_ratroot_cover_nf(self):
        # x > 0 and x < 0: x + 1·(-x) = 0, the ordered identity with one cone term.
        self.gp("claim", "sign-clash", "--system", self.file("clash", {"variables": ["x"], "signs": [
            ["x", 1], ["x", -1]]}), "--kind", "EMPTY", "--real")
        self.held("sign-clash", {"certificate": {"type": "ordered", "cofactors": [], "positive_powers": [1, 0],
                                                 "cone": [{"atoms": [1], "squares": ["1"]}]}})
        self.gp("claim", "sqrt2-not-rational", "--system", self.file("x2m2", {"variables": ["x"], "equations": [
            "x^2 - 2"]}), "--kind", "EMPTY", "--rat-field")
        self.held("sqrt2-not-rational", {"certificate": {"type": "rational_root"}})
        cover = {"variables": ["x"], "equations": ["x^2 - 2"], "signs": [["x - 1", 1], ["x - 2", -1]],
                 "branches": [{"equations": ["x^2 - 2"], "signs": [["x", 1]]}]}
        self.gp("claim", "sqrt2-cover", "--system", self.file("cover", cover), "--kind", "COVER", "--real")
        self.held("sqrt2-cover", {"certificate": {"type": "root_cover", "interval": ["1", "2"]}})
        nf = {"symbol": "t", "minimal_polynomial": "t^2 - 2", "variables": ["x", "y"],
              "equations": ["x^2 - 2", "y - x - 1"], "nonzero": ["x"], "point": {"x": "t", "y": "t + 1"}}
        code, out = self.gp("claim", "nf-point", "--nf", self.file("nf", nf), "--kind", "NONEMPTY", "--char0")
        self.assertEqual(code, 0, out)
        self.held("nf-point", {"certificate": {"type": "nf"}})

    def test_6_kummer_premise_stays_open(self):
        sys_ = self.file("sqrt6", {"variables": ["x", "y"], "equations": ["x^2 - 2", "y^2 - 3"],
                                   "signs": [["x", 1], ["y", 1]]})
        code, out = self.gp("claim", "sqrt2-sqrt3", "--system", sys_, "--kind", "NONEMPTY", "--real",
                            "--premise", "KUMMER-INDEPENDENCE=2,3")
        self.assertEqual(code, 0, out)
        self.assertIn("[premise KUMMER-INDEPENDENCE: OPEN]", out)
        # w = √2 + √3 has minimal polynomial w^4 - 10w^2 + 1; √2 = (w^3 - 9w)/2, √3 = (11w - w^3)/2.
        self.held("sqrt2-sqrt3", {"certificate": {
            "type": "real_point", "symbol": "w", "polynomial": "w^4 - 10*w^2 + 1", "interval": ["3", "4"],
            "point": {"x": "w^3/2 - 9*w/2", "y": "11*w/2 - w^3/2"}}})
        code, out = self.gp("explain", "sqrt2-sqrt3")
        self.assertIn("premise KUMMER-INDEPENDENCE: OPEN (the square classes of 2, 3", out)
        self.assertIn("means: has a point over ℝ with x^2 - 2 = 0, y^2 - 3 = 0, x > 0, y > 0", out)
        code, out = self.gp("tailings", "--export")
        self.assertIn("KUMMER-INDEPENDENCE OPEN", out)

    def test_7_claim_refusals(self):
        sys_ = self.file("x2p1", {"variables": ["x"], "equations": ["x^2 + 1"]})
        code, out = self.gp("claim", "bad-1", "--system", sys_, "--kind", "NONEMPTY", "--semireal")
        self.assertEqual(code, 1)
        self.assertIn("no admitted evidence gives a point in every semireal field", out)
        code, out = self.gp("claim", "bad-2", "--system", self.file("signs-q", {"variables": ["x"], "signs": [
            ["x", 1]]}), "--kind", "EMPTY", "--semireal")
        self.assertIn("sign conditions are read only over ℝ", out)
        code, out = self.gp("claim", "bad-3", "--system", self.file("undeclared", {"variables": ["x"], "equations": [
            "x - y"]}), "--kind", "EMPTY", "--real")
        self.assertEqual(code, 1)
        # Refused at filing, before the runner, naming the text (0.50 Trials C3b).
        self.assertIn("does not parse (equations[0]: undeclared variable: y)", out)
        code, out = self.gp("claim", "bad-4", "--system", sys_, "--kind", "EMPTY", "--real", "--premise", "OTHER")
        self.assertIn("unknown named premise OTHER", out)
        labels = {c["label"] for c in gp.Ledger(self.dir).claims()}
        self.assertFalse({"bad-1", "bad-2", "bad-3", "bad-4"} & labels)

    def test_8_views(self):
        code, out = self.gp("status")
        self.assertEqual(code, 0, out)
        self.assertIn("Real and number-field claims (held claims only; some results modulo the OPEN premise "
                      "KUMMER-INDEPENDENCE):", out)
        self.assertIn("has a point over ℝ with x^2 - 2 = 0, x > 0 (sqrt2)", out)
        self.assertIn("no point in any semireal field with x^2 + 1 = 0 (x2p1-semireal)", out)
        self.assertIn("no point over ℚ with x^2 - 2 = 0 (sqrt2-not-rational)", out)
        self.assertIn("has a point over an algebraically closed field of characteristic 0 (over ℂ, for instance) "
                      "with x^2 + 3 = 0 (x2p3-complex)", out)
        self.assertIn("t^2 - 2 is irreducible over ℚ and, at every root t of it", out)
        self.assertIn("(sqrt2-sqrt3) (modulo KUMMER-INDEPENDENCE)", out)
        self.assertIn("[premise KUMMER-INDEPENDENCE: OPEN]", out)
        self.assertIn("Goal: DECIDE Q := some real x > 0 has x^2 = 2", out)
        self.assertIn("readings: Euclidean reals; exact equality", out)
        self.assertIn("  Q: not held\n", out)  # sqrt2-sqrt3 is no goal claim (HW61 G-1)
        self.assertIn("verdict: undecided", out)
        code, out = self.gp("frontier")
        self.assertEqual(code, 0, out)
        self.assertIn("x2p3-real-point: refused:", out)
        code, out = self.gp("explain", "lin-empty-semireal")
        self.assertIn("by rule k1a from:", out)
        self.assertIn("lin-empty-0: EMPTY at characteristic 0: held", out)
        code, out = self.gp("explain", "sqrt2")
        self.assertIn("by real_point certificate", out)
        self.assertIn("point replay accepted", out)

    def test_9_batch_and_append_only(self):
        sys_ = self.file("x2m3", {"variables": ["x"], "equations": ["x^2 - 3"], "signs": [["x", -1]]})
        self.gp("claim", "b-minus-sqrt3", "--system", sys_, "--kind", "NONEMPTY", "--real")
        self.gp("claim", "b-x2m3-q", "--system", self.file("x2m3q", {"variables": ["x"], "equations": ["x^2 - 3"]}),
                "--kind", "EMPTY", "--rat-field")
        batch = [{"label": "b-minus-sqrt3", "receipt": self.file("bb1", {"certificate": {
                     "type": "real_point", "symbol": "w", "polynomial": "w^2 - 3", "interval": ["-2", "-1"],
                     "point": {"x": "w"}}})},
                 {"label": "b-x2m3-q", "receipt": self.file("bb2", {"certificate": {"type": "rational_root"}})}]
        code, out = self.gp("submit-batch", self.file("batch3", batch))
        self.assertEqual(code, 0, out)
        self.assertIn("batch: 2 held, 0 refused, in 1 folds", out)
        lines = (self.dir / "ledger.jsonl").read_text(encoding="utf-8").splitlines()
        self.assertTrue(all(json.loads(l)["op"] in {"init", "claim", "support", "refused"} for l in lines))

    def test_9a_explain_diagnoses_of_held_receipts(self):
        # A real point on an order-free NONEMPTY claim (no sign conditions): the point replay's own diagnosis.
        sys_ = self.file("x2m2-free", {"variables": ["x"], "equations": ["x^2 - 2"]})
        self.gp("claim", "sqrt2-free", "--system", sys_, "--kind", "NONEMPTY", "--real")
        self.held("sqrt2-free", {"certificate": SQRT2})
        code, out = self.gp("explain", "sqrt2-free")
        self.assertIn("by real_point certificate", out)
        self.assertIn("point replay accepted (a point over ℝ)", out)
        self.assertNotIn("no admission for this evidence", out)
        # A held 3a receipt, as gp_ledger3 reports it: held, not "its reach does not cover".
        sys2 = self.file("x-minus-1", {"variables": ["x"], "equations": ["x - 1"], "nonzero": []})
        self.gp("claim", "one-point", "--system", sys2, "--kind", "NONEMPTY", "--char0")
        self.held("one-point", {"certificate": {"type": "point", "point": {"x": "1"}}})
        ledger = gp.Ledger(self.dir)
        key = ledger.claim("one-point")["key"]
        item = next(i for i in gp.run_ledger3(gp.surface3(ledger, {key}))["items"] if i["key"] == key)
        self.assertTrue(item["held"])
        self.assertEqual(item["diagnosis"], "held: 3a receipt accepted; its reach covers the requested scope")

    def test_9b_decide_goal(self):
        # HW61 G-1: shape is not meaning. Both premise-free shortcuts are refused at filing.
        sys_ = self.file("x2p1", {"variables": ["x"], "equations": ["x^2 + 1"]})
        code, out = self.gp("claim", "g-not-q", "--system", sys_, "--kind", "EMPTY", "--real", "--goal", "no")
        self.assertEqual(code, 1, out)
        self.assertIn("one exclusion cannot show not Q", out)
        sys2 = self.file("sqrt2", {"variables": ["x"], "equations": ["x^2 - 2"], "signs": [["x", ">0"]]})
        code, out = self.gp("claim", "g-q", "--system", sys2, "--kind", "NONEMPTY", "--real", "--goal", "yes")
        self.assertEqual(code, 1, out)
        self.assertIn("a --system claim carries no bridge to Q", out)
        # The shape check still runs first: Q is a point over R.
        code, out = self.gp("claim", "g-bad", "--system", sys_, "--kind", "EMPTY", "--real", "--goal", "yes")
        self.assertIn("Q is shown by a point over ℝ", out)
        # Defence in depth: a goal tag already in a ledger (filed before G-1) never decides the goal.
        self.gp("claim", "g-legacy", "--system", sys2, "--kind", "NONEMPTY", "--real")
        self.held("g-legacy", {"certificate": SQRT2})
        path = self.dir / "ledger.jsonl"
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            r = json.loads(line)
            if r.get("op") == "claim" and r.get("label") == "g-legacy":
                r["goal"] = "yes"
                lines[i] = json.dumps(r, ensure_ascii=False, sort_keys=True)
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        code, out = self.gp("status")
        self.assertIn("Q: not held (g-legacy held, but unbridged", out)
        self.assertIn("verdict: undecided", out)
        self.assertNotIn("decided: Q", out)
        code, out = self.gp("explain", "g-legacy")
        self.assertIn("filed as Q (unbridged:", out)


if __name__ == "__main__":
    unittest.main()
