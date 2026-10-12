"""Post-G3a §4.4 and §4.6: the 3P checker-gap controls, run through the `gp` CLI and the Kernel fold.

1. Points at a single characteristic: an F_2 point of the Fano system mints NONEMPTY with reach {2}.
2. Mod-p-only emptiness: the non-Fano system is EMPTY at characteristic 2 by a certificate whose
   rational residual vanishes mod 2 but not over Q; its reach is exactly {2}.
3. A point over F_p[a]/(m): `proper` mod p on {m(a) = 0} and R3 along the coordinates, all mod p.
Plus the tutorial's reach refusal: a rational non-Fano point does not reach characteristic 2.
"""
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_cli", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

POINT = {"x4": "1", "y4": "1", "z4": "0", "x5": "0", "y5": "1", "z5": "1", "x7": "1", "y7": "0", "z7": "1"}
# Sigma q_i E_i = (-y4) * z5 * z7 on the Fano system, found by an untrusted CAS; GP replays it.
FANO_EMPTY = ["x5*y7/2 - x7*y5/2", "x4*z5/2", "x4*z7/2", "-y4*z7/2", "y4*z5/2", "z5*z7/2", "-1/2"]


class GpCliControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = Path(tempfile.mkdtemp())
        shutil.copy(ROOT / "campaigns/3p-matroids/campaign.json", cls.dir / "campaign.json")
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

    def receipt(self, name, body):
        path = self.dir / f"{name}.json"
        path.write_text(json.dumps(body), encoding="utf-8")
        return str(path)

    def test_1_fano_point_mod_2(self):
        self.gp("claim", "F7-real-2", "--matroid", "F7", "--kind", "NONEMPTY", "--char", "2")
        code, out = self.gp("submit", "F7-real-2", self.receipt("f7p", {"certificate": {
            "type": "point", "characteristic": 2, "point": POINT}}))
        self.assertEqual(code, 0, out)
        self.assertIn("held", out)

    def test_2_fano_empty_over_q_excludes_2(self):
        self.gp("claim", "F7-unreal-0", "--matroid", "F7", "--kind", "EMPTY", "--char0")
        code, out = self.gp("submit", "F7-unreal-0", self.receipt("f7e", {"certificate": {
            "type": "ideal", "cofactors": FANO_EMPTY, "m": 0, "k": 1, "guards": [0, 1, 2]}}))
        self.assertEqual(code, 0, out)
        self.assertIn("earned, unclaimed: 0 and every prime except {2}", out)
        # The overclaim "Fano is realizable nowhere" from the same certificate: refused at 2 by reach.
        self.gp("claim", "F7-unreal-2", "--matroid", "F7", "--kind", "EMPTY", "--char", "2")
        code, out = self.gp("submit", "F7-unreal-2", self.receipt("f7e2", {"certificate": {
            "type": "ideal", "cofactors": FANO_EMPTY, "m": 0, "k": 1, "guards": [0, 1, 2],
            "characteristic": 2}}))
        self.assertEqual(code, 1)
        self.assertIn("refused", out)
        self.assertIn("does not cover the requested characteristic 2", out)

    def test_3_non_fano_rational_point_does_not_reach_2(self):
        self.gp("claim", "F7m-real-0", "--matroid", "F7-", "--kind", "NONEMPTY", "--char0")
        code, out = self.gp("submit", "F7m-real-0", self.receipt("nfp", {"certificate": {
            "type": "point", "point": POINT}}))
        self.assertEqual(code, 0, out)
        self.assertIn("earned, unclaimed: 0 and every prime except {2}", out)
        self.gp("claim", "F7m-real-2", "--matroid", "F7-", "--kind", "NONEMPTY", "--char", "2")
        code, out = self.gp("submit", "F7m-real-2", self.receipt("nfp2", {"certificate": {
            "type": "point", "characteristic": 2, "point": POINT}}))
        self.assertEqual(code, 1)
        self.assertIn("replay", out)

    def test_3b_non_fano_empty_mod_2_only(self):
        # Sigma q_i E_i - G_22 = -2*y4*z5*z7: zero mod 2, nonzero over Q. Reach exactly {2}.
        cert = {"type": "ideal", "characteristic": 2, "m": 0, "k": 1, "guards": [22],
                "cofactors": ["x5*y7 - x7*y5", "x4*z5", "x4*z7", "-y4*z7", "y4*z5", "z5*z7"]}
        self.gp("claim", "F7m-unreal-2", "--matroid", "F7-", "--kind", "EMPTY", "--char", "2")
        code, out = self.gp("submit", "F7m-unreal-2", self.receipt("nfe2", {"certificate": cert}))
        self.assertEqual(code, 0, out)
        self.assertNotIn("earned", out)
        self.gp("claim", "F7m-unreal-0", "--matroid", "F7-", "--kind", "EMPTY", "--char0")
        code, out = self.gp("submit", "F7m-unreal-0", self.receipt("nfe0", {"certificate": dict(
            cert, characteristic=None)}))
        self.assertEqual(code, 1)

    def test_3c_point_over_f4(self):
        # {x^2 + x + 1 = 0} has no F_2 point; over F_2[a]/(a^2 + a + 1) it has x = a. `proper` mod 2
        # cannot see it (every rootless polynomial is 1 on F_2); the coefficient of `a` can.
        src = self.dir / "src.json"
        src.write_text(json.dumps({"variables": ["a"], "equations": ["a^2 + a + 1"], "nonzero": []}))
        tgt = self.dir / "tgt.json"
        tgt.write_text(json.dumps({"variables": ["x"], "equations": ["x^2 + x + 1"], "nonzero": []}))
        self.gp("claim", "m-proper-2", "--system", str(src), "--kind", "NOT_IN_IDEAL", "--target", "1",
                "--char", "2")
        code, out = self.gp("submit", "m-proper-2", self.receipt("mp", {"certificate": {
            "type": "proper_coefficient", "characteristic": 2, "monomial": "a"}}))
        self.assertEqual(code, 0, out)
        self.gp("claim", "x-proper-2", "--system", str(tgt), "--kind", "NOT_IN_IDEAL", "--target", "1",
                "--char", "2")
        code, out = self.gp("submit", "x-proper-2", self.receipt("xm", {"premises": ["m-proper-2"], "rule": {
            "type": "map", "map": {"x": "a"},
            "eq_certificates": [{"type": "ideal", "characteristic": 2, "cofactors": ["1"], "m": 1, "k": 0}]}}))
        self.assertEqual(code, 0, out)
        # Geometric nonemptiness is not a point in every field of characteristic 2: F_2 has none.
        self.gp("claim", "x-f2-point", "--system", str(tgt), "--kind", "NONEMPTY", "--char", "2")
        code, out = self.gp("submit", "x-f2-point", self.receipt("xf2", {"certificate": {
            "type": "point", "characteristic": 2, "point": {"x": "1"}}}))
        self.assertEqual(code, 1)

    def test_4_views_render(self):
        for args in (["status"], ["frontier"], ["tailings", "--export"], ["explain", "F7-real-2"]):
            code, out = self.gp(*args)
            self.assertEqual(code, 0, out)
        code, out = self.gp("status")
        # ENCODING-FRAME is proved (frame_iff); each matroid claim's system is re-derived by the Lean encoder.
        self.assertIn("[premise ENCODING-FRAME: discharged]", out)
        self.assertNotIn("modulo", out)
        # 3P friction item 1: one χ verdict per matroid, from held claims only.
        self.assertIn("χ(F7) = {2}, fully held", out)
        self.assertIn("χ(F7-) = every characteristic except {2}, fully held", out)
        code, out = self.gp("explain", "F7-real-2")
        self.assertIn("discharged (proved: GPBinding.Matroid.frame_iff", out)
        run, _ = gp.state(gp.Ledger(self.dir))
        self.assertTrue(run["frames"] and all(f["equal"] for f in run["frames"]), run["frames"])
        code, out = self.gp("tailings", "--export")
        self.assertNotIn("open premise", out)
        # A system the Lean encoder does not re-derive keeps the premise OPEN.
        self.assertEqual(gp.premise_state({"frames": [{"key": 1, "equal": False}]}, {"key": 1}), "OPEN")
        self.assertEqual(gp.premise_state({"frames": []}, {"key": 1}), "OPEN")

    def test_4c_refusals_name_the_failure(self):
        # 3P friction items 2, 3 and 5: the failing item, a missing file, decimals.
        code, out = self.gp("submit", "x-f2-point", self.receipt("xf2b", {"certificate": {
            "type": "point", "characteristic": 2, "point": {"x": "1"}}}))
        self.assertIn("equation 0 is 3 at the point, not 0 mod 2", out)
        code, out = self.gp("submit", "x-f2-point", str(self.dir / "absent.json"))
        self.assertEqual(code, 1)
        self.assertIn("no receipt file", out)
        code, out = self.gp("submit", "x-f2-point", self.receipt("xdec", {"certificate": {
            "type": "point", "characteristic": 2, "point": {"x": "0.5"}}}))
        self.assertIn("decimals are not exact numbers", out)

    def test_4b_emit_lean(self):
        code, out = self.gp("emit-lean", "F7-unreal-0")
        self.assertEqual(code, 0, out)
        self.assertIn("theorem w_F7_unreal_0 :", out)
        self.assertIn("(mul_ne_zero g0 (mul_ne_zero g1 g2))", out)  # the selected guards only
        # Points and proper coefficients are covered by the generic warrants; map-rule claims are not yet.
        code, out = self.gp("emit-lean", "F7-real-2")
        self.assertEqual(code, 0, out)
        self.assertIn("warranted_point", out)
        code, out = self.gp("emit-lean", "x-proper-2")
        self.assertEqual(code, 1)
        self.assertIn("no Lean warrant (outside coverage (rule map))", out)
        binding = ROOT / "binding"
        if not (binding / ".lake/build/lib/lean/GPBinding.olean").exists():
            self.skipTest("binding not built")
        code, text = self.gp("emit-lean", "--all")
        self.assertIn("coverage: ", text)
        text = text[: text.index("coverage: ")]
        path = binding / "tmp" / "EmitControl.lean"
        path.parent.mkdir(exist_ok=True)
        path.write_text(text, encoding="utf-8")
        try:
            env = dict(gp.os.environ)
            toolchain = gp.ELAN_HOME / "toolchains" / (binding / "lean-toolchain").read_text(
                encoding="utf-8").strip().replace("/", "--").replace(":", "---")
            env["PATH"] = str(toolchain / "bin") + gp.os.pathsep + env["PATH"]
            run = gp.subprocess.run([str(toolchain / ("bin/lake" + (".exe" if gp.os.name == "nt" else ""))),
                                     "env", "lean", "tmp/EmitControl.lean"], cwd=binding, env=env,
                                    capture_output=True, text=True, encoding="utf-8")
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertNotIn("error", run.stdout)
        finally:
            path.unlink(missing_ok=True)

    def test_4d_submit_batch(self):
        # F2 friction: one fold per batch. Same records as single submits; pre-fold refusals skip.
        self.gp("claim", "b-f7m-0", "--matroid", "F7-", "--kind", "NONEMPTY", "--char0")
        self.gp("claim", "b-f7m-2", "--matroid", "F7-", "--kind", "NONEMPTY", "--char", "2")
        self.gp("claim", "b-f7-2", "--matroid", "F7", "--kind", "NONEMPTY", "--char", "2")
        batch = [{"label": "b-f7m-0", "receipt": self.receipt("b1", {"certificate": {"type": "point", "point": POINT}})},
                 {"label": "b-f7m-2", "receipt": self.receipt("b2", {"certificate": {
                     "type": "point", "characteristic": 2, "point": POINT}})},
                 {"label": "b-nope", "receipt": self.receipt("b3", {"certificate": {"type": "point", "point": POINT}})},
                 {"label": "b-f7-2", "receipt": self.receipt("b4", {"certificate": {
                     "type": "point", "characteristic": 2, "point": POINT}})}]
        before = len(gp.Ledger(self.dir).records)
        code, out = self.gp("submit-batch", self.receipt("batch", batch))
        self.assertEqual(code, 1, out)
        self.assertIn("held: b-f7m-0 at characteristic 0; earned, unclaimed: 0 and every prime except {2}", out)
        self.assertIn("held: b-f7-2 at characteristic 2", out)
        self.assertIn("refused: b-f7m-2: the certificate does not replay exactly", out)
        self.assertIn("refused: b-nope: no claim labelled 'b-nope'", out)
        # The refusal costs one confirming fold without the refused receipt.
        self.assertIn("batch: 2 held, 2 refused, in 2 folds", out)
        added = gp.Ledger(self.dir).records[before:]
        self.assertEqual([(r["op"], r["label"]) for r in added],
                         [("support", "b-f7m-0"), ("refused", "b-f7m-2"), ("support", "b-f7-2")])
        _, items = gp.state(gp.Ledger(self.dir))
        keys = {c["label"]: c["key"] for c in gp.Ledger(self.dir).claims()}
        self.assertTrue(items[keys["b-f7m-0"]]["held"] and items[keys["b-f7-2"]]["held"])
        self.assertFalse(items[keys["b-f7m-2"]]["held"])

    def test_5_ledger_is_append_only_jsonl(self):
        lines = (self.dir / "ledger.jsonl").read_text(encoding="utf-8").splitlines()
        self.assertEqual(json.loads(lines[0])["op"], "init")
        self.assertTrue(all(json.loads(l)["op"] in {"init", "claim", "support", "refused"} for l in lines))


if __name__ == "__main__":
    unittest.main()
