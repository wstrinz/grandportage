"""The merge guard on ledgers with 3b claims (release hardening, fix 1 and 2).

`gp merge` on a ledger with a claim over ℝ, ℚ or a semireal field ran the 3a guard without its flag, and so
refused every such merge ("inputs fit no 3a frontend family"); the 3b claims themselves never reached the
Kernel guard. Now `run_guard` runs the Kernel's `resolve` on each runner's merged log: `gp_ledger --guard` on
the 3a part and `gp_ledger3 --guard` (`GPProfile.Real.LedgerRun3.guardLedger3`) on the 3b part.

a. Disjoint and shared 3b claims on two branches merge, and every claim held on either branch is held after.
b. A 3b claim held by a certificate on one branch and by rule narrow on the other: the Kernel refuses
   (conflicting warrant contents), from gp_ledger3's guard.
c. Two branches allocate one key to different 3b claims (the old counter allocator): the Kernel refuses
   (conflicting current bindings), from gp_ledger3's guard.
d. Two different certificates for one 3b claim (fix 2): `merge_plan` splits the claim in the 3b part (it used
   to raise KeyError); the Kernel warrants are equal, and the adapter refuses the different receipts.
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
spec = importlib.util.spec_from_file_location("gp_cli_merge3", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

SYSTEMS = {"sqrt2": {"variables": ["x"], "equations": ["x^2 - 2"], "signs": [["x", ">0"]]},
           "x2p1": {"variables": ["z"], "equations": ["z^2 + 1"]},
           "w2m1": {"variables": ["w"], "equations": ["w^2 - 1"]},
           "lin": {"variables": ["y"], "equations": ["y - 3"]}}
SQRT2_POINT = {"certificate": {"type": "real_point", "symbol": "t", "polynomial": "t^2 - 2", "interval": ["1", "2"],
                               "point": {"x": "t"}}}
X2P1_SOS = {"certificate": {"type": "sos", "cofactors": ["-1"], "squares": ["z"]}}


def point(**values):
    return {"certificate": {"type": "real_point", "point": {k: str(v) for k, v in values.items()}}}


class MergeGuard3b(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.files = self.tmp / "files"
        self.files.mkdir()
        for name, system in SYSTEMS.items():
            (self.files / f"{name}.json").write_text(json.dumps(system), encoding="utf-8")
        self.base = self.tmp / "base"
        self.base.mkdir()
        (self.base / "campaign.json").write_text(json.dumps({"name": "merge 3b", "family": []}), encoding="utf-8")
        self.ok(self.base, "init")
        # Spy on gp_ledger3: which guard runs happened, and what the Kernel said.
        self.guard3 = []
        real = gp.run_ledger3

        def spy(plan, guard=False):
            out = real(plan, guard)
            if guard:
                self.guard3.append(out)
            return out
        gp.run_ledger3 = spy
        self.addCleanup(setattr, gp, "run_ledger3", real)

    def gp(self, where, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(where), *args])
        return code, out.getvalue() + err.getvalue()

    def ok(self, where, *args):
        code, out = self.gp(where, *args)
        self.assertEqual(code, 0, out)
        return out

    def claim(self, where, label, system, *scope, kind="NONEMPTY"):
        return self.ok(where, "claim", label, "--system", str(self.files / f"{system}.json"), "--kind", kind,
                       *(scope or ("--real",)))

    def submit(self, where, label, receipt):
        path = self.files / f"{where.name}-{label}.json"
        path.write_text(json.dumps(receipt), encoding="utf-8")
        out = self.ok(where, "submit", label, str(path))
        self.assertIn(f"held: {label}", out)

    def fork(self, *names):
        out = []
        for name in names:
            shutil.copytree(self.base, self.tmp / name)
            out.append(self.tmp / name)
        return out

    def key(self, where, label):
        return gp.Ledger(where).claim(label)["key"]

    def held(self, where):
        _, items = gp.state(gp.Ledger(where))
        return {c["label"] for c in gp.Ledger(where).claims() if items[c["key"]]["held"]}

    def refused(self, a, b, reason):
        """`gp merge` refuses with `reason` and leaves both ledgers byte-identical."""
        before = [(d / "ledger.jsonl").read_bytes() for d in (a, b)]
        code, out = self.gp(a, "merge", str(b))
        self.assertEqual(code, 1, out)
        self.assertIn("refused:", out)
        self.assertIn(reason, out)
        self.assertNotIn("Traceback", out)
        self.assertEqual([(d / "ledger.jsonl").read_bytes() for d in (a, b)], before)
        return out

    def test_a_disjoint_and_shared(self):
        self.claim(self.base, "shared", "x2p1", kind="EMPTY")
        self.submit(self.base, "shared", X2P1_SOS)
        self.claim(self.base, "lin-0", "lin", "--char0")  # a 3a claim beside them
        self.submit(self.base, "lin-0", {"certificate": {"type": "point", "point": {"y": "3"}}})
        a, b = self.fork("a", "b")
        self.claim(a, "on-a", "sqrt2")
        self.submit(a, "on-a", SQRT2_POINT)
        self.claim(b, "on-b", "w2m1")
        self.submit(b, "on-b", point(w=1))
        for d in (a, b):  # one 3b claim filed and held alike on both branches: one key, one record after
            self.claim(d, "both", "lin")
            self.submit(d, "both", point(y=3))
        self.assertEqual(self.key(a, "both"), self.key(b, "both"))
        held_a, held_b, theirs = self.held(a), self.held(b), (b / "ledger.jsonl").read_bytes()
        out = self.ok(a, "merge", str(b))
        self.assertIn("merged 2 records (1 claims, 1 supports, 0 refusals); the merged log folds", out)
        self.assertEqual(self.guard3, [{"guard": "ok"}])  # the 3b part went through the Kernel guard
        self.assertEqual((b / "ledger.jsonl").read_bytes(), theirs)
        self.assertEqual([c["label"] for c in gp.Ledger(a).claims()], ["shared", "lin-0", "on-a", "both", "on-b"])
        self.assertEqual(self.held(a), held_a | held_b)
        self.assertIn("nothing to merge", self.ok(a, "merge", str(b)))

    def test_b_certificate_versus_rule(self):
        self.claim(self.base, "z-semi", "x2p1", "--semireal", kind="EMPTY")
        self.submit(self.base, "z-semi", X2P1_SOS)
        self.claim(self.base, "z-real", "x2p1", kind="EMPTY")
        a, b = self.fork("a", "b")
        self.submit(a, "z-real", X2P1_SOS)
        self.submit(b, "z-real", {"rule": {"type": "narrow"}, "premises": ["z-semi"]})
        k = self.key(a, "z-real")
        self.refused(a, b, f"the merged log does not fold: conflicting warrant contents: {k} [rule: merge guard")
        self.assertEqual(self.guard3, [{"error": f"conflicting warrant contents: {k}"}])

    def test_c_same_version_current_tie(self):
        a, b = self.fork("a", "b")
        legacy = gp.new_key
        gp.new_key = lambda ledger, body: 1 + max([c["key"] for c in ledger.claims()], default=0)
        try:
            self.claim(a, "on-a", "sqrt2")
            self.claim(b, "on-b", "w2m1")
        finally:
            gp.new_key = legacy
        k = self.key(a, "on-a")
        self.assertEqual(k, self.key(b, "on-b"))
        self.refused(a, b, f"the merged log does not fold: conflicting current bindings: {k}")
        self.assertEqual(self.guard3, [{"error": f"conflicting current bindings: {k}"}])

    def test_d_split_receipts(self):
        self.claim(self.base, "u", "w2m1")
        c, d = self.fork("c", "d")
        self.submit(c, "u", point(w=1))
        self.submit(d, "u", point(w=-1))
        k = self.key(c, "u")
        merged, new, plan, split = gp.merge_plan(gp.Ledger(c), gp.Ledger(d))
        self.assertEqual(split, {k})
        self.assertEqual(sum(e["key"] == k for e in plan["_3b"]["claims"]), 3)  # the claim and both warrants
        self.refused(c, d, f"conflicting warrant contents: {k} (the branches support u by different receipts)")
        self.assertEqual(self.guard3, [{"guard": "ok"}])  # equal Kernel warrants: the adapter refuses
        # The fix: one receipt on both branches; then the merge lands.
        self.submit(c, "u", point(w=-1))
        self.assertIn("nothing to merge", self.ok(c, "merge", str(d)))
        self.assertIn("the merged log folds", self.ok(d, "merge", str(c)))
        self.assertEqual(gp.Ledger(d).supports()[k]["receipt"], point(w=-1))


if __name__ == "__main__":
    unittest.main()
