"""Post-G2 §1.5 and §6: the commit/merge guard, with its four collision controls.

Each control forks one `gp` ledger into two branch directories, works on both, and merges one into
the other with `gp merge`. A merge lands only if the merged log still folds in the Kernel;
otherwise it is refused with the Kernel's reason and neither ledger changes.

a. A same-version current tie across branches: two branches allocate one key to different claims
   (the counter allocator `gp` used before content-derived keys). Refused.
b. Retraction versus supersession of one target. `gp` writes no lifecycle records yet (the profile
   files only declarations, currents and warrants), so they are written here at the ledger-JSON
   level, as Kernel `retract` and `supersede` events. Each branch folds alone; the merge is refused.
c. Conflicting warrant contents under one id: one claim filed before the fork, supported by a
   certificate on one branch and by a rule on the other. Refused by the Kernel; two different
   certificates (equal warrant contents, different receipts) are refused by the adapter.
d. A clean concurrent merge: disjoint new claims on both branches, with content-derived keys. Lands,
   folds, and every claim held on either branch is held after it.
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
spec = importlib.util.spec_from_file_location("gp_cli_merge", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

SYSTEMS = {"sx": {"variables": ["x"], "equations": ["x - 1"], "nonzero": []},
           "sy": {"variables": ["y"], "equations": ["y - 2"], "nonzero": []},
           "sz": {"variables": ["z"], "equations": ["z^2 - 1"], "nonzero": []},
           "sw": {"variables": ["w"], "equations": ["w + 3"], "nonzero": []}}


def point(**values):
    return {"certificate": {"type": "point", "point": {k: str(v) for k, v in values.items()}}}


class MergeGuard(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.files = self.tmp / "files"
        self.files.mkdir()
        for name, system in SYSTEMS.items():
            (self.files / f"{name}.json").write_text(json.dumps(system), encoding="utf-8")
        self.base = self.tmp / "base"
        self.base.mkdir()
        shutil.copy(ROOT / "campaigns/3p-matroids/campaign.json", self.base / "campaign.json")
        self.ok(self.base, "init")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def gp(self, where, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(where), *args])
        return code, out.getvalue() + err.getvalue()

    def ok(self, where, *args):
        code, out = self.gp(where, *args)
        self.assertEqual(code, 0, out)
        return out

    def claim(self, where, label, system):
        return self.ok(where, "claim", label, "--system", str(self.files / f"{system}.json"),
                       "--kind", "NONEMPTY", "--char0")

    def submit(self, where, label, receipt):
        path = self.files / f"{where.name}-{label}.json"
        path.write_text(json.dumps(receipt), encoding="utf-8")
        return self.ok(where, "submit", label, str(path))

    def fork(self):
        a, b = self.tmp / "a", self.tmp / "b"
        shutil.copytree(self.base, a)
        shutil.copytree(self.base, b)
        return a, b

    def key(self, where, label):
        return gp.Ledger(where).claim(label)["key"]

    def forge(self, where, record):
        with (where / "ledger.jsonl").open("ab") as f:
            f.write((json.dumps(dict(record, at="2026-10-09T00:00:00Z"), sort_keys=True) + "\n").encode("utf-8"))

    def refused(self, a, b, reason):
        """`gp merge` refuses with `reason` and leaves both ledgers byte-identical."""
        before = [(d / "ledger.jsonl").read_bytes() for d in (a, b)]
        code, out = self.gp(a, "merge", str(b))
        self.assertEqual(code, 1, out)
        self.assertIn("refused:", out)
        self.assertIn(reason, out)
        self.assertEqual([(d / "ledger.jsonl").read_bytes() for d in (a, b)], before)
        return out

    def held(self, where):
        _, items = gp.state(gp.Ledger(where))
        return {c["label"] for c in gp.Ledger(where).claims() if items[c["key"]]["held"]}

    def test_a_same_version_current_tie(self):
        a, b = self.fork()
        legacy = gp.new_key
        # The pre-guard allocator: the next counter value. Both branches take the same one.
        gp.new_key = lambda ledger, body: 1 + max([c["key"] for c in ledger.claims()], default=0)
        try:
            self.claim(a, "on-a", "sx")
            self.claim(b, "on-b", "sy")
        finally:
            gp.new_key = legacy
        self.assertEqual(self.key(a, "on-a"), self.key(b, "on-b"))
        self.refused(a, b, f"the merged log does not fold: conflicting current bindings: {self.key(a, 'on-a')}")
        # With content-derived keys the same two filings do not collide, and the merge lands.
        a2, b2 = self.tmp / "a2", self.tmp / "b2"
        shutil.copytree(self.base, a2)
        shutil.copytree(self.base, b2)
        self.claim(a2, "on-a", "sx")
        self.claim(b2, "on-b", "sy")
        self.assertNotEqual(self.key(a2, "on-a"), self.key(b2, "on-b"))
        self.assertIn("the merged log folds", self.ok(a2, "merge", str(b2)))

    def test_b_retraction_versus_supersession(self):
        self.claim(self.base, "p", "sx")
        self.submit(self.base, "p", point(x=1))
        self.claim(self.base, "q", "sy")
        self.submit(self.base, "q", point(y=2))
        p, q = self.key(self.base, "p"), self.key(self.base, "q")
        a, b = self.fork()
        self.forge(a, {"op": "retract", "target": p})
        self.forge(b, {"op": "supersede", "target": p, "successor": q})
        for branch in (a, b):  # each branch's log folds alone
            ledger = gp.Ledger(branch)
            plan = dict(gp.surface(ledger), lifecycle=gp.lifecycle_events(ledger.records))
            self.assertEqual(gp.run_profile(plan, guard=True), {"guard": "ok"})
        self.refused(a, b, f"the merged log does not fold: withdrawal and replacement: {p}")
        # A lifecycle record that folds still does not land: the profile does not apply it yet.
        self.refused(self.base, a, "does not apply yet")

    def test_c_conflicting_warrant_contents(self):
        self.claim(self.base, "src", "sy")
        self.submit(self.base, "src", point(y=2))
        self.claim(self.base, "t", "sx")
        a, b = self.fork()
        self.submit(a, "t", point(x=1))
        self.submit(b, "t", {"premises": ["src"], "rule": {"type": "map", "map": {"x": "y - 1"}, "eq_certificates": [
            {"type": "ideal", "cofactors": ["1"], "m": 1, "k": 0}]}})
        self.assertIn("t", self.held(a) & self.held(b))
        self.refused(a, b, f"the merged log does not fold: conflicting warrant contents: {self.key(a, 't')}")
        # Two certificates: the Kernel warrants are equal (receipts are named per claim), so the
        # adapter refuses the different receipt bytes under the one warrant id.
        self.claim(self.base, "u", "sz")
        c, d = self.tmp / "c", self.tmp / "d"
        shutil.copytree(self.base, c)
        shutil.copytree(self.base, d)
        self.submit(c, "u", point(z=1))
        self.submit(d, "u", point(z=-1))
        self.refused(c, d, f"conflicting warrant contents: {self.key(c, 'u')} (the branches support u by "
                           "different receipts)")
        # The fix: one receipt on both branches (the later support wins). Then d holds nothing c
        # lacks, and merging c into d lands with d's (agreed) support still the latest.
        self.submit(c, "u", point(z=-1))
        self.assertIn("nothing to merge", self.ok(c, "merge", str(d)))
        self.assertIn("the merged log folds", self.ok(d, "merge", str(c)))
        u = gp.Ledger(d).supports()[self.key(d, "u")]
        self.assertEqual(u["receipt"], point(z=-1))
        self.assertIn("u", self.held(d))

    def test_d_clean_concurrent_merge(self):
        self.claim(self.base, "shared", "sx")
        self.submit(self.base, "shared", point(x=1))
        a, b = self.fork()
        self.claim(a, "on-a", "sy")
        self.submit(a, "on-a", point(y=2))
        self.claim(b, "on-b", "sw")
        self.submit(b, "on-b", point(w=-3))
        self.claim(a, "same", "sz")  # one claim filed on both branches: one key, one record after
        self.claim(b, "same", "sz")
        self.claim(b, "open-b", "sz")
        held_a, held_b, theirs = self.held(a), self.held(b), (b / "ledger.jsonl").read_bytes()
        keys = {c["key"] for d in (a, b) for c in gp.Ledger(d).claims()}
        self.assertTrue(all(k >= gp.KEY_BASE for k in keys))
        self.assertEqual(self.key(a, "same"), self.key(b, "same"))
        out = self.ok(a, "merge", str(b))
        self.assertIn("merged 3 records (2 claims, 1 supports, 0 refusals); the merged log folds", out)
        self.assertEqual((b / "ledger.jsonl").read_bytes(), theirs)
        merged = gp.Ledger(a)
        self.assertEqual([c["label"] for c in merged.claims()], ["shared", "on-a", "same", "on-b", "open-b"])
        self.assertEqual(self.held(a), held_a | held_b)
        status = self.ok(a, "status")
        for label in ("shared", "on-a", "on-b"):
            self.assertIn(f"held     {label}", status)
        self.assertIn("open     open-b", status)
        self.assertIn("nothing to merge", self.ok(a, "merge", str(b)))


if __name__ == "__main__":
    unittest.main()
