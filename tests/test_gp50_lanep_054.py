"""GP 0.54 Lane P fixes (defects a trial found) and speed, on the Mathlib-free fixture package of tests/test_gp50_lanep.py
(with its P2 Comparator claim A-cmp, tests/test_gp50_lanep_p2.py). Each fix has a regression test that fails before it:

1. A replay that could not run (an unreadable or missing file) is not a kernel rejection: it is reported as "replay
   could not run ... retry", recorded as an attempt, and withholds nothing; a 0.53 record of such a failure no longer
   outranks a passing replay of the same tree; a kernel rejection still sticks until the tree changes.
2. An emitted Comparator Solution imports the closure of the solution theorem's own module (and the statement
   modules), not every module of the package; a closure that reaches a bridge module is said and recorded.
3. Recorded-only files are re-hashed on every view: an edited one shows "changed since recorded" and no longer counts,
   a missing one shows "missing", until it is re-submitted.
4. A wrong theorem (the kernel refuses its type) is a refusal: the full expected and actual types, exit 1, nothing
   filed.

Speed: a bind reuses the rows earlier binds of the same environment reported; `gp register --batch` (or several
declarations) registers N statements with one bind. The bridge verdict cache is tested with the bridges
(tests/test_gp50_lanep_p2.py, Bridges).
"""
import importlib.util
import json
from pathlib import Path
import re
import shutil
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_lanep_p2_tests_054", ROOT / "tests/test_gp50_lanep_p2.py")
p2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2)
p1, gp = p2.p1, p2.gp

MORE = """import Tiny.Basic

namespace Tiny

def D : Prop := base ≠ 0

def E : Prop := 0 < base

def F : Prop := base < 4

def G : Prop := base ≤ 3

def H : Prop := 3 ≤ base

def I : Prop := base * 1 = 3

theorem a_holds : A := rfl

end Tiny
"""
# leanchecker's own words when it could not read a Mathlib file under load (gp 0.53 recorded this as a kernel failure)
IO_FAIL = ["leanchecker found a problem in Tiny.Basic",
         "uncaught exception: failed to read file '/work/binding/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/"
         "GroupTheory/OreLocalization/Basic.olean.private'"]
KERNEL = ["leanchecker found a problem in Tiny.Skip", "uncaught exception: while replaying declaration 'Tiny.bad':",
          "(kernel) declaration type mismatch, 'Tiny.bad' has type", "  True", "but it is expected to have type",
          "  Tiny.A"]


@unittest.skipUnless(p1.have_toolchain(), "the pinned Lean toolchain is not installed")
class Fixes054(p2.Base, unittest.TestCase):
    key, append = p1.LaneP.key, p1.LaneP.append

    def records(self, where, op=None):
        return [r for r in gp.Ledger(where).records if op is None or r["op"] == op]

    def write(self, where, rel, text):
        path = where / "lean" / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.encode("utf-8"))

    # --- 1. replay: an infrastructure failure is not a kernel rejection ---------------------------------------

    def test_replay_that_could_not_run_withholds_nothing(self):
        c = self.copy("r-infra")
        self.ok(c, "bind")
        olean = c / "lean/.lake/build/lib/lean/Tiny/Basic.olean"
        aside = olean.with_name("Basic.olean.aside")
        olean.rename(aside)  # leanchecker cannot read a file the build made: an I/O failure, not a kernel verdict
        try:
            code, out = self.gp_at(c, "bind", "--replay")
        finally:
            aside.rename(olean)
        self.assertEqual(code, 1, out)
        self.assertIn("replay could not run: leanchecker exited", out)
        self.assertIn("retry", out)
        self.assertIn("this is not a kernel rejection", out)
        self.assertNotIn("skipKernelTC", out)
        self.assertEqual(self.records(c, "replay"), [])
        self.assertEqual([r["status"] for r in self.records(c, "pattempt")], ["replay could not run"])
        lines = self.lines(c)
        self.assertTrue(lines["B-held"].startswith("B-held: held; tier 2 (unreplayed)"), lines["B-held"])
        self.assertTrue(lines["A-of-B"].startswith("A-of-B: held"), lines["A-of-B"])
        # The retry passes and tier 2 is final.
        self.assertIn("tier 2 is final", self.ok(c, "bind", "--replay"))
        self.assertTrue(self.lines(c)["B-held"].startswith("B-held: held; tier 2;"))

    def test_replay_latest_completed_decides(self):
        c = self.copy("r-legacy")
        self.ok(c, "bind", "--replay")
        passed = self.records(c, "replay")[-1]
        same = {k: passed[k] for k in ("checker", "tree_sha256", "stamp", "modules")}
        # A 0.53 record of a replay that could not read a file (recorded as failed) beside a passing replay of the same
        # tree: it is not a kernel rejection, so the pass decides.
        self.append(c, dict(same, op="replay", ok=False, seconds=1.0, detail=IO_FAIL))
        lines = self.lines(c)
        self.assertTrue(lines["B-held"].startswith("B-held: held; tier 2;"), lines["B-held"])
        self.assertTrue(lines["A-of-B"].startswith("A-of-B: held; tier 2;"), lines["A-of-B"])
        # A kernel rejection of the same tree (0.53 form: no class, the kernel's words) withholds every theorem
        # warrant, and a later passing replay of the same tree does not clear it: only a changed tree does.
        self.append(c, dict(same, op="replay", ok=False, seconds=1.0, detail=KERNEL))
        self.append(c, dict(same, op="replay", ok=True, seconds=2.0))
        lines = self.lines(c)
        self.assertFalse(lines["B-held"].split(": ", 1)[1].startswith("held"), lines["B-held"])
        self.assertIn("the lean4checker replay of this package failed", lines["B-held"])
        self.append(c, dict(same, op="replay", ok=False, seconds=1.0, detail=IO_FAIL, **{"class": "infrastructure"}))
        self.assertFalse(self.held(c, "B-held"))

    # --- 2. the Comparator solution's imports ---------------------------------------------------------------

    def test_comparator_solution_imports_the_theorems_closure(self):
        c = self.copy("cmp-closure")
        self.write(c, "Tiny/Extra.lean", "namespace Tiny\n\ntheorem extra : True := trivial\n\nend Tiny\n")
        self.write(c, "Tiny/GPBridge/Fake.lean", "namespace Tiny.GPBridge\n\ndef fake : Prop := True\n\nend Tiny.GPBridge\n")
        self.write(c, "Tiny/UsesBridge.lean", "import Tiny.Basic\nimport Tiny.GPBridge.Fake\n\nnamespace Tiny\n\n"
                                              "theorem c_via : C := c_holds\n\nend Tiny\n")

        def imports(label):
            s = next(r for r in self.records(c) if r.get("label") == label)["support"]
            text = (c / "lean" / (s["solution"].replace(".", "/") + ".lean")).read_bytes().decode("utf-8")
            return re.findall(r"^import (\S+)$", text, re.M), s

        out = self.ok(c, "claim", "C-cmp", "--lean", "C", "--comparator", "Tiny.c_holds")
        mods, s = imports("C-cmp")
        self.assertEqual(mods, ["Tiny.Basic"])  # not Tiny.Extra, Tiny.UsesBridge or the bridge module
        self.assertNotIn("needs the binding", out)
        self.assertNotIn("needs_binding", s)
        out = self.ok(c, "claim", "C-cmp2", "--lean", "C", "--comparator", "Tiny.c_via")
        mods, s = imports("C-cmp2")
        self.assertEqual(mods, ["Tiny.Basic", "Tiny.UsesBridge"])
        self.assertIn("C-cmp2 needs the binding: the import closure of Tiny.c_via includes Tiny.GPBridge.Fake", out)
        self.assertEqual(s["needs_binding"], ["Tiny.GPBridge.Fake"])
        self.assertIn("needs the binding (Tiny.GPBridge.Fake)", self.ok(c, "explain", "C-cmp2"))
        # A solution theorem of another statement is refused before anything is emitted.
        before = sorted(p.name for p in (c / "comparator").iterdir())
        code, out = self.gp_at(c, "claim", "C-cmp3", "--lean", "C", "--comparator", "Tiny.b_holds")
        self.assertEqual(code, 1, out)
        self.assertIn("does not prove the claim's statement", out)
        self.assertEqual(sorted(p.name for p in (c / "comparator").iterdir()), before)

    def test_comparator_solution_after_a_053_bind(self):
        # The trial campaign's shape: statements in one module, the proof in Proofs/, a bridge module in the package,
        # and the proof already held by a lean_theorem claim whose bind was recorded by the 0.53 binder (theorem rows
        # without a module). The Comparator claim's bind then matches that recorded bind exactly.
        c = self.copy("cmp-053")
        self.write(c, "Tiny/GPBridge/Fake.lean", "namespace Tiny.GPBridge\n\ndef fake : Prop := True\n\nend Tiny.GPBridge\n")
        self.write(c, "Tiny/Proofs/Graph.lean", "import Tiny.Basic\n\nnamespace Tiny\n\ntheorem c_graph : C := c_holds\n\n"
                                                "end Tiny\n")
        self.ok(c, "claim", "C-graph", "--lean", "C", "--theorem", "Tiny.c_graph")
        ledger = gp.Ledger(c)
        rows = []
        for r in ledger.records:
            if r["op"] == "bind":
                rep = gp.lanep.load_report(ledger, r)
                for t in rep["theorems"].values():
                    t.pop("module", None)
                r = dict(r, report=ledger.store_receipt(rep))
            rows.append(r)
        (c / "ledger.jsonl").write_bytes(b"".join((json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n").encode()
                                                 for r in rows))
        binds = len(self.records(c, "bind"))
        out = self.ok(c, "claim", "C-cmp-053", "--lean", "C", "--comparator", "Tiny.c_graph")
        self.assertNotIn("needs the binding", out)
        s = next(r for r in self.records(c) if r.get("label") == "C-cmp-053")["support"]
        text = (c / "lean" / (s["solution"].replace(".", "/") + ".lean")).read_bytes().decode("utf-8")
        self.assertEqual(re.findall(r"^import (\S+)$", text, re.M), ["Tiny.Basic", "Tiny.Proofs.Graph"])
        self.assertEqual(len(self.records(c, "bind")), binds + 1)  # the module lookup records nothing; the claim binds

    # --- 3. recorded-only files are re-hashed ---------------------------------------------------------------

    def test_recorded_files_are_rehashed(self):
        c = self.copy("rehash")
        self.ok(c, "claim", "C-hand", "--lean", "C")
        proof = c / "proofs/c.md"
        proof.parent.mkdir()
        proof.write_bytes(b"C: base + 1 = 4 since base = 3.\n")
        self.ok(c, "submit", "C-hand", "--hand-proof", str(proof), "--state", "complete")
        num = c / "proofs/c.csv"
        num.write_bytes(b"base,4\n3,4\n")
        self.ok(c, "submit", "C-hand", "--numerical", str(num))
        line = self.lines(c)["C-hand"]
        self.assertTrue(line.startswith("C-hand: open; best: tier 5 (hand proof (complete), recorded only)"), line)
        self.assertNotIn("RECORDED", line)
        # Edited after submission: it no longer counts as that evidence (the numerical record still does).
        proof.write_bytes(b"C: edited after submission.\n")
        line = self.lines(c)["C-hand"]
        self.assertTrue(line.startswith("C-hand: open; best: tier 6 (numerical, recorded only)"), line)
        self.assertIn("hand proof (complete) proofs/c.md CHANGED SINCE RECORDED: not counted (re-submit it)", line)
        out = self.ok(c, "explain", "C-hand")
        self.assertIn("proofs/c.md sha256", out)
        self.assertIn("CHANGED SINCE RECORDED: not counted until re-submitted", out)
        # Missing: shown as missing.
        num.unlink()
        line = self.lines(c)["C-hand"]
        self.assertIn("numerical proofs/c.csv MISSING: not counted (re-submit it)", line)
        self.assertFalse(line.startswith("C-hand: open; best: tier"), line)
        # Re-submitted: it counts again.
        self.ok(c, "submit", "C-hand", "--hand-proof", str(proof), "--state", "complete")
        line = self.lines(c)["C-hand"]
        self.assertTrue(line.startswith("C-hand: open; best: tier 5 (hand proof (complete), recorded only)"), line)
        # A locator outside the campaign never counts.
        k = self.key(c, "C-hand")
        self.append(c, {"op": "pwarrant", "key": k, "label": "C-hand", "kind": "exact_script", "locator": "../x.txt",
                        "sha256": "0" * 64})
        self.assertIn("exact script ../x.txt MISSING", self.lines(c)["C-hand"])

    # --- 4. a wrong theorem is a full refusal ----------------------------------------------------------------

    def test_wrong_theorem_refused_in_full(self):
        c = self.copy("wrong")
        code, out = self.gp_at(c, "claim", "A-wrong", "--lean", "A", "--theorem", "Tiny.c_holds")
        self.assertEqual(code, 1, out)
        self.assertIn("refused: theorem Tiny.c_holds refused for A: the kernel refused its type: Tiny.c_holds does not "
                      "prove the claim's statement; expected (the claim's type): Tiny.A; actual (Tiny.c_holds's type): "
                      "Tiny.C", out)
        self.assertIn("smallest fix: give a theorem whose type is exactly A", out)
        self.assertNotIn("_gp_lanep_check", out)
        code, out = self.gp_at(c, "claim", "A-wrong2", "--lean", "A", "--premise", "C", "--theorem", "Tiny.a_of_b")
        self.assertEqual(code, 1, out)
        self.assertIn("expected (the claim's type): Tiny.C → Tiny.A; actual (Tiny.a_of_b's type): Tiny.B → Tiny.A", out)
        self.assertFalse(any(r.get("label", "").startswith("A-wrong") for r in self.records(c)))
        # An appended claim naming a wrong theorem (0.53 filed these): its status line carries both types.
        stmt = next(r for r in self.records(c, "register") if r["name"] == "A")["code"]
        self.append(c, {"op": "pclaim", "key": 9002, "label": "A-old", "stmt": stmt, "premises": [],
                        "support": {"kind": "theorem", "decl": "Tiny.c_holds"}})
        line = self.lines(c)["A-old"]
        self.assertIn("expected (the claim's type): Tiny.A; actual (Tiny.c_holds's type): Tiny.C", line)

    # --- speed: row reuse and batch registration ---------------------------------------------------------------

    def test_batch_register_and_row_reuse(self):
        c = self.copy("batch")
        self.write(c, "Tiny/More.lean", MORE)
        self.ok(c, "status")  # binds the changed tree once
        binds = len(self.records(c, "bind"))
        batch = c / "batch.txt"
        batch.write_bytes(b"# two statements, one bind\nTiny.D\nTiny.E Epos\n")
        out = self.ok(c, "register", "--batch", str(batch))
        self.assertIn("registered D (code", out)
        self.assertIn("registered Epos (code", out)
        self.assertIn("2 Lean statements bound in one bind", out)
        new = self.records(c, "bind")[binds:]
        self.assertEqual(len(new), 1)
        self.assertEqual(new[0]["rows"], {"bound": 2, "reused": 8})  # only D and E were bound; 8 rows were reused
        # A batch with a problem registers nothing, and says every problem.
        batch.write_bytes(b"Tiny.F\nTiny.Nope\nTiny.base\n")
        code, out = self.gp_at(c, "register", "--batch", str(batch))
        self.assertEqual(code, 1, out)
        self.assertIn("the batch was not registered: 2 problems", out)
        self.assertIn("Tiny.Nope is not a declaration of the campaign package", out)
        self.assertIn("Tiny.base is not a campaign-local", out)
        self.assertNotIn("F", [r["name"] for r in self.records(c, "register")])
        # Rerunning with the problems fixed builds and binds nothing: every row was bound by the refused batch.
        built = []
        orig = gp.lanep.run_capped
        gp.lanep.run_capped = lambda *a, **k: built.append(a) or orig(*a, **k)
        try:
            self.assertIn("registered F (code", self.ok(c, "register", "Tiny.F"))
        finally:
            gp.lanep.run_capped = orig
        self.assertEqual(built, [])
        self.assertEqual(self.records(c, "bind")[-1]["seconds"], {"build": 0, "bind": 0})
        # A new theorem claim binds one row (and the code its type needs) and reuses the rest.
        out = self.ok(c, "claim", "A-held", "--lean", "A", "--theorem", "Tiny.a_holds")
        self.assertIn("held; tier 2 (unreplayed)", out)
        rows = self.records(c, "bind")[-1]["rows"]
        self.assertEqual(rows["bound"], 2)  # the theorem row and code A
        self.assertGreater(rows["reused"], 8)
        # Several declarations in one call, and a JSON batch with prose.
        self.assertIn("2 Lean statements bound in one bind", self.ok(c, "register", "Tiny.G", "Tiny.H"))
        path = c / "batch.json"
        path.write_bytes(json.dumps([{"decl": "Tiny.I", "as": "Ipos"}, {"prose": "a referee reads it", "as": "ref",
                                                                          "process": "review"}]).encode("utf-8"))
        out = self.ok(c, "register", "--batch", str(path))
        self.assertIn("registered Ipos (code", out)
        self.assertIn("registered ref (code", out)
        # The reused rows give exactly the status a fresh bind of every row gives.
        reused = self.ok(c, "status")
        fresh = c.with_name("batch-fresh")
        shutil.copytree(c, fresh)
        led = fresh / "ledger.jsonl"
        led.write_bytes(b"".join(l + b"\n" for l in led.read_bytes().splitlines() if b'"op": "bind"' not in l))
        self.assertEqual(self.ok(fresh, "status"), reused)
        self.assertEqual(self.records(fresh, "bind")[-1]["rows"]["reused"], 0)


if __name__ == "__main__":
    unittest.main()
