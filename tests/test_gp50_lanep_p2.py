"""GP 0.52 Lane P, phase P2 (docs/private/LANEP-DESIGN.md: the builder's review note's phase 2), on the Mathlib-free
fixture package of tests/test_gp50_lanep.py:

- `comparator_receipt` (tier 1): `gp claim --comparator T` emits the challenge from the registry, and the binder checks
  the challenge's type is the claim's (the emitter is not trusted). A receipt holds only at the pinned revisions
  (decision 3); controls: another pin (recorded only), a log that does not match or does not say okay, another
  theorem, a package changed since Comparator ran, a challenge edited to another type or after the run, a tampered
  stored log. The receipts here are written by the test: what is tested is gp's checking of a receipt, not Comparator
  (the real receipt is the C3b fixture's, tests/test_gp50_lanep_c3b.py).
- the lean4checker replay (`gp bind --replay`): a passing replay makes tier 2 final; a module that skips the kernel
  (`debug.skipKernelTC`) holds a false theorem until the replay catches it, and then no theorem warrant of the package
  holds.
- process conditions: shown as open, and a presentation that leaves them out reads "conditions open", not OVERSTATED;
  a dropped mathematical premise is still OVERSTATED.
- `min_reader`: new init records carry it; a reader older than it refuses the ledger with a clear message.

Bridges (`profile_replay`, tier 3, control 8) need the binding's Mathlib build and are in the second class.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_lanep_p1_tests", ROOT / "tests/test_gp50_lanep.py")
p1 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p1)
gp = p1.gp
BRIDGE_OLEAN = ROOT / "binding/.lake/build/lib/lean/GPBinding/LaneP/Bridge.olean"
MATHLIB = ROOT / "binding/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
OKAY_LOG = b"Exporting ...\nRunning Lean default kernel on solution.\nLean default kernel accepts the solution\n" \
           b"Your solution is okay!\n"
SKIP = """import Lean
import Tiny.Basic

open Lean Elab Command

-- A false theorem the kernel never saw: `A` "proved" by `True.intro`.
set_option debug.skipKernelTC true in
run_cmd liftCoreM do
  addDecl (.thmDecl { name := `Tiny.bad, levelParams := [], type := mkConst `Tiny.A, value := mkConst ``True.intro })
"""


def sha(data):
    return hashlib.sha256(data).hexdigest()


class Base:
    """The P1 fixture (A, B, C; A-of-B, B-held, B-of-C, C-held) plus a Comparator claim A-cmp of A under B. The P1 test
    class's helpers are borrowed, not inherited, so its tests do not run twice."""
    make = staticmethod(p1.LaneP.make)
    gp_at = staticmethod(p1.LaneP.gp_at)
    ok_at = classmethod(p1.LaneP.ok_at.__func__)
    tearDownClass = classmethod(p1.LaneP.tearDownClass.__func__)
    copy, ok, no, lines, held, edit = (p1.LaneP.copy, p1.LaneP.ok, p1.LaneP.no, p1.LaneP.lines, p1.LaneP.held,
                                       p1.LaneP.edit)

    @classmethod
    def setUpClass(cls):
        p1.LaneP.setUpClass.__func__(cls)
        cls.ok_at(cls.base, "claim", "A-cmp", "--lean", "A", "--premise", "B", "--comparator", "Tiny.a_of_b")

    def receipt(self, where, label="A-cmp", log=OKAY_LOG, name="r", **over):
        ledger = gp.Ledger(where)
        ledger.verify_statement()
        s = gp.lanep.pclaim(ledger, label)["support"]
        pins = gp.lanep.comparator_pins()
        r = {"schema": "gp-comparator-receipt/v1", "theorem": s["theorem"], "challenge_module": s["challenge"],
             "solution_module": s["solution"],
             "challenge_sha256": gp.lanep.file_sha(gp.lanep.module_file(ledger, s["challenge"])),
             "tree_sha256": gp.lanep.tree_sha(ledger), "toolchain": pins["toolchain"],
             "comparator_rev": pins["comparator_rev"], "lean4export_rev": pins["lean4export_rev"],
             "landrun_rev": "test", "hardening": "test", "exit": 0, "okay": True, "seconds": 1, "log": f"{name}.log",
             "log_sha256": sha(log)}
        r.update(over)
        d = where / "comparator"
        (d / f"{name}.log").write_bytes(log)
        (d / f"{name}.json").write_bytes(json.dumps(r).encode("utf-8"))
        return str(d / f"{name}.json")


@unittest.skipUnless(p1.have_toolchain(), "the pinned Lean toolchain is not installed")
class LaneP2(Base, unittest.TestCase):
    # --- comparator_receipt ------------------------------------------------------------------------------

    def test_comparator_emission_and_held_tier_1(self):
        c = self.copy("cmp")
        ledger = gp.Ledger(c)
        s = next(r for r in ledger.records if r.get("label") == "A-cmp")["support"]
        chal = (c / "lean" / (s["challenge"].replace(".", "/") + ".lean")).read_bytes().decode("utf-8")
        self.assertIn(f"theorem {s['theorem']} : (Tiny.B) → (Tiny.A) := by sorry", chal)
        cfg = json.loads((c / "comparator" / f"K{s['theorem'].split('.K')[1]}.json").read_bytes())
        self.assertEqual(cfg["theorem_names"], [s["theorem"]])
        self.assertEqual(cfg["permitted_axioms"], ["propext", "Quot.sound", "Classical.choice"])
        self.assertIn("Comparator: no Comparator receipt yet", self.lines(c)["A-cmp"])
        out = self.ok(c, "submit", "A-cmp", "--comparator", self.receipt(c))
        self.assertIn("recorded at the pinned revisions; held; tier 1; open: B", out)
        out = self.ok(c, "explain", "A-cmp")
        self.assertIn("comparator_receipt", out)
        self.assertIn("[tier 1, held]: ok", out)
        self.assertIn("Comparator challenge", self.ok(c, "bind"))
        # The receipt holds through discharge too: A at the weaker tier of the two premises.
        out = self.ok(c, "discharge", "A-cmp", "--premise", "B", "--by", "B-held", "--as", "A-via-cmp")
        self.assertIn("held; tier 2 (unreplayed)", out)
        # Moving the pins turns the receipt into a recorded-only one (decision 3: only the campaign pin holds).
        orig = gp.lanep.comparator_pins
        gp.lanep.comparator_pins = lambda: dict(orig(), comparator_rev="1" * 40)
        try:
            line = self.lines(c)["A-cmp"]
        finally:
            gp.lanep.comparator_pins = orig
        self.assertIn("A-cmp: open; best: tier 1 (Comparator receipt at another pin, recorded only)", line)

    def test_comparator_controls(self):
        c = self.copy("cmp-ctl")
        # Another pin: recorded only (decision 3).
        out = self.ok(c, "submit", "A-cmp", "--comparator", self.receipt(c, name="other", comparator_rev="0" * 40))
        self.assertIn("from another pin: recorded only", out)
        line = self.lines(c)["A-cmp"]
        self.assertIn("A-cmp: open; best: tier 1 (Comparator receipt at another pin, recorded only)", line)
        self.assertIn("only receipts from other pins", line)
        # A log that does not match, a log that does not say okay, another theorem.
        bad = self.receipt(c, name="mismatch", log_sha256="0" * 64)
        self.assertIn("the log does not match", self.no(c, "submit", "A-cmp", "--comparator", bad))
        refused = self.receipt(c, name="refused", log=b"Illegal axiom detected: 'sorryAx'\n")
        self.assertIn("did not accept", self.no(c, "submit", "A-cmp", "--comparator", refused))
        other = self.receipt(c, name="thm", theorem="GPLaneP.K1")
        self.assertIn("not this claim's challenge", self.no(c, "submit", "A-cmp", "--comparator", other))
        # A package changed since Comparator ran.
        stale = self.receipt(c, name="stale")
        self.edit(c, "theorem c_holds : C := rfl", "theorem c_holds : C := rfl\n\ntheorem c_again : C := rfl")
        self.assertIn("changed since Comparator ran", self.no(c, "submit", "A-cmp", "--comparator", stale))
        self.assertFalse(self.held(c, "A-cmp"))

    def test_comparator_challenge_is_checked_not_trusted(self):
        c = self.copy("cmp-emit")
        ledger = gp.Ledger(c)
        s = next(r for r in ledger.records if r.get("label") == "A-cmp")["support"]
        path = c / "lean" / (s["challenge"].replace(".", "/") + ".lean")
        text = path.read_bytes().decode("utf-8")
        # An edited challenge stating another type: a receipt for it is accepted as a record, but the binder's check
        # that the challenge's type is the claim's fails, so the claim is not held.
        path.write_bytes(text.replace("(Tiny.B) → (Tiny.A)", "(Tiny.C)").encode("utf-8"))
        self.ok(c, "submit", "A-cmp", "--comparator", self.receipt(c))
        self.assertIn("the challenge's type is not the claim's", self.lines(c)["A-cmp"])
        self.assertIn("NOT the claim's type", self.ok(c, "bind"))
        # Restored: held. Edited after the run (same type, other bytes): not held.
        path.write_bytes(text.encode("utf-8"))
        self.ok(c, "submit", "A-cmp", "--comparator", self.receipt(c, name="r2"))
        self.assertTrue(self.held(c, "A-cmp"))
        path.write_bytes((text + "\n-- edited after the run\n").encode("utf-8"))
        self.assertIn("the challenge file changed since Comparator ran", self.lines(c)["A-cmp"])
        path.write_bytes(text.encode("utf-8"))
        self.assertTrue(self.held(c, "A-cmp"))
        # A stored log tampered after submission: every command refuses (receipt custody).
        w = [r for r in gp.Ledger(c).records if r["op"] == "pwarrant" and r.get("kind") == "comparator"][-1]
        (c / w["log"]["path"]).write_bytes(b"Your solution is okay!\nforged\n")
        self.assertIn("does not match its recorded SHA-256", self.no(c, "status"))

    # --- the lean4checker replay -------------------------------------------------------------------------

    def test_replay_and_skip_kernel_control(self):
        c = self.copy("replay")
        out = self.ok(c, "bind", "--replay")
        self.assertIn("replayed", out)
        self.assertIn("tier 2 is final", out)
        lines = self.lines(c)
        self.assertTrue(lines["B-held"].startswith("B-held: held; tier 2;"), lines["B-held"])
        self.assertNotIn("unreplayed", lines["A-of-B"])
        # A module that skips the kernel: its false theorem holds A until the replay catches it.
        (c / "lean/Tiny/Skip.lean").write_bytes(SKIP.encode("utf-8"))
        out = self.ok(c, "claim", "A-bad", "--lean", "A", "--theorem", "Tiny.bad")
        self.assertIn("held; tier 2 (unreplayed)", out)  # the residual gap, as the design names it
        out = self.no(c, "bind", "--replay")
        self.assertIn("the lean4checker replay failed", out)
        self.assertIn("Tiny.bad", out)
        lines = self.lines(c)
        for label in ("A-bad", "B-held", "A-of-B"):
            self.assertFalse(lines[label].split(": ", 1)[1].startswith("held"), lines[label])
        self.assertIn("the lean4checker replay of this package failed", lines["B-held"])
        # Removing the module restores the tree the first replay passed on: held, and tier 2 is final again.
        (c / "lean/Tiny/Skip.lean").unlink()
        lines = self.lines(c)
        self.assertTrue(lines["B-held"].startswith("B-held: held; tier 2;"), lines["B-held"])
        self.assertIn("the theorem is missing from the package", lines["A-bad"])

    # --- process conditions --------------------------------------------------------------------------------

    def test_process_conditions(self):
        c = self.copy("proc")
        self.ok(c, "register", "--prose", "a peer reviewer reads the proof", "--as", "peer review",
                "--process", "review")
        self.ok(c, "register", "--prose", "the branch is merged", "--as", "merge", "--process", "merge")
        self.assertIn("not a mathematical premise",
                      self.no(c, "claim", "X", "--lean", "B", "--premise", "peer review", "--theorem", "Tiny.b_holds"))
        self.assertIn("is not a process condition", self.no(c, "claim", "X", "--lean", "B", "--condition", "C"))
        out = self.ok(c, "claim", "B-rev", "--lean", "B", "--condition", "peer review", "--theorem", "Tiny.b_holds")
        self.assertIn("held; tier 2 (unreplayed); conditions open: peer review", out)
        out = self.ok(c, "present", "B-rev", "--venue", "abstract", "--tag", "LEAN")
        self.assertNotIn("OVERSTATED", out)
        self.ok(c, "present", "B-rev", "--venue", "paper", "--tag", "LEAN", "--premise", "peer review")
        self.assertIn("presented [LEAN] in 2 venues (1 conditions open)", self.lines(c)["B-rev"])
        self.assertIn("presented in abstract as [LEAN] stating no premises: conditions open (peer review)",
                      self.ok(c, "explain", "B-rev"))
        # A tag above the earned tier, or a dropped mathematical premise, is still OVERSTATED.
        self.assertIn("OVERSTATED", self.ok(c, "present", "B-rev", "--venue", "slides", "--tag", "COMPARATOR"))
        self.assertIn("OVERSTATED", self.ok(c, "present", "A-of-B", "--venue", "talk", "--tag", "LEAN"))
        # A hand proof's reviewer condition that is a process condition: open, not OVERSTATED when left out.
        self.ok(c, "claim", "C-open", "--lean", "C")
        proof = c / "proof.md"
        proof.write_bytes(b"base + 1 = 4.\n")
        out = self.ok(c, "submit", "C-open", "--hand-proof", str(proof), "--state", "complete", "--condition", "merge")
        self.assertIn("conditions open: merge", out)
        self.assertNotIn("OVERSTATED", self.ok(c, "present", "C-open", "--venue", "note", "--tag", "HAND"))
        self.assertIn("open process conditions", self.ok(c, "frontier"))
        # A discharge keeps the open process conditions of what it rests on.
        self.ok(c, "claim", "A-rev", "--lean", "A", "--premise", "B", "--condition", "merge", "--theorem", "Tiny.a_of_b")
        out = self.ok(c, "discharge", "A-rev", "--premise", "B", "--by", "B-rev", "--as", "A-rev-d")
        self.assertIn("held; tier 2 (unreplayed); conditions open: merge, peer review", out)

    # --- min_reader ----------------------------------------------------------------------------------------

    def test_min_reader(self):
        c = self.copy("reader")
        path = c / "ledger.jsonl"
        rows = [json.loads(l) for l in path.read_bytes().decode("utf-8").splitlines() if l.strip()]
        self.assertEqual(rows[0]["min_reader"], gp.GP_VERSION)
        for need, msg in (("99.0.0", "this ledger needs gp 99.0.0 or later to read it"),
                          ("soon", "this ledger needs gp soon or later")):
            rows[0]["min_reader"] = need
            path.write_bytes("".join(json.dumps(r, sort_keys=True) + "\n" for r in rows).encode("utf-8"))
            self.assertIn(msg, self.no(c, "status"))
        del rows[0]["min_reader"]  # an older ledger: no min_reader, read as before
        path.write_bytes("".join(json.dumps(r, sort_keys=True) + "\n" for r in rows).encode("utf-8"))
        self.ok(c, "status")


@unittest.skipUnless(p1.have_toolchain() and BRIDGE_OLEAN.exists() and MATHLIB.exists(),
                     "the binding's Lane P bridge module or Mathlib is not built here")
class Bridges(unittest.TestCase):
    """profile_replay (tier 3) and control 8: a P code generated as the literal meaning of a held 3a claim."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        cls.three = cls.tmp / "threeA"
        cls.three.mkdir()
        shutil.copy(ROOT / "campaigns/3p-matroids/campaign.json", cls.three / "campaign.json")
        (cls.tmp / "sx.json").write_bytes(json.dumps({"variables": ["x"], "equations": ["x - 1"], "nonzero": []}).encode())
        (cls.tmp / "rx.json").write_bytes(json.dumps({"certificate": {"type": "point", "point": {"x": "1"}}}).encode())
        cls.run_ok(cls.three, "init")
        cls.run_ok(cls.three, "claim", "p", "--system", str(cls.tmp / "sx.json"), "--kind", "NONEMPTY", "--char0")
        cls.run_ok(cls.three, "submit", "p", str(cls.tmp / "rx.json"))
        cls.run_ok(cls.three, "claim", "q", "--system", str(cls.tmp / "sx.json"), "--kind", "EMPTY", "--char0")
        cls.pc = cls.make(cls.tmp / "pc")
        cls.run_ok(cls.pc, "init")
        out = cls.run_ok(cls.pc, "register", "--bridge", f"{cls.three.as_posix()}:p", "--as", "Pt")
        assert "the kernel confirmed it" in out, out
        cls.run_ok(cls.pc, "register", "--bridge", f"{cls.three.as_posix()}:q", "--as", "Qt")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    @staticmethod
    def make(where):
        binding = (ROOT / "binding").resolve()
        pkg = where / "lean"
        (pkg / "BridgeP").mkdir(parents=True)
        (pkg / "lakefile.toml").write_bytes(
            (f'name = "bridgep"\nversion = "0.1.0"\ndefaultTargets = ["BridgeP"]\n'
             f'packagesDir = "{(binding / ".lake/packages").as_posix()}"\n\n'
             f'[[require]]\nname = "gp_binding"\npath = "{binding.as_posix()}"\n\n'
             f'[[lean_lib]]\nname = "BridgeP"\nglobs = ["BridgeP.+"]\n').encode("utf-8"))
        m = json.loads((binding / "lake-manifest.json").read_bytes())
        packages = [{"type": "path", "scope": "", "name": "gp_binding", "manifestFile": "lake-manifest.json",
                     "inherited": False, "dir": binding.as_posix(), "copy": False, "configFile": "lakefile.toml"}]
        for q in m["packages"]:
            q = dict(q, inherited=True)
            if q["type"] == "path":
                q["dir"] = (binding / q["dir"]).resolve().as_posix()
            packages.append(q)
        (pkg / "lake-manifest.json").write_bytes(json.dumps(
            {"version": "1.3.0", "packagesDir": (binding / ".lake/packages").as_posix(), "packages": packages,
             "name": "bridgep", "lakeDir": ".lake", "fixedToolchain": False}, indent=1).encode("utf-8"))
        shutil.copy(ROOT / "profile/lean-toolchain", pkg / "lean-toolchain")
        (pkg / "BridgeP/Basic.lean").write_bytes(b"namespace BridgeP\n\ndef T : Prop := True\n\nend BridgeP\n")
        (where / "campaign.json").write_bytes(json.dumps(
            {"name": "bridgep", "profile": "P", "package": "lean", "roots": ["BridgeP"]}).encode("utf-8"))
        return where

    @classmethod
    def run_ok(cls, where, *args):
        code, out = p1.LaneP.gp_at(where, *args)
        assert code == 0, out
        return out

    def copy(self, name):
        dest = self.tmp / name
        shutil.copytree(self.pc, dest)
        three = self.tmp / f"{name}-threeA"
        shutil.copytree(self.three, three)
        # The copy bridges to its own copy of the 3a campaign.
        f = dest / "ledger.jsonl"
        f.write_bytes(f.read_bytes().replace(b'"../threeA"', f'"../{name}-threeA"'.encode()))
        return dest, three

    def lines(self, where):
        code, out = p1.LaneP.gp_at(where, "status")
        self.assertEqual(code, 0, out)
        return {l.split(": ", 1)[0]: l for l in out.splitlines() if ": " in l}

    def test_bridge_held_tier_3_and_control_8(self):
        c, three = self.copy("b8")
        out = self.run_ok(c, "claim", "Pt-held", "--lean", "Pt", "--bridge", "p")
        self.assertIn("Pt; held; tier 3", out)
        self.assertIn("profile_replay of ../b8-threeA:p [tier 3, held]: ok", self.run_ok(c, "explain", "Pt-held"))
        # The bridged claim q is not held in its campaign: neither is its bridge.
        out = self.run_ok(c, "claim", "Qt-open", "--lean", "Qt", "--bridge", "q")
        self.assertIn("bridge: the bridged claim q of ../b8-threeA is not held there", out)
        # Control 8: a withdrawn bridged 3a claim un-holds the P claim.
        self.run_ok(three, "withdraw", "p", "--reason", "control 8")
        line = self.lines(c)["Pt-held"]
        self.assertIn("Pt-held: open; bridge: the bridged claim p is withdrawn in ../b8-threeA", line)

    def test_bridge_verdict_cache(self):
        # 0.54: the bridge's verdict (`bridgeOk`, the runner's re-fold of the bridged part) is cached by the SHA-256
        # of the bridge input; the fold gets it as the runner's own bridge record, so the verdicts are the ones the
        # fold gets when it re-folds the bridged part itself.
        c, three = self.copy("bc")
        self.run_ok(c, "claim", "Pt-held", "--lean", "Pt", "--bridge", "p")
        self.run_ok(c, "claim", "Qt-open", "--lean", "Qt", "--bridge", "q")
        calls = []
        orig = gp.lanep.run_runner
        gp.lanep.run_runner = lambda p, mode="run": calls.append(mode) or orig(p, mode)
        try:
            first = self.lines(c)
            self.assertEqual(calls.count("bridge"), 0)  # filing the claims cached both verdicts
            ledger = gp.Ledger(c)
            ledger.verify_statement()
            plan = gp.lanep.plan(ledger, gp.lanep.current_report(ledger))
            bridges = []
            for k in sorted(r["stmt"] for r in plan["records"] if r["declaration"].startswith("bridge:")):
                reg = gp.lanep.code_by_id(ledger)[k]
                bridges.append({"code": k, "lit": reg["bridge"]["lit"], "plan": gp.lanep.bridged_plan(ledger, reg)})
            old = dict(plan, records=[r for r in plan["records"] if not r["declaration"].startswith("bridge:")],
                       bridges=bridges)
            self.assertEqual(len(bridges), 2)
            self.assertEqual(orig(old)["items"], orig(plan)["items"])  # the 0.53 plan (re-folded in the run): same
            os.environ["GP_NO_CACHE"] = "1"
            try:
                self.assertEqual(self.lines(c), first)
            finally:
                del os.environ["GP_NO_CACHE"]
            self.assertEqual(calls.count("bridge"), 2)
        finally:
            gp.lanep.run_runner = orig
        self.assertTrue(first["Pt-held"].startswith("Pt-held: held; tier 3"))
        self.assertTrue(first["Qt-open"].startswith("Qt-open: open"))
        # A change to the bridged campaign is a new bridge input: re-folded, not served from the cache (control 8).
        self.run_ok(three, "withdraw", "p", "--reason", "control 8")
        self.assertIn("Pt-held: open; bridge: the bridged claim p is withdrawn", self.lines(c)["Pt-held"])

    def test_bridge_refusals_and_tampering(self):
        c, three = self.copy("bt")
        code, out = p1.LaneP.gp_at(c, "claim", "X", "--lean", "Pt", "--bridge", "q")
        self.assertEqual(code, 1, out)
        self.assertIn("Pt bridges ../bt-threeA:p, not q", out)
        code, out = p1.LaneP.gp_at(c, "register", "--bridge", f"{c.as_posix()}:x", "--as", "Self")
        self.assertEqual(code, 1, out)
        self.assertIn("is a Lane P campaign", out)
        self.run_ok(c, "claim", "Pt-held", "--lean", "Pt", "--bridge", "p")
        # A register record whose literal is not the definition's (appended by hand): the binder refuses it.
        rows = [json.loads(l) for l in (c / "ledger.jsonl").read_bytes().decode("utf-8").splitlines() if l.strip()]
        reg = next(r for r in rows if r["op"] == "register" and r["name"] == "Pt")
        lit_q = next(r for r in rows if r["op"] == "register" and r["name"] == "Qt")["bridge"]["lit"]
        forged = dict(reg, code=reg["code"] + 1, name="Pt-forged", bridge=dict(reg["bridge"], lit=lit_q))
        claim = {"op": "pclaim", "key": 4242, "label": "forged", "stmt": forged["code"], "premises": [],
                 "support": {"kind": "bridge"}}
        with (c / "ledger.jsonl").open("ab") as f:
            for r in (forged, claim):
                f.write((json.dumps(r, sort_keys=True) + "\n").encode("utf-8"))
        line = self.lines(c)["forged"]
        self.assertIn("forged: open; bridge: the binder did not confirm", line)
        self.assertIn("is not `meaning3` of this literal", line)
        # An edited generated file: the code's closure changes, so its claims are unbound.
        gen = c / "lean/BridgeP/GPBridge/Pt.lean"
        gen.write_bytes(gen.read_bytes().replace(b"Do not edit", b"Do not edit (edited)") +
                        b"\ndef BridgeP.GPBridge.extra : Prop := True\n")
        self.assertTrue(self.lines(c)["Pt-held"].startswith("Pt-held: held"))  # a comment and a new def: same closure
        gen.write_bytes(gen.read_bytes().replace(b"x - 1", b"x - 2"))
        self.assertIn("unbound (Pt was redefined", self.lines(c)["Pt-held"])

    def test_bridge_needs_the_binding_pin(self):
        where = self.tmp / "nopin"
        self.make(where)
        lf = where / "lean/lakefile.toml"
        text = lf.read_bytes().decode("utf-8")
        block = text[text.index("[[require]]"):text.index("[[lean_lib]]")]
        lf.write_bytes(text.replace(block, "").encode("utf-8"))
        self.run_ok(where, "init")
        code, out = p1.LaneP.gp_at(where, "register", "--bridge", f"{self.three.as_posix()}:p", "--as", "Pt")
        self.assertEqual(code, 1, out)
        self.assertIn("does not require the binding", out)



if __name__ == "__main__":
    unittest.main()
