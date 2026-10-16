"""GP 0.52 Lane P, phase P1: the controls of the Lane P design (§8(c), controls 1-7 and 9), through the `gp` CLI, the P
binder `gp_bindp` and the P runner `gp_ledgerp`, on a Mathlib-free fixture package written here.

Each control must leave the claim not held, or refuse:
1. a renamed declaration; 2. a redefined dependency (the message names the changed constant); 3. an edited ledger
hash, a stale environment stamp, or a tampered bind report; 4. discharge by an unheld claim, by a different statement
(code mismatch) or by a claim with extra premises, through the CLI and as hand-appended records; 5. hand-appended
records (a recorded-only warrant, a claim naming a refused theorem); 6. `sorry`, `native_decide` and a custom axiom;
7. a withdrawn premise claim (refused without --cascade, which lists the discharge that loses its hold); 9. both
merge orders give the same status. Also: the held positives, prose never holdable, OVERSTATED presentations and
fidelity, and that P commands need a P campaign.

Needs the pinned Lean toolchain (the package builds in seconds); skipped without it.
"""
import io
import importlib.util
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_cli_lanep", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

PIN = (ROOT / "profile/lean-toolchain").read_text(encoding="utf-8").strip()
LAKEFILE = 'name = "tiny"\nversion = "0.1.0"\ndefaultTargets = ["Tiny"]\n\n[[lean_lib]]\nname = "Tiny"\nglobs = ["Tiny.+"]\n'
MANIFEST = ('{"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [], "name": "tiny", "lakeDir": ".lake", '
            '"fixedToolchain": false}\n')
BASIC = """namespace Tiny

def base : Nat := 3

def A : Prop := base = 3

def B : Prop := 2 ≤ base

def C : Prop := base + 1 = 4

theorem a_of_b : B → A := fun _ => rfl

theorem b_holds : B := by unfold B base; decide

theorem b_of_c : C → B := fun _ => by unfold B base; decide

theorem c_holds : C := rfl

theorem a_sorry : A := sorry

axiom cheat : A

theorem a_axiom : A := cheat

theorem c_native : C := by unfold C base; native_decide

end Tiny
"""


def have_toolchain():
    try:
        gp.toolchain_lake()
        return True
    except gp.Refusal:
        return False


@unittest.skipUnless(have_toolchain(), "the pinned Lean toolchain is not installed")
class LaneP(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        cls.base = cls.make(cls.tmp / "base")
        cls.ok_at(cls.base, "init")
        for decl in ("Tiny.A", "Tiny.B", "Tiny.C"):
            cls.ok_at(cls.base, "register", decl)
        cls.ok_at(cls.base, "register", "--prose", "the reviewer's second reading", "--as", "second review")
        cls.ok_at(cls.base, "claim", "A-of-B", "--lean", "A", "--premise", "B", "--theorem", "Tiny.a_of_b")
        cls.ok_at(cls.base, "claim", "B-held", "--lean", "B", "--theorem", "Tiny.b_holds")
        cls.ok_at(cls.base, "claim", "B-of-C", "--lean", "B", "--premise", "C", "--theorem", "Tiny.b_of_c")
        cls.ok_at(cls.base, "claim", "C-held", "--lean", "C", "--theorem", "Tiny.c_holds")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    @staticmethod
    def make(where):
        (where / "lean/Tiny").mkdir(parents=True)
        for name, text in (("lakefile.toml", LAKEFILE), ("lake-manifest.json", MANIFEST), ("lean-toolchain", PIN + "\n"),
                           ("Tiny/Basic.lean", BASIC)):
            (where / "lean" / name).write_bytes(text.encode("utf-8"))
        (where / "campaign.json").write_bytes(json.dumps(
            {"name": "tiny", "profile": "P", "package": "lean", "roots": ["Tiny"]}).encode("utf-8"))
        return where

    @staticmethod
    def gp_at(where, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(where), *args])
        return code, out.getvalue() + err.getvalue()

    @classmethod
    def ok_at(cls, where, *args):
        code, out = cls.gp_at(where, *args)
        assert code == 0, out
        return out

    def copy(self, name):
        dest = self.tmp / name
        shutil.copytree(self.base, dest)
        return dest

    def ok(self, where, *args):
        code, out = self.gp_at(where, *args)
        self.assertEqual(code, 0, out)
        return out

    def no(self, where, *args):
        code, out = self.gp_at(where, *args)
        self.assertEqual(code, 1, out)
        return out

    def lines(self, where):
        return {l.split(": ", 1)[0]: l for l in self.ok(where, "status").splitlines() if ": " in l}

    def held(self, where, label):
        return self.lines(where)[label].split(": ", 1)[1].startswith("held")

    def edit(self, where, old, new):
        path = where / "lean/Tiny/Basic.lean"
        text = path.read_bytes().decode("utf-8")
        self.assertIn(old, text)
        path.write_bytes(text.replace(old, new).encode("utf-8"))

    def append(self, where, record):
        with (where / "ledger.jsonl").open("ab") as f:
            f.write((json.dumps(dict(record, at="2026-10-16T00:00:00Z"), sort_keys=True) + "\n").encode("utf-8"))

    def key(self, where, label):
        return next(r["key"] for r in gp.Ledger(where).records if r.get("label") == label and "key" in r
                    and r["op"] in ("pclaim", "discharge"))

    # --- positives -------------------------------------------------------------------------------------

    def test_held_positives_and_views(self):
        lines = self.lines(self.base)
        self.assertIn("A-of-B: held; tier 2 (unreplayed); open: B (dischargeable by B-held)", lines["A-of-B"])
        self.assertTrue(lines["B-held"].startswith("B-held: held; tier 2 (unreplayed)"))
        c = self.copy("pos")
        out = self.ok(c, "discharge", "A-of-B", "--premise", "B", "--by", "B-held", "--as", "A")
        self.assertIn("with B-held: A; held; tier 2 (unreplayed)", out)
        self.assertIn("discharge of B", self.ok(c, "explain", "A"))
        # Weakening is Kernel narrowing: same statement, more premises.
        out = self.ok(c, "claim", "B-weak", "--lean", "B", "--premise", "C", "--from", "B-held")
        self.assertIn("held", out)
        self.assertIn("weakening needs", self.no(c, "claim", "B-bad", "--lean", "A", "--from", "B-held"))

    def test_prose_never_holdable(self):
        c = self.copy("prose")
        self.assertIn("never holdable", self.no(c, "claim", "P", "--prose", "second review", "--theorem", "Tiny.b_holds"))
        self.ok(c, "claim", "P", "--prose", "second review")
        self.assertIn("cannot take a prose premise",
                      self.no(c, "claim", "Q", "--lean", "A", "--premise", "second review", "--theorem", "Tiny.a_sorry"))
        self.assertFalse(self.held(c, "P"))

    # --- control 1: a renamed declaration ----------------------------------------------------------

    def test_control_1_renamed_declaration(self):
        c = self.copy("c1")
        self.edit(c, "def A : Prop := base = 3", "def A2 : Prop := base = 3")
        self.edit(c, "theorem a_of_b : B → A", "theorem a_of_b : B → A2")
        self.edit(c, "theorem a_sorry : A", "theorem a_sorry : A2")
        self.edit(c, "axiom cheat : A", "axiom cheat : A2")
        self.edit(c, "theorem a_axiom : A", "theorem a_axiom : A2")
        line = self.lines(c)["A-of-B"]
        self.assertIn("A-of-B: unbound (Tiny.A is missing from the package (renamed or deleted)", line)
        self.assertTrue(self.held(c, "B-held"))

    # --- control 2: a redefined dependency ---------------------------------------------------------

    def test_control_2_redefined_dependency(self):
        c = self.copy("c2")
        self.edit(c, "def base : Nat := 3", "def base : Nat := 1 + 2")
        lines = self.lines(c)
        self.assertIn("unbound (A was redefined: changed Tiny.base", lines["A-of-B"])
        self.assertIn("register a new code and refile the claim", lines["A-of-B"])
        for label in ("A-of-B", "B-held", "C-held"):
            self.assertFalse(self.held(c, label))
        # The fix: register new codes and refile; the new claim is held.
        self.ok(c, "register", "Tiny.A", "--as", "A'")
        self.ok(c, "register", "Tiny.B", "--as", "B'")
        self.assertIn("held", self.ok(c, "claim", "A2", "--lean", "A'", "--premise", "B'", "--theorem", "Tiny.a_of_b"))
        self.assertIn("Tiny.base", self.ok(c, "frontier"))

    # --- control 3: an edited ledger hash, a stale stamp, a tampered bind report --------------------------

    def tamper_register(self, where, field, value):
        path = where / "ledger.jsonl"
        rows = [json.loads(l) for l in path.read_bytes().decode("utf-8").splitlines() if l.strip()]
        for r in rows:
            if r["op"] == "register" and r["name"] == "B":
                r[field] = value
        path.write_bytes("".join(json.dumps(r, sort_keys=True) + "\n" for r in rows).encode("utf-8"))

    def test_control_3_edited_hash_and_stale_stamp(self):
        for field, value in (("hash", "0" * 64), ("stamp", "1" * 64)):
            c = self.copy(f"c3-{field}")
            self.tamper_register(c, field, value)
            line = self.lines(c)["B-held"]
            self.assertIn("B-held: unbound", line)
            self.assertIn("environment stamp" if field == "stamp" else "B was redefined", line)
            self.assertFalse(self.held(c, "A-of-B"))
            self.assertTrue(self.held(c, "C-held"))

    def test_control_3_tampered_bind_report(self):
        # Forge the binder's verdict on a refused theorem: the stored report no longer matches its SHA-256.
        c = self.copy("c3-report")
        self.ok(c, "claim", "A-sorry", "--lean", "A", "--theorem", "Tiny.a_sorry")
        bind = [r for r in gp.Ledger(c).records if r["op"] == "bind"][-1]
        path = c / bind["report"]["path"]
        report = json.loads(path.read_bytes())
        forged = [row for row in report["theorems"].values() if not row["axiomsOk"]]
        self.assertTrue(forged)
        for row in forged:
            row.update(axiomsOk=True, axioms=[])
        path.write_bytes(json.dumps(report, sort_keys=True, ensure_ascii=False).encode("utf-8"))
        self.assertIn("does not match its recorded SHA-256", self.no(c, "status"))

    # --- control 4: discharge by an unheld claim, another statement, extra premises -----------------------

    def test_control_4_discharge(self):
        c = self.copy("c4")
        self.ok(c, "claim", "B-open", "--lean", "B")
        out = self.ok(c, "discharge", "A-of-B", "--premise", "B", "--by", "B-open", "--as", "A-unheld")
        self.assertIn("rests on unheld B-open", out)
        self.assertFalse(self.held(c, "A-unheld"))
        out = self.no(c, "discharge", "A-of-B", "--premise", "B", "--by", "C-held")
        self.assertIn("statement mismatch: C-held is a claim of C, the premise is B (code mismatch)", out)
        out = self.no(c, "discharge", "A-of-B", "--premise", "B", "--by", "B-of-C")
        self.assertIn("B-of-C has premises the result would drop: C", out)
        # The same discharges appended by hand: the Kernel rule refuses them.
        a, cc, boc = self.key(c, "A-of-B"), self.key(c, "C-held"), self.key(c, "B-of-C")
        stmt_a = next(r for r in gp.Ledger(c).records if r.get("label") == "A-of-B")["stmt"]
        b = next(r for r in gp.Ledger(c).records if r.get("op") == "register" and r["name"] == "B")["code"]
        for label, by in (("A-bad-stmt", cc), ("A-extra", boc)):
            self.append(c, {"op": "discharge", "key": 7000 + len(label), "label": label, "stmt": stmt_a, "premises": [],
                            "support": {"kind": "discharge", "from": a, "by": by, "premise": b}})
        lines = self.lines(c)
        for label in ("A-bad-stmt", "A-extra"):
            self.assertFalse(lines[label].split(": ", 1)[1].startswith("held"), lines[label])
        self.assertTrue(self.held(c, "A-of-B"))

    # --- control 5: hand-appended records ------------------------------------------------------------

    def test_control_5_hand_appended_records(self):
        c = self.copy("c5")
        self.ok(c, "claim", "A-open", "--lean", "A")
        k = self.key(c, "A-open")
        self.append(c, {"op": "pwarrant", "key": k, "label": "A-open", "kind": "hand_proof", "state": "complete",
                        "locator": "nowhere.md", "sha256": "0" * 64})
        self.append(c, {"op": "pwarrant", "key": k, "label": "A-open", "kind": "lean_theorem", "locator": "x"})
        line = self.lines(c)["A-open"]
        self.assertTrue(line.startswith("A-open: open; best: tier 5 (hand proof (complete), recorded only)"), line)
        stmt = next(r for r in gp.Ledger(c).records if r.get("label") == "A-open")["stmt"]
        self.append(c, {"op": "pclaim", "key": 9001, "label": "A-forged", "stmt": stmt, "premises": [],
                        "support": {"kind": "theorem", "decl": "Tiny.a_sorry"}})
        self.assertIn("refused: axiom audit: uses sorryAx", self.lines(c)["A-forged"])

    # --- control 6: sorry, native_decide, a custom axiom ----------------------------------------------

    def test_control_6_axiom_audit(self):
        c = self.copy("c6")
        for label, stmt, thm, ax in (("A-sorry", "A", "Tiny.a_sorry", "sorryAx"), ("A-axiom", "A", "Tiny.a_axiom", "Tiny.cheat"),
                                     ("C-native", "C", "Tiny.c_native", "native_decide")):
            out = self.ok(c, "claim", label, "--lean", stmt, "--theorem", thm)
            self.assertIn(f"theorem {thm} refused: axiom audit: uses", out)
            self.assertIn(ax, out)
            self.assertFalse(self.held(c, label))
        # A theorem of a different statement: the kernel refuses the type.
        out = self.ok(c, "claim", "A-wrong", "--lean", "A", "--theorem", "Tiny.c_holds")
        self.assertIn("the kernel refused its type", out)

    # --- control 7: a withdrawn premise claim -----------------------------------------------------------

    def test_control_7_withdrawn_premise(self):
        c = self.copy("c7")
        self.ok(c, "discharge", "A-of-B", "--premise", "B", "--by", "B-held", "--as", "A")
        self.assertTrue(self.held(c, "A"))
        out = self.no(c, "withdraw", "B-held", "--reason", "filed in error")
        self.assertIn("would un-hold 1 other held claim: A", out)
        out = self.ok(c, "withdraw", "B-held", "--reason", "filed in error", "--cascade")
        self.assertIn("no longer held: A (discharge)", out)
        lines = self.lines(c)
        self.assertIn("B-held: withdrawn", lines["B-held"])
        self.assertFalse(self.held(c, "A"))
        self.assertTrue(self.held(c, "A-of-B"))
        self.assertIn("already withdrawn", self.no(c, "withdraw", "B-held", "--reason", "again"))

    # --- control 9: both merge orders give the same status --------------------------------------------

    def test_control_9_merge_orders(self):
        x, y = self.copy("m-x"), self.copy("m-y")
        self.ok(x, "discharge", "A-of-B", "--premise", "B", "--by", "B-held", "--as", "A")
        self.ok(x, "present", "A", "--venue", "notes", "--tag", "HAND")
        self.ok(y, "withdraw", "B-held", "--reason", "superseded")
        self.ok(y, "fidelity", "A", "--level", "human-audited", "--by", "reviewer", "--ref", "r1")
        self.ok(y, "present", "A-of-B", "--venue", "talk", "--tag", "LEAN")
        xy, yx = self.tmp / "m-xy", self.tmp / "m-yx"
        shutil.copytree(x, xy)
        shutil.copytree(y, yx)
        self.ok(xy, "merge", str(y))
        self.ok(yx, "merge", str(x))
        a, b = self.ok(xy, "status"), self.ok(yx, "status")
        self.assertEqual(a, b)
        self.assertIn("A: open; rests on unheld B-held", a)
        self.assertIn("A-of-B: held; tier 2 (unreplayed); open: B; presented [LEAN] in 1 venue: OVERSTATED", a)

    # --- presentations and fidelity ------------------------------------------------------------------

    def test_overstated_and_fidelity(self):
        c = self.copy("pres")
        self.assertIn("OVERSTATED", self.ok(c, "present", "A-of-B", "--venue", "abstract", "--tag", "LEAN"))
        self.assertNotIn("OVERSTATED", self.ok(c, "present", "A-of-B", "--venue", "paper", "--tag", "LEAN",
                                               "--premise", "B"))
        self.assertIn("OVERSTATED", self.ok(c, "present", "B-held", "--venue", "slides", "--tag", "COMPARATOR"))
        self.assertNotIn("OVERSTATED", self.ok(c, "present", "B-held", "--venue", "notes", "--tag", "HAND"))
        self.ok(c, "fidelity", "A", "--level", "LLM-audited", "--by", "agent", "--ref", "audit-1")
        self.ok(c, "fidelity", "B", "--level", "anchored", "--by", "owner", "--ref", "fc")
        lines = self.lines(c)
        self.assertIn("presented [LEAN] in 2 venues (1 OVERSTATED)", lines["A-of-B"])
        self.assertIn("fidelity: LLM-audited", lines["A-of-B"])
        self.assertIn("fidelity: anchored (asserted)", lines["B-held"])
        self.assertIn("presented [COMPARATOR] in 1 venue: OVERSTATED", lines["B-held"])

    def test_hand_proof_conditions(self):
        # A reviewer's condition on a hand proof is an OPEN premise: shown, and a presentation must state it.
        c = self.copy("cond")
        self.ok(c, "claim", "C-open", "--lean", "C")
        proof = c / "proof.md"
        proof.write_bytes(b"base + 1 = 4 by computation." + bytes([10]))
        out = self.ok(c, "submit", "C-open", "--hand-proof", str(proof), "--state", "complete",
                      "--condition", "second review")
        self.assertIn("recorded only: hand proof (complete)", out)
        self.assertIn("open: second review", out)
        self.assertIn("OVERSTATED", self.ok(c, "present", "C-open", "--venue", "note", "--tag", "HAND"))
        self.assertNotIn("OVERSTATED", self.ok(c, "present", "C-open", "--venue", "ledger", "--tag", "HAND",
                                               "--premise", "second review"))
        self.assertIn("outside the campaign", self.no(c, "submit", "C-open", "--script", str(ROOT / "LIMITS.md")))
        self.assertFalse(self.held(c, "C-open"))

    def test_relative_campaign_path(self):
        # `lake env` runs the binder in the package directory: a relative --campaign must still bind.
        c = self.copy("rel")
        (c / "lean/Tiny/Basic.lean").write_bytes(BASIC.replace("def base : Nat := 3", "def base : Nat := 2 + 1").encode())
        here = os.getcwd()
        os.chdir(self.tmp)
        try:
            out = self.ok("rel", "bind")
        finally:
            os.chdir(here)
        self.assertIn("A: NOT FRESH: A was redefined: changed Tiny.base", out)

    def test_p_commands_need_a_p_campaign(self):
        c = self.tmp / "threeA"
        c.mkdir()
        shutil.copy(ROOT / "campaigns/3p-matroids/campaign.json", c / "campaign.json") if \
            (ROOT / "campaigns/3p-matroids/campaign.json").exists() else (c / "campaign.json").write_bytes(b"{}")
        self.ok(c, "init")
        self.assertIn("needs a P campaign", self.no(c, "register", "X"))
        self.assertIn("needs a P campaign", self.no(c, "claim", "L", "--lean", "X"))
        self.assertIn("not a Lane P command", self.no(self.base, "cover", "x", "--candidates", "f", "--n", "1", "--m", "1"))


if __name__ == "__main__":
    unittest.main()
