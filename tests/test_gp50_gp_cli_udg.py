"""HW61 G-2 and release plan A2: graph-bound claims (`gp claim --udg`) and the DECIDE goal held by the Kernel.

Two small DECIDE goals Q(n, m) := ∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P that GP can decide:
- Q(4, 5) is true: the rhombus K4 - {0,3} (two unit triangles) has an exact real point (√3). The Kernel holds
  goal:Q45 by rule realize (`realizeRuleOk_sound`: `udg_frame_iff`, `realize_sound`).
- Q(4, 6) is false: a cover with the one candidate K4 (exhaustive for (4, 6)), K4 excluded over ℝ by an L1a
  case tree. The Kernel holds the cover (cover_all), its spine (rule spine) and goal:not-Q46 (rule decide).
  A cover filed on a named premise (ENUM-COMPLETE) stays open: the spine is held, the goal is not.

Controls, each refused by the Kernel's own check or not deciding: realize from a frame that is not the premise's,
a padded edge list, fewer than m edges, a graph on other n; spine from K₂,₃ for K4, from an exclusion held only
in every semireal field or only at characteristic 0, or from a tampered system; decide with mismatched n, m or L,
or with an open cover; cover_all on a non-exhaustive or empty list; covers for other (n, m); a legacy cover record;
--goal yes on a --system claim, --goal no anywhere, and a premise-free cover that is not exhaustive.
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
spec = importlib.util.spec_from_file_location("gp_cli_udg", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

K4 = {"name": "K4", "n": 4, "edges": [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]}
RHOMBUS = {"name": "rhombus", "n": 4, "edges": [[0, 1], [0, 2], [1, 2], [1, 3], [2, 3]]}  # K4 - {0, 3}
C4 = {"name": "C4", "n": 4, "edges": [[0, 1], [1, 2], [2, 3], [0, 3]]}
K23 = {"name": "K23", "n": 5, "edges": [[0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4]]}
POINTS4 = [[f"x{i + 1}", f"y{i + 1}"] for i in range(4)]
POINTS5 = [[f"x{i + 1}", f"y{i + 1}"] for i in range(5)]
# p0 - p1 = ½(p0 - p1 + p2 - p3) + ½(p0 - p1 + p3 - p2): the rhombi 0-1-2-3 and 0-1-3-2 collide 0 and 1.
K4_TREE = {"certificate": {"type": "case_tree", "points": POINTS4, "tree": {"collision": {
    "rhombi": [["1/2", [0, 1, 2, 3]], ["1/2", [0, 1, 3, 2]]], "pair": [0, 1]}}}}
K23_TREE = {"certificate": {"type": "case_tree", "points": POINTS5, "tree": {"collision": {
    "rhombi": [["1", [0, 2, 1, 3]], ["-1", [0, 2, 1, 4]]], "pair": [4, 3]}}}}
RHOMBUS_POINT = {"certificate": {"type": "real_point", "symbol": "w", "polynomial": "w^2 - 3", "interval": ["1", "2"],
                                 "point": {"x1": "0", "y1": "0", "x2": "1", "y2": "0", "x3": "1/2", "y3": "w/2",
                                           "x4": "3/2", "y4": "w/2"}}}
C4_POINT = {"certificate": {"type": "real_point", "point": {"x1": "0", "y1": "0", "x2": "1", "y2": "0", "x3": "1",
                                                            "y3": "1", "x4": "0", "y4": "1"}}}
RH5 = {"name": "rhombus+1", "n": 5, "edges": RHOMBUS["edges"]}  # the rhombus and an isolated fifth vertex
RH5_POINT = {"certificate": dict(RHOMBUS_POINT["certificate"], point=dict(RHOMBUS_POINT["certificate"]["point"],
                                                                          x5="5", y5="0"))}
# Σ qᵢ·eqᵢ = 1 on the gauged K4 system: K4 has no point even over ℂ (found by tools-free linear algebra, replayed).
K4_GAUGED_IDEAL = {"certificate": {"type": "ideal", "m": 0, "k": 0, "cofactors": [
    "-2*x1*x3^2 + 2*x1*x3*x4 - x1*x3 - 2*x1*y3*y4 + 2*x1*y4^2 + x1/2 + 2*x3^2*x4 + 2*x3^2 - 2*x3*x4^2 - 2*x3*x4 + "
    "2*x3*y3*y4 - 4*x3*y4^2 + 2*x3 + 2*x4^2 + 2*x4*y3*y4 - 3*x4",
    "-2*x3^2*y1 + 4*x3^2*y4 + 2*x3*x4*y1 - 2*x3*x4*y3 - 2*x3*x4*y4 - x3*y1 + 2*x3*y3 - 2*x4*y3 + 2*x4*y4 - "
    "2*y1*y3*y4 + 2*y1*y4^2 + y1/2 + 2*y3^2*y4 - 2*y3*y4^2 + 2*y3 - 3*y4",
    "x2*x3 + x2/2 - 2*x3^2 + 2*x3*x4 - 2*x4^2 + 1/2", "x3*y2 - 2*x3*y3 + 2*x4*y3 - 2*x4*y4 + y2/2 - y3", "0",
    "-x3*x4 + x3 - x4 + y3*y4 - 2*y4^2 + 1", "2*x3^2 - x3*x4 + x4 + y3*y4 - 3/2", "-x3 + x4 - 1/2", "-x4",
    "x3*x4 - y3*y4 - 1/2"]}}


class Campaign:
    """One campaign directory with a DECIDE goal over (n, m)."""

    @classmethod
    def make(cls, n, m):
        cls.dir = Path(tempfile.mkdtemp())
        goal = {"kind": "DECIDE", "name": f"Q{n}{m}", "statement": f"{n} points with at least {m} unit distances",
                "negation": f"u({n}) < {m}", "udg": {"n": n, "m": m}}
        (cls.dir / "campaign.json").write_text(json.dumps({"name": "G-2 controls", "family": [], "goal": goal}))
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

    def ok(self, *args):
        code, out = self.gp(*args)
        self.assertEqual(code, 0, out)
        return out

    def no(self, *args):
        code, out = self.gp(*args)
        self.assertEqual(code, 1, out)
        return out

    def held(self, label, receipt):
        out = self.ok("submit", label, self.file(label + "-receipt", receipt))
        self.assertIn(f"held: {label}", out)

    def tamper(self, label, change):
        path = self.dir / "ledger.jsonl"
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            r = json.loads(line)
            if r.get("op") == "claim" and r.get("label") == label:
                change(r)
                lines[i] = json.dumps(r, ensure_ascii=False, sort_keys=True)
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")


class YesSide(Campaign, unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.make(4, 5)

    def test_1_shortcuts_refused(self):
        sys_ = self.file("rh-sys", {k: v for k, v in gp.udg_encoder.encode(RHOMBUS).items()
                                    if k in ("variables", "equations", "nonzero")})
        out = self.no("claim", "sys-yes", "--system", sys_, "--kind", "NONEMPTY", "--real", "--goal", "yes")
        self.assertIn("a --system claim carries no bridge to Q", out)
        out = self.no("claim", "udg-no", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--real", "--goal", "no")
        self.assertIn("one exclusion cannot show not Q", out)
        out = self.no("claim", "c4-yes", "--udg", self.file("c4", C4), "--kind", "NONEMPTY", "--real", "--goal", "yes")
        self.assertIn("the graph has 4 edges; Q needs at least 5 unit distances", out)
        out = self.no("claim", "both", "--udg", self.file("k4", K4), "--system", sys_, "--kind", "EMPTY", "--real")
        self.assertIn("--udg names the graph", out)
        out = self.no("claim", "char0", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--char0")
        self.assertIn("a graph-bound claim is a 3b claim over a field", out)
        out = self.no("claim", "frame", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--real",
                      "--premise", "ENCODING-FRAME")
        self.assertIn("ENCODING-FRAME comes with --udg", out)
        labels = {c["label"] for c in gp.Ledger(self.dir).claims()}
        self.assertFalse({"sys-yes", "udg-no", "c4-yes", "both", "char0", "frame"} & labels)

    def test_2_record_shape(self):
        out = self.ok("claim", "rh-g6", "--udg", "Cz", "--kind", "NONEMPTY", "--real", "--gauge")
        self.assertIn("ENCODING-FRAME: equal to the Lean encoder's", out)
        c = gp.Ledger(self.dir).claim("rh-g6")
        # graph6 "Cz" is the rhombus K4 - {0, 3}; the record is canonical and bound by its digest.
        n, edges = gp.udg_encoder.graph6_decode("Cz")
        self.assertEqual((c["udg"]["n"], c["udg"]["edges"], c["udg"]["gauge"]), (n, RHOMBUS["edges"], True))
        self.assertEqual(sorted(edges), RHOMBUS["edges"])
        self.assertEqual(c["inputs"], [f"udg:{gp.graph_sha(n, sorted(map(tuple, edges)))}"])
        self.assertEqual(c["family"], "orderFree")
        self.assertEqual(c["named_premises"], ["ENCODING-FRAME"])

    def test_3_tampered_and_short_never_bridge(self):
        # A legacy goal tag on a held claim with too few edges: unbridged.
        self.ok("claim", "c4", "--udg", self.file("c4", C4), "--kind", "NONEMPTY", "--real")
        self.held("c4", C4_POINT)
        self.tamper("c4", lambda r: r.update(goal="yes"))
        # A tampered system: one edge equation dropped, so the point holds but the frame is unequal.
        self.ok("claim", "rh-t", "--udg", self.file("rh", RHOMBUS), "--kind", "NONEMPTY", "--real", "--goal", "yes")
        self.tamper("rh-t", lambda r: r["system"].update(equations=r["system"]["equations"][:-1]))
        self.held("rh-t", RHOMBUS_POINT)
        out = self.ok("status")
        self.assertIn("Q45: not held (c4, rh-t held, but unbridged: the graph has 4 edges", out)
        self.assertIn("verdict: undecided", out)
        # The Kernel refused rule realize from both on its own check (A2), not on this view's pre-check.
        refused = [r["refusal"]["message"] for r in gp.Ledger(self.dir).attempts("goal:Q45")]
        self.assertGreaterEqual(sum("rule realize refused" in m for m in refused), 2, refused)
        # Controls offered directly: a graph that is not the premise's (a tampered frame), C4 padded with repeated
        # and reversed edges (the canonical count stays 4 < 5), and a premise on 5 vertices.
        self.ok("claim", "rh5", "--udg", self.file("rh5", RH5), "--kind", "NONEMPTY", "--real")
        self.held("rh5", RH5_POINT)
        for name, rule, premise in (("tamper", {"edges": RHOMBUS["edges"]}, "c4"),
                                    ("pad", {"edges": C4["edges"] + [[0, 1], [1, 0], [3, 0]]}, "c4"),
                                    ("n5", {"edges": RHOMBUS["edges"]}, "rh5")):
            out = self.no("submit", "goal:Q45", self.file("realize-" + name, {"rule": dict(rule, type="realize"),
                                                                               "premises": [premise]}))
            self.assertIn("rule realize refused", out)
        out = self.ok("status")
        self.assertIn("verdict: undecided", out)
        out = self.ok("explain", "rh-t")
        self.assertIn("premise ENCODING-FRAME: OPEN", out)
        self.assertIn("the system is not the Lean encoder's for this graph", out)
        self.assertIn("unbridged: the claim's system is not the Lean encoder's for its graph", out)

    def test_4_yes_held(self):
        out = self.ok("claim", "rh", "--udg", self.file("rh", RHOMBUS), "--kind", "NONEMPTY", "--real", "--goal", "yes")
        self.assertIn("[graph rhombus (4 vertices, 5 edges", out)
        # --goal yes files a realize attempt; it waits for its premise.
        self.assertIn("goal: goal:Q45 not held (rule realize from rh): rule realize needs held premises; not held: rh",
                      out)
        out = self.ok("submit", "rh", self.file("rh-receipt", RHOMBUS_POINT))
        self.assertIn("held: rh", out)
        self.assertIn("held: goal:Q45 at the field ℝ (rule realize from rh)", out)
        out = self.ok("status")
        self.assertIn("Q45: held by the Kernel (goal:Q45: rule realize from rh; GPBinding.Real.realizeRuleOk_sound: "
                      "udg_frame_iff, realize_sound)", out)
        self.assertIn("verdict: decided: Q45", out)
        out = self.ok("explain", "rh")
        self.assertIn("premise ENCODING-FRAME: discharged (proved: GPBinding.UDG.udg_frame_iff", out)
        self.assertIn("filed as Q45: the Kernel holds goal:Q45 through it (rule realize", out)
        out = self.ok("explain", "goal:Q45")
        self.assertIn("goal:Q45: GOAL at the field ℝ: held", out)
        self.assertIn("by rule realize from:", out)


class NoSide(Campaign, unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.make(4, 6)

    def status(self):
        return self.ok("status")

    def test_1_cover_refusals(self):
        out = self.no("cover", "bare", "--candidates", self.file("k4s", [K4]), "--n", "4", "--m", "5")
        self.assertIn("a cover's completeness needs a warrant", out)  # {K4} misses K4 - e at (4, 5)
        out = self.no("cover", "empty", "--candidates", self.file("none", []), "--n", "4", "--m", "6")
        self.assertIn("a cover's completeness needs a warrant", out)
        out = self.no("cover", "wrong-n", "--candidates", self.file("k23s", [K23]), "--n", "4", "--m", "6",
                      "--premise", "ENUM-COMPLETE")
        self.assertIn("candidate 0 has 5 vertices, not 4", out)
        out = self.no("cover", "kummer", "--candidates", self.file("k4s", [K4]), "--n", "4", "--m", "6",
                      "--premise", "KUMMER-INDEPENDENCE")
        self.assertIn("a cover rests on AMP-THM1, GP74-NON-UD, ENUM-COMPLETE", out)
        self.assertEqual(gp.cover_claims(gp.Ledger(self.dir)), [])

    def test_2_open_until_excluded(self):
        out = self.ok("cover", "c-enum", "--candidates", self.file("k4s", [K4]), "--n", "4", "--m", "6",
                      "--premise", "ENUM-COMPLETE=abc123")
        self.assertIn("[premise ENUM-COMPLETE: OPEN]", out)
        # Covers for other parameters never count: (4, 5) and (5, 6).
        self.ok("cover", "c45", "--candidates", self.file("k4s", [K4]), "--n", "4", "--m", "5", "--premise", "ENUM-COMPLETE")
        self.ok("cover", "c56", "--candidates", self.file("k23s", [K23]), "--n", "5", "--m", "6",
                "--premise", "ENUM-COMPLETE")
        out = self.status()
        self.assertIn("not Q46 (u(4) < 6): open (cover c-enum: no held exclusion over ℝ for K4 (4 vertices, 6 edges", out)
        self.assertIn("(cover c45 is for n = 4, m = 5; not the goal's n = 4, m = 6; it does not count)", out)
        self.assertIn("verdict: undecided", out)

    def test_3_exclusions_that_do_not_count(self):
        # A different graph, held over ℝ: it excludes K₂,₃, not K4 (and the (5, 6) cover does not count).
        self.ok("claim", "k23", "--udg", self.file("k23", K23), "--kind", "EMPTY", "--real")
        self.held("k23", K23_TREE)
        # K4 excluded at characteristic 0 (a --system claim, not graph-bound) and, by K1a, in every semireal field.
        enc = gp.udg_encoder.encode(K4, gauge=True)
        sys_ = self.file("k4g-sys", {k: enc[k] for k in ("variables", "equations", "nonzero")})
        self.ok("claim", "k4-c", "--system", sys_, "--kind", "EMPTY", "--char0")
        self.held("k4-c", K4_GAUGED_IDEAL)
        self.ok("claim", "k4-semi", "--udg", self.file("k4", K4), "--gauge", "--kind", "EMPTY", "--semireal")
        self.held("k4-semi", {"rule": {"type": "k1a"}, "premises": ["k4-c"]})
        # K4 over ℝ, but with a tampered stored system (an extra equation): the frame is unequal.
        self.ok("claim", "k4-t", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--real")
        self.tamper("k4-t", lambda r: r["system"].update(equations=r["system"]["equations"] + ["x1"]))
        self.held("k4-t", K4_TREE)
        out = self.status()
        self.assertIn("not Q46 (u(4) < 6): open (cover c-enum", out)
        self.assertIn("verdict: undecided", out)
        out = self.ok("explain", "c-enum")
        self.assertIn("premise ENUM-COMPLETE: OPEN (the enumeration of abc123 lists every candidate graph", out)
        self.assertIn("no held exclusion over ℝ", out)
        self.assertIn("k4-semi does not count: held at every semireal field, not over ℝ (narrow it: rule narrow)", out)
        self.assertIn("k4-t does not count: its system is not the Lean encoder's for the graph", out)
        self.assertNotIn("k4-c", out)
        self.assertIn("rule: GPBinding.UDG.spine_sound", out)
        out = self.ok("explain", "c56")
        self.assertIn("excluded by k23", out)
        self.assertIn("spine c56:spine: held by the Kernel (rule spine from k23", out)
        self.assertIn("this cover is for other parameters and does not count", out)
        # Controls offered directly to the Kernel: K₂,₃ for K4, an exclusion held only in every semireal field, one
        # held only at characteristic 0 (a 3a claim), and one on a tampered system.
        for premise in ("k23", "k4-semi", "k4-c", "k4-t"):
            out = self.no("submit", "c-enum:spine", self.file("spine-" + premise, {"rule": {"type": "spine"},
                                                                                     "premises": [premise]}))
            self.assertIn("rule spine refused", out)
        # cover_all on a list that is not exhaustive: (4, 5) needs every graph with at least 5 edges.
        out = self.no("submit", "c45", self.file("all45", {"certificate": {"type": "cover_all"}}))
        self.assertIn("not exhaustive", out)
        self.assertIn("verdict: undecided", self.status())

    def test_4_conditional_then_firm(self):
        self.ok("claim", "k4", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--real")
        self.held("k4", K4_TREE)
        out = self.status()
        self.assertIn("not Q46 (u(4) < 6): open; the Kernel holds spine c-enum:spine (if cover c-enum is complete then "
                      "not Q46); the cover is open, resting on the named premises ENUM-COMPLETE", out)
        self.assertIn("verdict: undecided", out)
        out = self.ok("cover", "c-firm", "--candidates", self.file("k4s", [K4]), "--n", "4", "--m", "6",
                      "--supports", "k23")
        self.assertIn("; exhaustive", out)
        self.assertIn("held: c-firm at the field ℝ (the exhaustive list)", out)
        self.assertIn("held: goal:not-Q46 at the field ℝ (rule decide from c-firm:spine and c-firm)", out)
        out = self.status()
        self.assertIn("not Q46 (u(4) < 6): held by the Kernel (goal:not-Q46: rule decide from c-firm:spine, c-firm; "
                      "GPBinding.Real.decideRuleOk_sound)", out)
        self.assertIn("verdict: decided: not Q46", out)
        out = self.ok("explain", "c-firm")
        self.assertIn("completeness: exhaustive", out)
        self.assertIn("GPBinding.UDG.coverComplete_of_all", out)
        self.assertIn("excluded by k4: held, EMPTY over ℝ, ENCODING-FRAME discharged "
                      "(GPBinding.UDG.candidate_isEmpty, GPBinding.UDG.udg_frame_iff", out)
        self.assertIn("supports (shown, not used by the rule): k23 (held)", out)
        self.assertIn("for the goal: held, not Q, with no OPEN premise", out)
        # A goal claim still never decides not Q; the cover and its spine are Kernel claims, with no legacy record.
        out = self.no("claim", "k4-no", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--real", "--goal", "no")
        self.assertIn("one exclusion cannot show not Q", out)
        ops = {json.loads(l)["op"] for l in (self.dir / "ledger.jsonl").read_text(encoding="utf-8").splitlines()}
        self.assertLessEqual(ops, {"init", "claim", "support", "refused"})
        ledger = gp.Ledger(self.dir)
        self.assertEqual((ledger.claim("c-firm")["family"], ledger.claim("c-firm:spine")["family"]), ("cover", "spine"))


class KernelControls(Campaign, unittest.TestCase):
    """decide with mismatched n, m or L, or with an open cover; an empty cover; a legacy cover record; an older
    ledger's goal claims."""

    @classmethod
    def setUpClass(cls):
        cls.make(4, 6)

    def decide(self, name, spine, cover):
        return self.no("submit", "goal:not-Q46", self.file("decide-" + name, {"rule": {"type": "decide"},
                                                                              "premises": [spine, cover]}))

    def test_1_decide_mismatches(self):
        self.ok("claim", "k4", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--real")
        self.held("k4", K4_TREE)
        none = self.file("none", [])
        self.assertIn("; exhaustive", self.ok("cover", "c47", "--candidates", none, "--n", "4", "--m", "7"))
        self.assertIn("; exhaustive", self.ok("cover", "c34", "--candidates", none, "--n", "3", "--m", "4"))
        self.ok("cover", "c-k4c4", "--candidates", self.file("k4c4", [K4, C4]), "--n", "4", "--m", "6")
        self.ok("cover", "c-open", "--candidates", self.file("k4s", [K4]), "--n", "4", "--m", "6",
                "--premise", "ENUM-COMPLETE")
        ledger = gp.Ledger(self.dir)
        out, items = gp.state(ledger)
        held = {c["label"] for c in ledger.claims() if items[c["key"]]["held"]}
        self.assertLessEqual({"c47", "c47:spine", "c34", "c34:spine", "c-k4c4", "c-open:spine"}, held)
        self.assertFalse({"c-k4c4:spine", "c-open", "goal:not-Q46"} & held)
        self.assertIn("rule decide refused", self.decide("m", "c47:spine", "c47"))
        self.assertIn("rule decide refused", self.decide("n", "c34:spine", "c34"))
        self.assertIn("rule decide refused", self.decide("L", "c-open:spine", "c-k4c4"))
        self.assertIn("rule decide needs held premises; not held: c-open", self.decide("open", "c-open:spine", "c-open"))
        out = self.ok("status")
        self.assertIn("not Q46 (u(4) < 6): open; the Kernel holds spine c-open:spine (if cover c-open is complete then "
                      "not Q46); the cover is open, resting on the named premises ENUM-COMPLETE", out)
        self.assertIn("verdict: undecided", out)
        out = self.ok("frontier")
        self.assertIn("not Q46: open; the Kernel holds spine c-open:spine", out)
        self.assertIn("cover c-open: premise ENUM-COMPLETE: OPEN", out)
        self.assertIn("cover c-k4c4: missing held exclusion over R for C4 (4 vertices, 4 edges", out)
        self.assertIn("goal frontier remains open", out)

    def test_2_empty_cover_and_legacy_record(self):
        self.ok("cover", "c-none", "--candidates", self.file("none", []), "--n", "4", "--m", "6",
                "--premise", "ENUM-COMPLETE")
        out = self.no("submit", "c-none", self.file("all-none", {"certificate": {"type": "cover_all"}}))
        self.assertIn("not exhaustive", out)
        # A pre-A2 record claiming an exhaustive K4 cover: shown as a refile notice, never read as a verdict.
        with (self.dir / "ledger.jsonl").open("a", encoding="utf-8") as f:
            f.write(json.dumps({"op": "cover", "label": "cell-legacy", "n": 4, "m": 6, "candidates": [
                dict(K4, sha256=gp.graph_sha(4, [tuple(e) for e in K4["edges"]]))], "named_premises": [],
                "supports": [], "exhaustive": True, "at": "2026-10-09T00:00:00Z"}, sort_keys=True) + "\n")
        out = self.ok("status")
        self.assertIn("legacy cover record cell-legacy (n = 4, m = 6): refile with `gp cover`; it decides nothing", out)
        self.assertIn("verdict: undecided", out)
        self.assertIn("legacy cover record (filed before release plan A2): refile with `gp cover`",
                      self.ok("explain", "cell-legacy"))
        self.assertIn("verdict: undecided", self.ok("frontier"))

    def test_3_older_ledger_files_the_goal_claims(self):
        old = Path(tempfile.mkdtemp())
        try:
            statement = (self.dir / "campaign.json").read_bytes()
            (old / "campaign.json").write_bytes(statement)
            (old / "ledger.jsonl").write_text(json.dumps({"op": "init", "schema": gp.SCHEMA, "statement_sha256":
                                                          gp.sha(statement), "at": "2026-10-09T00:00:00Z"}) + "\n")

            def run(*words):
                out, err = io.StringIO(), io.StringIO()
                with redirect_stdout(out), redirect_stderr(err):
                    code = gp.main(["--campaign", str(old), *words])
                return code, out.getvalue() + err.getvalue()

            code, out = run("status")
            self.assertEqual(code, 0, out)
            self.assertIn("the goal claims are not filed yet", out)
            self.assertEqual(gp.Ledger(old).claims(), [])
            code, out = run("claim", "k4", "--udg", str(self.file("k4", K4)), "--kind", "EMPTY", "--real")
            self.assertEqual(code, 0, out)
            self.assertIn("goal claim goal:not-Q46 filed", out)
            code, out = run("claim", "c4", "--udg", str(self.file("c4", C4)), "--kind", "NONEMPTY", "--real")
            self.assertNotIn("goal claim", out)
            self.assertEqual(sorted(c["label"] for c in gp.family_claims(gp.Ledger(old), "goal")),
                             ["goal:Q46", "goal:not-Q46"])
        finally:
            shutil.rmtree(old, ignore_errors=True)


class Joins(unittest.TestCase):
    def test_exhaustive_and_canon(self):
        k4 = (4, tuple(map(tuple, K4["edges"])))
        self.assertTrue(gp.exhaustive(4, 6, [k4]))
        self.assertFalse(gp.exhaustive(4, 5, [k4]))
        self.assertTrue(gp.exhaustive(4, 7, []))  # no graph on 4 vertices has 7 edges
        self.assertIsNone(gp.exhaustive(22, 61, []))  # too many graphs: completeness needs a premise
        self.assertIsNone(gp.canon({"n": 4, "edges": [[0, 1], [0, 1]]}))  # repeats would inflate the edge count
        self.assertIsNone(gp.canon({"n": 4, "edges": [[1, 0]]}))
        self.assertIsNone(gp.canon({"n": 4, "edges": [[0, 4]]}))
        self.assertEqual(gp.canon({"n": 2, "edges": [[0, 1]]}), (2, ((0, 1),)))

    def test_lf(self):
        for p in (ROOT / "tools/gp.py", Path(__file__)):
            self.assertNotIn(b"\r\n", p.read_bytes(), p.name)


if __name__ == "__main__":
    unittest.main()
