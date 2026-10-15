"""GP 0.51: claim withdrawal (docs/WITHDRAWAL-DESIGN.md §6, tests 1-9), through the `gp` CLI and both runners.

1. A held claim, an open mis-filed claim and a vacuous EMPTY claim are withdrawn: each leaves the frontier and
   appears in tailings. The refusals of §5 (unknown label, already withdrawn, empty reason, goal and spine claims,
   a legacy cover record).
2. Withdraw, then resubmit the same receipt: refused. Control: a support record appended by hand is still not held.
3. A withdrawn rule premise: refused without --cascade, and with it the dependent is not held, in 3a and through
   the 3b copy of a 3a premise. Control: without the withdrawn keys in the 3b part, the dependent stays held.
4. A withdrawn cover under the decided Q(4,6) fixture: the verdict becomes undecided, the spine stays held, and a
   new cover decides it again.
5. Theorem warrants: the `#guard` checks of GPProfile/WithdrawTests.lean (withdrawn, a claim with a binder record is
   not held; control: retracting its support warrant alone leaves it held), elaborated here.
6. A withdrawn claim earns no widening.
7. Merge: a withdrawal on one branch and a support on the other give the same status in both orders. A raw
   `retract` record is still refused.
8. An old ledger (no withdraw record) gives the runners the same input as 0.50 and gets byte-identical output: the
   SHA-256 of each runner's stdout is pinned from the 0.50 runners.
9. W1-W3 and their run-level forms are in the CI axiom audit (tests/test_gp50_axiom_audit.py).
"""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_cli_withdraw", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

SX = {"variables": ["x"], "equations": ["x - 1"], "nonzero": []}
SY = {"variables": ["y"], "equations": ["y - 2"], "nonzero": []}
SZ = {"variables": ["z"], "equations": ["z^2 - 1"], "nonzero": []}
VAC = {"variables": ["x"], "equations": ["x"], "nonzero": ["x"]}  # x = 0 and x ≠ 0: EMPTY, vacuously
LIN = {"variables": ["x"], "equations": ["x - 1", "x - 2"], "nonzero": []}
MAP = {"premises": ["src"], "rule": {"type": "map", "map": {"x": "y - 1"}, "eq_certificates": [
    {"type": "ideal", "cofactors": ["1"], "m": 1, "k": 0}]}}
K4 = {"name": "K4", "n": 4, "edges": [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]}
POINTS4 = [[f"x{i + 1}", f"y{i + 1}"] for i in range(4)]
K4_TREE = {"certificate": {"type": "case_tree", "points": POINTS4, "tree": {"collision": {
    "rhombi": [["1/2", [0, 1, 2, 3]], ["1/2", [0, 1, 3, 2]]], "pair": [0, 1]}}}}


def point(**values):
    return {"certificate": {"type": "point", "point": {k: str(v) for k, v in values.items()}}}


class Campaign:
    statement = None  # campaign.json body; None copies the 3P statement

    @classmethod
    def make(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        cls.dir = cls.tmp / "c"
        cls.dir.mkdir()
        if cls.statement is None:
            shutil.copy(ROOT / "campaigns/3p-matroids/campaign.json", cls.dir / "campaign.json")
        else:
            (cls.dir / "campaign.json").write_text(json.dumps(cls.statement), encoding="utf-8")
        cls.gp_at(cls.dir, "init")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    @staticmethod
    def gp_at(where, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(where), *args])
        return code, out.getvalue() + err.getvalue()

    def ok(self, *args, where=None):
        code, out = self.gp_at(where or self.dir, *args)
        self.assertEqual(code, 0, out)
        return out

    def no(self, *args, where=None):
        code, out = self.gp_at(where or self.dir, *args)
        self.assertEqual(code, 1, out)
        return out

    def file(self, name, body):
        path = self.tmp / f"{name}.json"
        path.write_text(json.dumps(body), encoding="utf-8")
        return str(path)

    def claim(self, label, system, kind, *scope, where=None):
        return self.ok("claim", label, "--system", self.file(f"sys-{label}", system), "--kind", kind,
                       *(scope or ("--char0",)), where=where)

    def held(self, label, receipt, where=None):
        out = self.ok("submit", label, self.file(f"rc-{label}", receipt), where=where)
        self.assertIn(f"held: {label}", out)
        return out

    def items(self, where=None):
        ledger = gp.Ledger(where or self.dir)
        _, items = gp.state(ledger)
        return {c["label"]: items[c["key"]]["held"] for c in ledger.claims()}


class ThreeA(Campaign, unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.make()

    def test_1_withdraw_held_open_and_vacuous(self):
        self.claim("p", SX, "NONEMPTY")
        self.held("p", point(x=1))
        self.claim("misfiled", SZ, "EMPTY")  # z^2 - 1 has points: open for good
        self.claim("vac", VAC, "EMPTY")
        self.held("vac", {"certificate": {"type": "ideal", "cofactors": ["1"], "m": 0, "k": 1}})
        self.assertIn("misfiled: open, no attempt yet", self.ok("frontier"))
        out = self.ok("withdraw", "p", "--reason", "filed for the wrong matroid")
        self.assertIn("withdrawn: p (key ", out)
        self.assertIn("filed for the wrong matroid; was held at characteristic 0", out)
        self.assertIn("readers older than 0.51 will not see this withdrawal", out)
        self.assertIn("was not held", self.ok("withdraw", "misfiled", "--reason", "the system has points"))
        self.assertIn("was held", self.ok("withdraw", "vac", "--reason", "vacuous: the guard kills the locus"))
        held = self.items()
        self.assertFalse(held["p"] or held["misfiled"] or held["vac"])
        status = self.ok("status")
        for label in ("p", "misfiled", "vac"):
            self.assertIn(f"withdrawn {label}", status)
        frontier = self.ok("frontier")
        for label in ("p:", "misfiled:", "vac:"):
            self.assertNotIn(label, frontier)
        rows = {r["claim"]: r for r in gp.tailings(gp.Ledger(self.dir)) if r["kind"] == "withdrawn claim"}
        self.assertEqual(set(rows) & {"p", "misfiled", "vac"}, {"p", "misfiled", "vac"})
        self.assertEqual(rows["vac"]["completeness"], "vacuous: the guard kills the locus")
        self.assertFalse([r for r in gp.tailings(gp.Ledger(self.dir)) if r["kind"] == "open item"
                          and r["claim"] in ("p", "misfiled", "vac")])
        out = self.ok("explain", "p")
        self.assertIn("p: NONEMPTY at characteristic 0: not held (withdrawn ", out)
        # The record is exactly the design's: op, label, key, reason, at.
        ledger = gp.Ledger(self.dir)
        rec = next(r for r in ledger.records if r["op"] == "withdraw" and r["label"] == "p")
        self.assertEqual(set(rec), {"op", "label", "key", "reason", "at"})
        self.assertEqual(rec["key"], ledger.claim("p")["key"])
        # The runner flags withdrawn items, and only those.
        out = gp.run_profile(gp.surface(ledger))
        flagged = {i["key"] for i in out["items"] if i.get("withdrawn")}
        self.assertEqual(flagged, {ledger.claim(x)["key"] for x in ("p", "misfiled", "vac")})
        self.assertTrue(all(i.get("withdrawn", True) is True for i in out["items"]))

    def test_1b_refusals(self):
        self.claim("r", SY, "NONEMPTY")
        self.assertIn("no claim labelled 'nobody'", self.no("withdraw", "nobody", "--reason", "x"))
        self.assertIn("a withdrawal needs a reason", self.no("withdraw", "r", "--reason", "   "))
        self.ok("withdraw", "r", "--reason", "duplicate of p")
        self.assertIn("r is already withdrawn", self.no("withdraw", "r", "--reason", "again"))
        before = (self.dir / "ledger.jsonl").read_bytes()
        # A legacy cover record is not a claim.
        with (self.dir / "ledger.jsonl").open("ab") as f:
            f.write((json.dumps({"op": "cover", "label": "cell-legacy", "n": 4, "m": 6, "candidates": [],
                                 "at": "2026-10-01T00:00:00Z"}, sort_keys=True) + "\n").encode("utf-8"))
        self.assertIn("legacy cover record", self.no("withdraw", "cell-legacy", "--reason", "x"))
        (self.dir / "ledger.jsonl").write_bytes(before)
        # Labels stay taken.
        self.assertIn("label 'r' is taken", self.no("claim", "r", "--system", self.file("sy2", SY), "--kind",
                                                     "NONEMPTY", "--char0"))

    def test_2_resubmit_refused_and_hand_support_not_held(self):
        self.claim("q", SY, "NONEMPTY")
        receipt = self.file("rc-q", point(y=2))
        self.assertIn("held: q", self.ok("submit", "q", receipt))
        self.ok("withdraw", "q", "--reason", "superseded by a sharper claim")
        out = self.no("submit", "q", receipt)
        self.assertIn("q was withdrawn", out)
        self.assertIn("file the corrected claim under a new label", out)
        batch = self.file("batch-q", [{"label": "q", "receipt": receipt}])
        self.assertIn("q was withdrawn", self.no("submit-batch", batch))
        # Control: a support record appended by hand (bypassing `submit`) is still not held.
        ledger = gp.Ledger(self.dir)
        with (self.dir / "ledger.jsonl").open("ab") as f:
            f.write((json.dumps({"op": "support", "label": "q", "key": ledger.claim("q")["key"],
                                 "receipt": point(y=2), "receipt_sha256": "0" * 64, "reach": None,
                                 "at": "2026-10-15T00:00:00Z"}, sort_keys=True) + "\n").encode("utf-8"))
        self.assertFalse(self.items()["q"])
        self.assertIn("withdrawn q", self.ok("status"))

    def test_3_withdrawn_premise_3a_and_3b_copy(self):
        self.claim("src", SY, "NONEMPTY")
        self.held("src", point(y=2))
        self.claim("t", SX, "NONEMPTY")
        self.held("t", MAP)
        self.claim("lin0", LIN, "EMPTY")
        self.held("lin0", {"certificate": {"type": "ideal", "cofactors": ["1", "-1"], "m": 0, "k": 0}})
        self.claim("linS", LIN, "EMPTY", "--semireal")
        self.held("linS", {"rule": {"type": "k1a"}, "premises": ["lin0"]})
        ledger = gp.Ledger(self.dir)
        self.assertIn(ledger.claim("linS")["key"], gp.routed_3b(ledger))
        self.assertNotIn(ledger.claim("lin0")["key"], gp.routed_3b(ledger))
        for premise, dependent in (("src", "t"), ("lin0", "linS")):
            before = (self.dir / "ledger.jsonl").read_bytes()
            out = self.no("withdraw", premise, "--reason", "wrong system")
            self.assertIn(f"would un-hold 1 other held claim: {dependent}", out)
            self.assertIn("--cascade", out)
            self.assertEqual((self.dir / "ledger.jsonl").read_bytes(), before)
            out = self.ok("withdraw", premise, "--reason", "wrong system", "--cascade")
            self.assertIn(f"no longer held: {dependent} (rule ", out)
            held = self.items()
            self.assertFalse(held[premise] or held[dependent])
            self.assertIn(f"not held: rests on withdrawn {premise}", self.ok("status"))
            self.assertIn(f"{dependent}: not held: rests on withdrawn {premise}", self.ok("frontier"))
        out = self.no("submit", "t", self.file("rc-t2", MAP))
        self.assertIn("needs held premises; not held: src (withdrawn)", out)
        # Control (design §7's missed channel): the 3b part's copy of lin0 is what un-holds linS there. Without the
        # withdrawn keys in the 3b part, gp_ledger3 holds linS.
        plan = gp.surface(gp.Ledger(self.dir))
        k = gp.Ledger(self.dir).claim("linS")["key"]
        self.assertIn(gp.Ledger(self.dir).claim("lin0")["key"], plan["_3b"]["withdrawn"])
        part3 = dict(plan["_3b"])
        self.assertFalse(next(i for i in gp.run_ledger3(part3)["items"] if i["key"] == k)["held"])
        del part3["withdrawn"]
        self.assertTrue(next(i for i in gp.run_ledger3(part3)["items"] if i["key"] == k)["held"])

    def test_6_no_widening(self):
        self.claim("w", SZ, "NONEMPTY")
        self.assertIn("earned, unclaimed", self.held("w", point(z=1)))
        k = gp.Ledger(self.dir).claim("w")["key"]
        self.assertIn(k, {w["key"] for w in gp.state(gp.Ledger(self.dir))[0]["widened"]})
        self.ok("withdraw", "w", "--reason", "test")
        out, _ = gp.state(gp.Ledger(self.dir))
        self.assertNotIn(k, {w["key"] for w in out["widened"]})
        self.assertNotIn("w", {r["claim"] for r in gp.tailings(gp.Ledger(self.dir)) if r["kind"] == "earned widening"})


class Cover46(Campaign, unittest.TestCase):
    statement = {"name": "withdrawal controls", "family": [], "goal": {
        "kind": "DECIDE", "name": "Q46", "statement": "4 points with at least 6 unit distances",
        "negation": "u(4) < 6", "udg": {"n": 4, "m": 6}}}

    @classmethod
    def setUpClass(cls):
        cls.make()

    def test_4_withdrawn_cover(self):
        self.ok("claim", "k4", "--udg", self.file("k4", K4), "--kind", "EMPTY", "--real")
        self.held("k4", K4_TREE)
        self.assertIn("held: goal:not-Q46", self.ok("cover", "c-firm", "--candidates", self.file("k4s", [K4]),
                                                    "--n", "4", "--m", "6"))
        self.assertIn("verdict: decided: not Q46", self.ok("status"))
        # Goal and spine claims are refused; withdrawing the cover un-holds goal:not-Q46, so --cascade is needed.
        self.assertIn("a goal claim, which gp files itself", self.no("withdraw", "goal:not-Q46", "--reason", "x"))
        self.assertIn("a spine claim, which gp files itself", self.no("withdraw", "c-firm:spine", "--reason", "x"))
        self.assertIn("would un-hold 1 other held claim: goal:not-Q46", self.no("withdraw", "c-firm", "--reason", "x"))
        out = self.ok("withdraw", "c-firm", "--reason", "the candidate list is under review", "--cascade")
        self.assertIn("no longer held: goal:not-Q46 (rule decide from c-firm:spine, c-firm)", out)
        self.assertIn("goal verdict: decided: not Q46 -> undecided", out)
        held = self.items()
        self.assertTrue(held["c-firm:spine"] and held["k4"])
        self.assertFalse(held["c-firm"] or held["goal:not-Q46"])
        status = self.ok("status")
        self.assertIn("verdict: undecided", status)
        self.assertIn("withdrawn c-firm", status)
        self.assertIn("not held: rests on withdrawn c-firm", status)
        self.assertIn("goal frontier remains open", self.ok("frontier"))
        # A new cover decides it again.
        out = self.ok("cover", "c-again", "--candidates", self.file("k4s", [K4]), "--n", "4", "--m", "6")
        self.assertIn("held: goal:not-Q46 at the field ℝ (rule decide from c-again:spine and c-again)", out)
        self.assertIn("verdict: decided: not Q46", self.ok("status"))


class Merge(Campaign, unittest.TestCase):
    def setUp(self):
        self.make()
        self.claim("p", SX, "NONEMPTY")
        self.claim("keep", SY, "NONEMPTY")
        self.held("keep", point(y=2))

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    @classmethod
    def tearDownClass(cls):
        pass

    def fork(self, name):
        shutil.copytree(self.dir, self.tmp / name)
        return self.tmp / name

    def test_7_withdrawal_beats_support_in_both_orders(self):
        a1, b1 = self.fork("a1"), self.fork("b1")
        self.ok("withdraw", "p", "--reason", "wrong system", where=a1)
        self.held("p", point(x=1), where=b1)
        a2, b2 = self.tmp / "a2", self.tmp / "b2"
        shutil.copytree(a1, a2)
        shutil.copytree(b1, b2)
        out = self.ok("merge", str(b1), where=a1)  # withdrawal here, support there
        self.assertIn("merged 1 records (0 claims, 1 supports, 0 refusals); the merged log folds", out)
        self.assertIn("not held here: p, supported on the other branch (withdrawn here)", out)
        out = self.ok("merge", str(a2), where=b2)  # support here, withdrawal there
        self.assertIn("1 withdrawals); the merged log folds", out)
        self.assertIn("withdrawn on the other branch: p: wrong system", out)
        self.assertIn("no longer held here: p (withdrawn)", out)
        for d in (a1, b2):
            held = self.items(d)
            self.assertFalse(held["p"])
            self.assertTrue(held["keep"])
            self.assertIn("withdrawn p", self.ok("status", where=d))
            self.assertEqual(set(gp.Ledger(d).withdrawals()), {gp.Ledger(d).claim("p")["key"]})
        # A raw retract record still does not land.
        c = self.fork("raw")
        with (c / "ledger.jsonl").open("ab") as f:
            f.write((json.dumps({"op": "retract", "target": gp.Ledger(c).claim("keep")["key"],
                                 "at": "2026-10-15T00:00:00Z"}, sort_keys=True) + "\n").encode("utf-8"))
        before = (self.dir / "ledger.jsonl").read_bytes()
        out = self.no("merge", str(c))
        self.assertIn("raw retraction or supersession records, which the profile does not apply yet", out)
        self.assertEqual((self.dir / "ledger.jsonl").read_bytes(), before)

    def test_7b_withdraw_record_must_name_a_claim(self):
        a = self.fork("a")
        with (a / "ledger.jsonl").open("ab") as f:
            f.write((json.dumps({"op": "withdraw", "label": "ghost", "key": 7, "reason": "x",
                                 "at": "2026-10-15T00:00:00Z"}, sort_keys=True) + "\n").encode("utf-8"))
        self.assertIn("a withdraw record names no claim", self.no("merge", str(a)))


# Test 8: the runners' stdout on this fixture, pinned 2026-10-15 from the 0.50 runners of the main checkout
# (gp_ledger built 2026-10-10, gp_ledger3 2026-10-13); the 0.51 rc3 build gives the same bytes.
OLD_3A_SHA256 = "bb6356b8f8862427d2346413ccfecf437341c9d6af7520a86ccfb2483a43aa67"
OLD_3B_SHA256 = "3ce2ecb1b779b8a847f699ab013a5bbaf7d4c48562d3bce71af31f064493867a"


def old_fixture(where):
    """A ledger written without any withdraw record: 3a receipts and rules, a refusal, an open claim, and a 3b
    rule resting on a 3a premise."""
    def gp_(*args, rc=0):
        code, out = Campaign.gp_at(where, *args)
        if code != rc:
            raise AssertionError(out)

    def put(name, body):
        path = where.parent / f"old-{name}.json"
        path.write_text(json.dumps(body), encoding="utf-8")
        return str(path)

    for label, system, kind, scope, receipt, rc in (
            ("src", SY, "NONEMPTY", "--char0", point(y=2), 0),
            ("t", SX, "NONEMPTY", "--char0", MAP, 0),
            ("open", SZ, "EMPTY", "--char0", point(z=1), 1),  # refused: a point does not show EMPTY
            ("lin0", LIN, "EMPTY", "--char0", {"certificate": {"type": "ideal", "cofactors": ["1", "-1"], "m": 0,
                                                               "k": 0}}, 0),
            ("linS", LIN, "EMPTY", "--semireal", {"rule": {"type": "k1a"}, "premises": ["lin0"]}, 0)):
        gp_("claim", label, "--system", put(f"sys-{label}", system), "--kind", kind, scope)
        gp_("submit", label, put(f"rc-{label}", receipt), rc=rc)


def runner_bytes(plan, exe3a, exe3b):
    """Each runner's raw stdout on a ledger plan (the 3a part, then the 3b part)."""
    plan = dict(plan)
    part3 = plan.pop("_3b")
    a = subprocess.run([str(exe3a)], input=json.dumps(plan).encode("utf-8"), capture_output=True, check=True).stdout
    b = subprocess.run([str(exe3b)], input=json.dumps(part3).encode("utf-8"), capture_output=True, check=True).stdout
    return a, b


class OldLedger(Campaign, unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.make()
        old_fixture(cls.dir)

    def test_8_old_ledger_byte_identical(self):
        ledger = gp.Ledger(self.dir)
        self.assertFalse(ledger.withdrawals())
        plan = gp.surface(ledger)
        self.assertNotIn("withdrawn", plan)
        self.assertNotIn("withdrawn", plan["_3b"])
        gp.state(ledger)  # builds and stamps both runners if needed
        a, b = runner_bytes(plan, gp.EXE, gp.EXE3)
        self.assertEqual(hashlib.sha256(a).hexdigest(), OLD_3A_SHA256, a.decode("utf-8")[:400])
        self.assertEqual(hashlib.sha256(b).hexdigest(), OLD_3B_SHA256, b.decode("utf-8")[:400])
        # An explicit empty list is the same input: the same bytes.
        empty = dict(plan, withdrawn=[], _3b=dict(plan["_3b"], withdrawn=[]))
        self.assertEqual(runner_bytes(empty, gp.EXE, gp.EXE3), (a, b))
        self.assertNotIn(b'"withdrawn"', a + b)


class TheoremWarrant(unittest.TestCase):
    def test_5_theorem_warrant_guards(self):
        profile = ROOT / "profile"
        if not (profile / ".lake/build/lib/lean/GPProfile/Withdraw.olean").exists():
            self.skipTest("the profile is not built here")
        tests = (profile / "GPProfile/WithdrawTests.lean").read_text(encoding="utf-8")
        for needle in ("#guard heldIn (foldWith base records [.retract 1]) 1",
                       "#guard !heldRun { base with withdrawn := [1] } records 1",
                       "#guard widenedRun { base with withdrawn := [1] } == []"):
            self.assertIn(needle, tests)
        toolchain = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains" / (
            profile / "lean-toolchain").read_text(encoding="utf-8").strip().replace("/", "--").replace(":", "---")
        lake = toolchain / "bin" / ("lake.exe" if os.name == "nt" else "lake")
        run = subprocess.run([str(lake), "env", "lean", "GPProfile/WithdrawTests.lean"], cwd=profile,
                             capture_output=True, text=True, encoding="utf-8")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertNotIn("error", run.stdout + run.stderr)


class Audit(unittest.TestCase):
    def test_9_lemmas_in_the_axiom_audit(self):
        audit = (ROOT / "tests/test_gp50_axiom_audit.py").read_text(encoding="utf-8")
        for name in ("withdraw_antitone", "withdraw_resolves", "withdraw_unholds", "runWith_withdrawn",
                     "run3_withdrawn"):
            self.assertIn(f"GPProfile.Withdraw.{name}", audit)


if __name__ == "__main__":
    unittest.main()
