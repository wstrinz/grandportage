"""GP 0.52 Lane P, phase P1, acceptance (a): the C3b rerun under P (design §8(a)).

The fixture package (campaigns/lanep-c3b/lean, at the binding's pin, Mathlib shared through `packagesDir`) holds the
rope's definitions and theorems and the statements ConeEq, Hconv and Transport. Under P:
- ConeEq under {Hconv} is held by the lean_theorem cone_eq_qCone_of_convex;
- ¬Transport is held by factorization_alone_insufficient;
- the hostile (premise-free) transport is refused four ways: discharging Hconv with the factorization claim (code
  mismatch), a `sorry` theorem (axiom audit), a hand proof (recorded only: the claim stays open), and an
  unconditional presentation (OVERSTATED).

P2 (`test_p2_fixture_ledger`): the fixture's own ledger holds ConeEq under {Hconv} at tier 1 by a real Comparator
receipt (stock Comparator at the pinned v4.35.0-rc3 revisions, run on WSL's ext4 by tools/lanep-comparator.sh; its log
says "Your solution is okay"), and its lean4checker replay makes tier 2 final for the package as committed.

Withheld fixture: skipped where the campaign or the binding's Mathlib build is absent. Each bind imports Mathlib
(about a minute on the reference machine).
"""
import io
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
PKG = ROOT / "campaigns/lanep-c3b/lean"
MATHLIB = ROOT / "binding/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
spec = importlib.util.spec_from_file_location("gp_cli_lanep_c3b", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)


@unittest.skipUnless(PKG.is_dir() and MATHLIB.exists(), "the withheld C3b fixture or the binding's Mathlib is absent")
class C3bUnderP(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        cls.dir = cls.tmp / "c3b"
        cls.dir.mkdir()
        statement = json.loads((ROOT / "campaigns/lanep-c3b/campaign.json").read_bytes())
        statement["package"] = PKG.resolve().as_posix()  # this temporary ledger binds the fixture package in place
        (cls.dir / "campaign.json").write_bytes(json.dumps(statement).encode("utf-8"))

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def gp(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(self.dir), *args])
        return code, out.getvalue() + err.getvalue()

    def ok(self, *args):
        code, out = self.gp(*args)
        self.assertEqual(code, 0, out)
        return out

    def test_c3b_rerun(self):
        self.ok("init")
        for decl in ("C3b.ConeEq", "C3b.Hconv", "C3b.Transport"):
            self.assertIn("registered", self.ok("register", decl))
        out = self.ok("claim", "ConeEq-Hconv", "--lean", "ConeEq", "--premise", "Hconv",
                      "--theorem", "C3b.cone_eq_qCone_of_convex")
        self.assertIn("ConeEq under Hconv; held; tier 2 (unreplayed); open: Hconv", out)
        out = self.ok("claim", "NotTransport", "--lean", "¬Transport", "--theorem", "C3b.factorization_alone_insufficient")
        self.assertIn("¬Transport; held; tier 2 (unreplayed)", out)

        # 1. Discharging Hconv with the factorization claim: a code mismatch.
        code, out = self.gp("discharge", "ConeEq-Hconv", "--premise", "Hconv", "--by", "NotTransport")
        self.assertEqual(code, 1, out)
        self.assertIn("statement mismatch: NotTransport is a claim of ¬Transport, the premise is Hconv (code mismatch)", out)
        # 2. A `sorry` theorem: the axiom audit refuses it, and a discharge by it is not held.
        out = self.ok("claim", "Hconv-sorry", "--lean", "Hconv", "--theorem", "C3b.hconv_sorry")
        self.assertIn("theorem C3b.hconv_sorry refused: axiom audit: uses sorryAx", out)
        out = self.ok("claim", "ConeEq-sorry", "--lean", "ConeEq", "--theorem", "C3b.cone_eq_sorry")
        self.assertIn("refused: axiom audit: uses sorryAx", out)
        out = self.ok("discharge", "ConeEq-Hconv", "--premise", "Hconv", "--by", "Hconv-sorry", "--as", "ConeEq-via-sorry")
        self.assertIn("ConeEq; open; rests on unheld Hconv-sorry", out)
        out = self.ok("claim", "Hconv-axiom", "--lean", "Hconv", "--theorem", "C3b.hconv_axiom")
        self.assertIn("uses C3b.garding_convex", out)
        # 3. A hand proof is recorded only: Hconv stays open, and so does the discharge through it.
        self.ok("claim", "Hconv-hand", "--lean", "Hconv")
        proof = self.dir / "garding.md"
        proof.write_bytes(b"Garding (1959): q divides the hyperbolic p (paper Prop 3.2), so q is hyperbolic in e and its\n"
                          b"hyperbolicity cone is convex. Not formalized.\n")
        out = self.ok("submit", "Hconv-hand", "--hand-proof", str(proof), "--state", "complete")
        self.assertIn("recorded only: hand proof (complete)", out)
        out = self.ok("discharge", "ConeEq-Hconv", "--premise", "Hconv", "--by", "Hconv-hand", "--as", "ConeEq-via-hand")
        self.assertIn("ConeEq; open; best: tier 5 (not held; weakest step: Hconv-hand: hand proof (complete))", out)
        # 4. An unconditional presentation of the transport is OVERSTATED; stating Hconv is not.
        self.assertIn("OVERSTATED", self.ok("present", "ConeEq-Hconv", "--venue", "abstract", "--tag", "LEAN"))
        self.assertNotIn("OVERSTATED", self.ok("present", "ConeEq-Hconv", "--venue", "rope README", "--tag", "LEAN",
                                               "--premise", "Hconv"))

        status = {l.split(": ", 1)[0]: l for l in self.ok("status").splitlines() if ": " in l}
        self.assertTrue(status["ConeEq-Hconv"].startswith("ConeEq-Hconv: held; tier 2 (unreplayed); open: Hconv; "
                                                          "presented [LEAN] in 2 venues (1 OVERSTATED)"))
        self.assertTrue(status["NotTransport"].startswith("NotTransport: held"))
        for label in ("Hconv-sorry", "Hconv-axiom", "Hconv-hand", "ConeEq-sorry", "ConeEq-via-sorry", "ConeEq-via-hand"):
            self.assertTrue(status[label].startswith(f"{label}: open"), status[label])
        out = self.ok("explain", "ConeEq-via-hand")
        self.assertIn("recorded only: hand proof (complete) garding.md", out)
        self.assertIn("<- weakest step", out)
        out = self.ok("frontier")
        self.assertIn("Hconv: 1 claim (ConeEq-Hconv)", out)

    def test_p2_fixture_ledger(self):
        # Read-only: the committed ledger's bind and replay records match the package as committed, so nothing is
        # appended (a changed package would rebind, and the test says so).
        camp = ROOT / "campaigns/lanep-c3b"
        before = (camp / "ledger.jsonl").read_bytes()
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(camp), "status"])
        self.assertEqual(code, 0, out.getvalue() + err.getvalue())
        self.assertEqual((camp / "ledger.jsonl").read_bytes(), before, "the fixture package changed: rebind and replay")
        status = {l.split(": ", 1)[0]: l for l in out.getvalue().splitlines() if ": " in l}
        self.assertTrue(status["ConeEq-Hconv-cmp"].startswith("ConeEq-Hconv-cmp: held; tier 1; open: Hconv"))
        self.assertTrue(status["ConeEq-Hconv"].startswith("ConeEq-Hconv: held; tier 2; open: Hconv"))
        self.assertTrue(status["NotTransport"].startswith("NotTransport: held; tier 2;"))
        ledger = gp.Ledger(camp)
        w = next(r for r in ledger.records if r["op"] == "pwarrant" and r.get("kind") == "comparator")
        receipt = json.loads(ledger.receipt_file({"label": w["label"], "receipt_ref": w["receipt"]}))
        log = ledger.receipt_file({"label": w["label"], "receipt_ref": w["log"]})
        self.assertIn(b"Your solution is okay", log)
        pins = gp.lanep.comparator_pins()
        self.assertTrue(w["pinned"])
        for k in ("comparator_rev", "lean4export_rev", "toolchain"):
            self.assertEqual(receipt[k], pins[k])
        self.assertTrue(any(r["op"] == "replay" and r["ok"] for r in ledger.records))


if __name__ == "__main__":
    unittest.main()
