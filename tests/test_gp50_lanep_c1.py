"""GP 0.52 Lane P, phase P1, acceptance (b): a 33-row claims ledger encoded as a P campaign (design §8(b)).

The withheld fixture campaigns/lanep-c1 encodes every row (prose statements, recorded-only warrants at the rows'
tiers, OPEN premises, process conditions, fidelity and presentations) through the `gp` CLI. Its N1 row, SR-C34, must read
(P2): open; best: hand proof (sketch); open: written proof; conditions open: second review; presented [HAND] in 5
venues: OVERSTATED. GP cannot tell a sketch from a proof: it enforces the filer's declared state and the reviewer's
conditions. Nothing in the encoding is held: prose statements are never holdable and recorded-only warrants never
support.

P2's OVERSTATED tuning, measured against the audit's verdicts on the 67 presentations: process conditions left out read
"conditions open", so 6 of the 53 presentations the audit judged fine are flagged (P1: 17), and 8 of the 14 it judged
overstated (P1: 9; the one no longer flagged is overstated for a novelty claim, which GP does not model).

Skipped where the withheld fixture or its source rows are absent.
"""
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ENCODER = ROOT / "campaigns/lanep-c1/encode.py"


def load_encoder():
    spec = importlib.util.spec_from_file_location("lanep_c1_encode", ENCODER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(ENCODER.exists(), "the withheld C1 fixture is absent")
class C1Encoding(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.enc = load_encoder()
        if not cls.enc.SOURCE.exists():
            raise unittest.SkipTest("the C1 source rows are absent")
        cls.tmp = Path(tempfile.mkdtemp())
        cls.dir = cls.tmp / "c1"
        cls.rows, run = cls.enc.encode(cls.dir)
        cls.gp = staticmethod(run)
        cls.status = {l.split(": ", 1)[0]: l for l in run("status").splitlines() if ": " in l}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_all_rows_encoded_none_held(self):
        self.assertEqual(len(self.rows), 33)
        for r in self.rows:
            self.assertIn(r["id"], self.status)
            self.assertFalse(self.status[r["id"]].split(": ", 1)[1].startswith("held"), self.status[r["id"]])

    def test_n1_overstated_with_open_premises(self):
        self.assertIn("SR-C34: open; best: hand proof (sketch); open: written proof; conditions open: second review; "
                      "presented [HAND] in 5 venues: OVERSTATED", self.status["SR-C34"])

    def test_explain_and_frontier(self):
        out = self.gp("explain", "SR-C34")
        self.assertIn("recorded only: hand proof (sketch)", out)
        self.assertEqual(out.count(": OVERSTATED"), 6)  # the summary line and the five presentations
        frontier = self.gp("frontier")
        self.assertIn("second review (review): 2 claims (SR-C33, SR-C34)", frontier)

    def test_overstated_against_the_audit(self):
        counts = self.enc.compare(self.dir, self.rows, self.enc.load_gp())
        self.assertEqual(counts, {"C1 matches / GP OVERSTATED": 6, "C1 matches / GP conditions open": 11,
                                  "C1 matches / GP ok": 36, "C1 overstated / GP OVERSTATED": 8,
                                  "C1 overstated / GP conditions open": 1, "C1 overstated / GP ok": 5,
                                  "C1 understated / GP ok": 3})

    def test_tiers_and_complete_hand_proofs(self):
        self.assertIn("best: tier 5 (hand proof (complete), recorded only)", self.status["PD"])
        self.assertIn("best: tier 1 (external tier 1", self.status["A"])
        self.assertNotIn("OVERSTATED", self.status["A"])


if __name__ == "__main__":
    unittest.main()
