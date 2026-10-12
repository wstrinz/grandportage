"""Phase 3b: every 3b-owned corpus case through the 3b frontend and the Kernel fold with admission3."""
import json
import os
from pathlib import Path
import subprocess
import unittest

EXE_SUFFIX = ".exe" if os.name == "nt" else ""
ELAN_HOME = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / "profile"
OWNERS = ROOT / "corpus/GATE-OWNERS.json"
TOOLCHAIN = ELAN_HOME / "toolchains" / (PROFILE / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")

# Cases whose checker does not exist yet, with that checker. This list may only shrink, and only
# deliberately: a case leaves it when its checker lands and its verdict then has to agree.
PENDING = {}

# Some 3b cases read inputs from the historical oracle (oracle/history/checkout), which is private
# custody material. A public snapshot (marked by PUBLIC-SNAPSHOT-RECEIPT.json) excludes it, and workspace
# CI runs this suite; anywhere else its absence fails.
HISTORY_PRIVATE = ((ROOT / "PUBLIC-SNAPSHOT-RECEIPT.json").exists()
                   and not (ROOT / "oracle/history/checkout").is_dir())


@unittest.skipIf(HISTORY_PRIVATE, "public snapshot: the historical oracle is private")
class Corpus3bTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"])
        subprocess.run([str(TOOLCHAIN / ("bin/lake" + EXE_SUFFIX)), "build", "gp_corpus_3b"], cwd=PROFILE,
                       env=env, check=True, capture_output=True)
        out = subprocess.run([str(PROFILE / (".lake/build/bin/gp_corpus_3b" + EXE_SUFFIX)), str(ROOT), str(OWNERS)],
                             check=True, capture_output=True, text=True)
        cls.fresh = json.loads(out.stdout)
        cls.cases = {c["id"]: c for c in cls.fresh["cases"]}

    def test_runs_every_3b_case(self):
        owners = json.loads(OWNERS.read_text(encoding="utf-8"))
        ids = {c["id"] for c in owners["cases"] if c["owner"] == "3b"}
        self.assertEqual(len(ids), 51)
        self.assertEqual(set(self.cases), ids)
        self.assertEqual(self.fresh["case_count"], 51)

    def test_decided_cases_agree(self):
        for cid, case in self.cases.items():
            if case["observed"].startswith("PENDING:"):
                continue
            with self.subTest(case=cid):
                self.assertIn(case["observed"], ["ACCEPT", "REFUSE"])
                self.assertEqual(case["observed"], case["expected"])

    def test_no_false_accept(self):
        self.assertEqual(self.fresh["false_accept"], 0)
        for cid, case in self.cases.items():
            if case["observed"] == "ACCEPT":
                with self.subTest(case=cid):
                    self.assertEqual(case["expected"], "ACCEPT")

    def test_pending_set_is_exact(self):
        pending = {cid: c["observed"][len("PENDING:"):] for cid, c in self.cases.items()
                   if c["observed"].startswith("PENDING:")}
        self.assertEqual(pending, PENDING)
        self.assertEqual(self.fresh["pending"], len(PENDING))
        self.assertEqual(self.fresh["decided"], 51 - len(PENDING))

    def test_refusing_mechanisms(self):
        mech = {cid: c.get("mechanism", []) for cid, c in self.cases.items()}
        # GP-A10-C: an SOS receipt at the characteristic-0 alg scope (the C target) has no admission.
        self.assertTrue(mech["GP-A10-C"][0].startswith("checker: an SOS certificate is admitted only"))
        # Detached receipts refuse through the binding discipline, not through replay.
        for cid in ["GP-X02", "GP-X311"]:
            with self.subTest(case=cid):
                self.assertEqual(mech[cid], ["custody: the receipt is bound to a different statement"])
        # GP-A10-R is held at real by the Kernel's narrowing from the semireal SOS receipt.
        self.assertEqual(mech["GP-A10-R"], ["held by narrowing (K2) from claim 1"])
        # GP-X343: the zero-step route is not evidence, while the separate SOS control is held.
        self.assertTrue(mech["GP-X343"][0].startswith("a 0-step route audit"))
        self.assertTrue(all(i["held"] for i in self.cases["GP-X343"]["items"] if i["key"] != 1))
        # GP-X345: the cover and the ordered branch receipts are held; the lifted rule refuses.
        self.assertEqual(mech["GP-X345"], ["rule refused: a lifted 3a rule binds only alg premises"])
        self.assertEqual([i["held"] for i in self.cases["GP-X345"]["items"]], [True, True, True, False])
        # GP-X404: interval admission refuses before any sign is read.
        self.assertIn("lo < hi required", mech["GP-X404"][0])
        # C6: section and output rows are 3a IN_IDEAL receipts; altered or false rows fail replay, and
        # previously bound rows are unrequested controls (held) that lend the altered proof nothing.
        for cid in ["GP-X256", "GP-X257", "GP-X259", "GP-X260", "GP-X261"]:
            with self.subTest(case=cid):
                self.assertEqual(mech[cid], ["checker: 3a receipt refused"])
        self.assertEqual([i["held"] for i in self.cases["GP-X256"]["items"]], [False, True, True, True])
        self.assertEqual([i["held"] for i in self.cases["GP-X259"]["items"]], [False, True])

    def test_point_universe_controls(self):
        # R7: a typed step that changes the point universe has no R3 row; matching universes fold.
        no_row = "rule refused: no direction-table row"
        for cid in ["GP-X275", "GP-X276", "GP-X277", "GP-X278", "GP-X279", "GP-X368", "GP-A07a"]:
            with self.subTest(case=cid):
                self.assertTrue(self.cases[cid]["mechanism"][0].startswith(no_row))
        # The geometric premise is held where it is true, so the refusal is the step's.
        for cid in ["GP-X368", "GP-A07a"]:
            with self.subTest(case=cid):
                self.assertEqual([i["held"] for i in self.cases[cid]["items"]], [True, False])
        self.assertEqual(self.cases["GP-X280"]["mechanism"], ["held by lifted 3a rule"])
        self.assertEqual(self.cases["GP-X369"]["mechanism"], ["held by 3a receipt"])

    def test_number_field_points(self):
        # C4: extension-valued points replay in Q[a]/(m); m must pass the rational-root test.
        mech = {cid: c.get("mechanism", []) for cid, c in self.cases.items()}
        for cid in ["GP-X347", "GP-X348", "GP-X319"]:
            with self.subTest(case=cid):
                self.assertEqual(mech[cid], ["held by number-field receipt"])
        self.assertIn("guard has no verified inverse", mech["GP-X349"][0])
        self.assertIn("rational-root test", mech["GP-X350"][0])
        # GP-X48: the closure witness is held; the BASE claim cannot reuse its receipt.
        self.assertEqual(mech["GP-X48"], ["custody: the receipt is bound to a different statement"])
        self.assertEqual([i["held"] for i in self.cases["GP-X48"]["items"]], [True, False])
        # C5: the unit witness replays on the pinned fixture; a changed gcd report refuses at replay,
        # and every mutation of the fixture leaves the pinned receipt detached.
        self.assertIn("reported gcd degree", mech["GP-X320"][0])
        for cid in ["GP-X332", "GP-X333", "GP-X334"]:
            with self.subTest(case=cid):
                self.assertEqual(mech[cid], ["custody: the receipt is bound to different inputs"])
        for cid in ["GP-X335", "GP-X336"]:
            with self.subTest(case=cid):
                self.assertEqual(mech[cid], ["custody: the receipt is bound to a different statement"])

    def test_stop_and_ask_calls(self):
        # Will, 2026-10-09. X273/X274: a real-family cover with a trusted same-root check (Descartes).
        mech = {cid: c.get("mechanism", []) for cid, c in self.cases.items()}
        self.assertEqual(mech["GP-X273"], ["held by selected-root cover receipt"])
        self.assertEqual(mech["GP-X274"], ["checker: no branch holds the parent's selected root"])
        # X56 and A11a decide through signed instantiation fixtures; the held premise is true and
        # the refused conclusion is false.
        for cid in ["GP-X56", "GP-A11a"]:
            with self.subTest(case=cid):
                self.assertTrue(self.cases[cid].get("instantiated"))
                self.assertEqual([i["held"] for i in self.cases[cid]["items"]], [True, False])
        self.assertTrue(mech["GP-X56"][0].startswith("narrowing refused: no scope order from ratField"))
        self.assertEqual(self.cases["GP-X56"]["items"][0]["support"], "rational-root receipt")
        self.assertEqual(mech["GP-A11a"], ["rule refused: a lifted 3a rule binds only alg premises"])


if __name__ == "__main__":
    unittest.main()
