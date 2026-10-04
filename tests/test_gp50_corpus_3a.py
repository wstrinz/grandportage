"""post-G2 §3.7: 3a-owned expressible cases through the shared frontend reproduce the receipt."""
import json
import os
from pathlib import Path
import subprocess
import unittest

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / "profile"
RECEIPT = ROOT / "reports/PHASE-3A-CORPUS.json"
SAFETY = ROOT / "reports/PHASE-3A-SAFETY.json"
TOOLCHAIN = ELAN_HOME / "toolchains" / (PROFILE / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")


class Corpus3aTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"])
        # GPProfile.RuleChecks evaluates the IN_IDEAL rule instances with #guard at build time.
        subprocess.run([str(TOOLCHAIN / ("bin/lake" + EXE_SUFFIX)), "build", "gp_corpus_run", "GPProfile.RuleChecks"], cwd=PROFILE,
                       env=env, check=True, capture_output=True)
        out = subprocess.run([str(PROFILE / (".lake/build/bin/gp_corpus_run" + EXE_SUFFIX)), str(ROOT),
                              str(PROFILE / "slice/corpus-3a.json")], check=True, capture_output=True, text=True)
        cls.fresh = json.loads(out.stdout)
        safety = subprocess.run([str(PROFILE / (".lake/build/bin/gp_corpus_run" + EXE_SUFFIX)), str(ROOT),
                                 str(PROFILE / "slice/safety-all-profile.json")], check=True,
                                capture_output=True, text=True)
        cls.safety = json.loads(safety.stdout)

    def test_matches_committed_receipt(self):
        self.assertEqual(self.fresh, json.loads(RECEIPT.read_text(encoding="utf-8")))

    def test_every_case_agrees_without_loss(self):
        self.assertEqual(self.fresh["losses"], 0)
        for case in self.fresh["cases"]:
            with self.subTest(case=case["id"]):
                self.assertEqual(case["observed"], case["expected"])

    def test_supplied_counterexamples_refute_by_contra(self):
        # G3a review §4: the frontend files the counterexample; `contra` does the refusing.
        cases = {c["id"]: c for c in self.fresh["cases"]}
        for case_id in ["GP-X124", "GP-X128"]:
            with self.subTest(case=case_id):
                self.assertEqual(cases[case_id]["observed"], "REFUSE")
                self.assertEqual(len(cases[case_id]["mechanism"]), 1)
                self.assertTrue(cases[case_id]["mechanism"][0].startswith("refuted (contra"))

    def test_global_safety_has_no_false_accept(self):
        self.assertEqual(self.safety, json.loads(SAFETY.read_text(encoding="utf-8")))
        self.assertEqual(self.safety["case_count"], 242)
        for case in self.safety["cases"]:
            if case["observed"] == "ACCEPT":
                with self.subTest(case=case["id"]):
                    self.assertEqual(case["expected"], "ACCEPT")


if __name__ == "__main__":
    unittest.main()
