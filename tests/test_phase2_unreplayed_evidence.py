"""Unreplayed historical evidence and name-only certificate tests, with scratch-only test reports."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("unreplayed_evidence",ROOT/"tools/run-phase2-unreplayed-evidence.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


# The historical oracle (oracle/history/checkout) is private custody material. A public snapshot
# (marked by PUBLIC-SNAPSHOT-RECEIPT.json) excludes it, and workspace CI replays it; anywhere else
# its absence fails.
HISTORY_PRIVATE = ((ROOT / "PUBLIC-SNAPSHOT-RECEIPT.json").exists()
                   and not (ROOT / "oracle/history/checkout").is_dir())


@unittest.skipIf(HISTORY_PRIVATE, "public snapshot: the historical oracle is private")
class UnreplayedEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_two_complete_unchanged_contracts(self):
        self.assertEqual([self.cases[c]["observed"] for c in m.CASES],["REFUSE","REFUSE"])
        self.assertEqual(self.report["corpus_executions"],8)
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertEqual(row["native_results"]["normal"]["literal_fixture"],json.loads((ROOT/"corpus/must"/(c+".json")).read_bytes()))

    def test_historical_metadata_is_not_a_receipt(self):
        obs=self.cases["GP-X229"]["native_results"]["normal"]
        self.assertIsNone(obs["cofactors"])
        self.assertEqual(obs["historical_receipt"],"historical-execution:unavailable:matching:present")
        self.assertEqual(obs["state"]["held"],[])
        self.assertEqual(obs["state"]["live_warrants"],[20,100])
        self.assertEqual(self.controls["X229_identified_historical_backend"]["observed"],"REFUSE")

    def test_native_replay_accepts_only_exact_cofactors(self):
        good=self.controls["X229_replayed_cofactor"]["native_result"]
        self.assertTrue(good["actual_replay"])
        self.assertEqual(good["generators"],[[[1,"1"]]])
        self.assertEqual(good["target"],[[2,"1"],[0,"0"]])
        self.assertEqual(good["state"]["supports"],[10])
        for label in ("X229_wrong_cofactor","X229_false_identity_with_cofactor"):
            with self.subTest(control=label):
                self.assertFalse(self.controls[label]["native_result"]["actual_replay"])
                self.assertEqual(self.controls[label]["native_result"]["state"]["held"],[])

    def test_certificate_name_alone_grants_nothing(self):
        obs=self.cases["GP-X65"]["native_results"]["normal"]
        self.assertIsNone(obs["checked_stratum"])
        self.assertFalse(obs["actual_currency_check"])
        self.assertEqual(obs["state"]["held"],[])
        self.assertEqual(json.loads(obs["current_stratum"]),self.cases["GP-X65"]["literal_inputs"])

    def test_checked_verdict_must_match_current_stratum(self):
        good=self.controls["X65_checked_verdict"]["native_result"]
        self.assertEqual(good["checked_stratum"],good["current_stratum"])
        self.assertEqual(good["state"]["held"],[1])
        for label in ("X65_stale_after_generator_mutation","X65_stale_after_guard_mutation"):
            with self.subTest(control=label):
                obs=self.controls[label]["native_result"]
                self.assertNotEqual(obs["checked_stratum"],obs["current_stratum"])
                self.assertEqual(obs["state"]["held"],[])

    def test_malformed_inputs_fail_closed(self):
        for label in ("X229_unknown_question","X229_unsupported_variable","X65_extra_input_field"):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["native_result"]["status"],"MALFORMED")

    def test_order_and_duplicates_do_not_change_results(self):
        for c,row in self.cases.items():
            runs=row["native_results"];normal={k:v for k,v in runs["normal"].items() if k!="mode"}
            for mode in m.ORDERS:
                with self.subTest(case=c,mode=mode):
                    self.assertEqual({k:v for k,v in runs[mode].items() if k!="mode"},normal)

    def test_kernel_checked_standard_axioms_only(self):
        build=self.report["build"]
        self.assertTrue(build["kernel_checked"])
        self.assertEqual(set(build["axiom_declarations"]),set(m.DECLARATIONS))
        self.assertLessEqual(set(build["axioms"]),{"propext","Quot.sound","Classical.choice"})
        self.assertEqual(build["harness_sha256"],m.sha(m.HARNESS.read_bytes()))

    def test_no_replay_or_adoption_overclaims(self):
        self.assertFalse(self.report["localized_certificate_replayed"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["g2_pass"])

    def test_metadata_bytes_unchanged(self):
        for path,digest in self.report["metadata_hashes"].items():
            with self.subTest(path=path):
                self.assertEqual(m.sha(Path(path).read_bytes()),digest)

if __name__=="__main__":
    unittest.main()
