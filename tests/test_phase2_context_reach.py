"""Exact context-reach tests, with scratch-only test reports."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("context_reach",ROOT/"tools/run-phase2-context-reach.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class ContextReachTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_four_complete_unchanged_contracts(self):
        self.assertEqual([self.cases[c]["observed"] for c in m.CASES],["REFUSE"]*4)
        self.assertEqual(self.report["corpus_executions"],16)
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertEqual(set(row["native_results"]),set(m.ORDERS))

    def test_whole_literal_binding(self):
        for c,row in self.cases.items():
            with self.subTest(case=c):
                raw=(ROOT/"corpus/must"/(c+".json")).read_bytes();obs=row["native_results"]["normal"]
                self.assertEqual(obs["literal_fixture"],json.loads(raw))
                for w in obs["snapshot"]["warrants"]:
                    self.assertEqual(w["binding"]["inputHashes"],[m.sha(raw),obs["bound_literal"]])
                self.assertEqual(obs["snapshot"]["warrants"][-1]["evidence"]["text"],obs["bound_literal"])

    def test_each_context_change_is_unlicensed(self):
        expected={"GP-A01":("Q(sqrt(17))","every characteristic-zero field","BASE_EXTENSION"),
                  "GP-A08a":("Q","F_2","SPECIALIZATION"),
                  "GP-X283":("BASE","ALGEBRAIC_CLOSURE","UNTYPED"),
                  "GP-X14":("unanchored combinatorial objects over Q","Q","UNANCHORED")}
        for c,(s,t,rel) in expected.items():
            with self.subTest(case=c):
                obs=self.cases[c]["native_results"]["normal"]
                self.assertEqual((obs["source_context"],obs["target_context"],obs["relation"]),(s,t,rel))
                self.assertFalse(obs["actual_license_check"])
                self.assertNotIn(1,obs["state"]["held"])
                self.assertIn(10,obs["state"]["held"])

    def test_untyped_step_is_recorded_but_not_licensed(self):
        obs=self.cases["GP-X283"]["native_results"]["normal"]
        self.assertEqual(obs["kind"],"NONEMPTY")
        self.assertEqual(obs["asked_claim"],1)
        self.assertEqual(obs["state"]["held"],[3,10])
        rec=self.controls["X283_record_step_only"]
        self.assertEqual(rec["observed"],"ACCEPT")
        self.assertEqual(rec["native_result"]["asked_claim"],3)

    def test_accepting_contrasts_isolate_the_context_change(self):
        for label in ("A01_same_context_use","A08a_direct_target_certificate","X14_anchored_point_universe"):
            with self.subTest(control=label):
                obs=self.controls[label]["native_result"]
                self.assertEqual(self.controls[label]["observed"],"ACCEPT")
                self.assertIn(1,obs["state"]["held"])
        self.assertTrue(self.controls["A01_same_context_use"]["native_result"]["actual_license_check"])
        direct=self.controls["A08a_direct_target_certificate"]["native_result"]
        self.assertFalse(direct["actual_license_check"])
        self.assertIn(11,direct["state"]["supports"])
        self.assertNotIn(1,direct["state"]["supports"])

    def test_reversed_and_mismatched_changes_refuse(self):
        for label in ("A08a_reverse_characteristic","X283_reverse_universe","X14_mismatched_point_universe"):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["observed"],"REFUSE")

    def test_source_warrant_is_required_even_for_identity(self):
        obs=self.controls["A01_same_context_withheld_source"]["native_result"]
        self.assertTrue(obs["actual_license_check"])
        self.assertEqual(obs["state"]["held"],[])

    def test_malformed_inputs_fail_closed(self):
        for label in ("X283_typed_relation_unsupported","A01_unknown_warrant","X14_extra_input_field"):
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

    def test_no_arithmetic_or_adoption_claims(self):
        self.assertFalse(self.report["field_arithmetic_certified"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["g2_pass"])

    def test_metadata_bytes_unchanged(self):
        for path,digest in self.report["metadata_hashes"].items():
            with self.subTest(path=path):
                self.assertEqual(m.sha(Path(path).read_bytes()),digest)

if __name__=="__main__":
    unittest.main()
