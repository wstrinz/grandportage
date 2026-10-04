"""Native lifecycle concern tests over unchanged lifecycle-scenario fixtures, with scratch-only reports."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("lifecycle_concerns",ROOT/"tools/run-phase2-lifecycle-concerns.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class LifecycleConcernTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def normal(self,c): return self.cases[c]["native_results"]["normal"]

    def test_eight_complete_unchanged_contracts(self):
        self.assertEqual({c:r["observed"] for c,r in self.cases.items()},m.EXPECTED)
        self.assertEqual(self.report["corpus_executions"],32)
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertEqual(set(row["native_results"]),set(m.ORDERS))

    def test_nothing_is_held(self):
        for c,row in self.cases.items():
            obs=row["native_results"]["normal"]
            if obs.get("status")!="MALFORMED":
                with self.subTest(case=c):
                    self.assertEqual(obs["state"]["held"],[])
                    self.assertEqual(obs["literal_fixture"],json.loads((ROOT/"corpus/must"/(c+".json")).read_bytes()))

    def test_tombstone_is_not_an_edge(self):
        obs=self.normal("GP-X149")
        self.assertEqual(obs["concern"],"live_relation_query")
        self.assertNotIn("W-E",obs["live_names"])
        self.assertEqual(obs["state"]["retracted"],[3])
        self.assertEqual(self.controls["X157_query_live_untyped_successor"]["observed"],"ACCEPT")

    def test_withdrawal_does_not_hide_live_traffic(self):
        self.assertIn("I",self.normal("GP-X150")["live_names"])
        self.assertFalse(self.normal("GP-X150")["cleared"])
        self.assertNotIn("I",self.normal("GP-X151")["live_names"])
        self.assertTrue(self.normal("GP-X151")["cleared"])
        self.assertEqual(self.normal("GP-X151")["state"]["retracted"],[3,5])

    def test_only_a_typed_successor_clears_untyped_debt(self):
        self.assertEqual(self.normal("GP-X156")["live_names"],["IV","PD","E-IV-PD-RESTRICT"])
        self.assertTrue(self.normal("GP-X156")["cleared"])
        self.assertFalse(self.normal("GP-X157")["cleared"])
        self.assertEqual(self.controls["X157_typed_successor"]["observed"],"ACCEPT")
        self.assertEqual(self.controls["X156_without_reclassification"]["observed"],"REFUSE")

    def test_supersession_does_not_repoint(self):
        obs=self.normal("GP-X160")
        self.assertIn("C",obs["live_names"])
        self.assertNotIn("M",obs["live_names"])
        self.assertFalse(obs["cleared"])
        self.assertEqual(self.controls["X160_consumer_repointed"]["observed"],"ACCEPT")

    def test_amend_is_computed_not_declared(self):
        self.assertEqual(self.normal("GP-X162"),{"status":"MALFORMED","error":"annotation_only hides RELICENSE: [coefficients_in_base]"})
        self.assertTrue(self.normal("GP-X163")["cleared"])
        self.assertEqual(self.normal("GP-X163")["field_map"]["citation"],"cite")
        self.assertEqual(self.controls["X162_without_licensing_field"]["observed"],"ACCEPT")
        self.assertEqual(self.controls["X162_declared_restatement"]["observed"],"ACCEPT")
        self.assertEqual(self.controls["X163_statement_change_as_annotation"]["native_result"]["error"],
                         "annotation_only hides RESTATE: [statement]")

    def test_field_tables_match_pinned_kernel(self):
        t=m.tables(self.report["source_contract"])
        obs=self.normal("GP-X163")
        self.assertEqual(obs["identifying_fields"],t["identifying"])
        self.assertEqual(obs["licensing_fields"],t["licensing"])
        self.assertIn("coefficients_in_base",t["licensing"])

    def test_malformed_inputs_fail_closed(self):
        for label in ("X150_unknown_change","X150_unknown_concern"):
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

    def test_no_authority_or_adoption_claims(self):
        self.assertFalse(self.report["held_authority_claimed"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["g2_pass"])

    def test_metadata_bytes_unchanged(self):
        for path,digest in self.report["metadata_hashes"].items():
            with self.subTest(path=path):
                self.assertEqual(m.sha(Path(path).read_bytes()),digest)

if __name__=="__main__":
    unittest.main()
