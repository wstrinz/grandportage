"""Exact section verdict provenance tests, with scratch-only test reports."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("section_provenance",ROOT/"tools/run-phase2-section-provenance.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class SectionProvenanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}
        cls.certs=m.certificates(cls.report["source_contract"])

    def test_four_complete_unchanged_contracts(self):
        self.assertEqual([self.cases[c]["observed"] for c in m.CASES],["ACCEPT","REFUSE","REFUSE","REFUSE"])
        self.assertEqual(self.report["corpus_executions"],16)
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertEqual(row["literal_inputs"],m.INPUTS[c])
                self.assertEqual(set(row["native_results"]),set(m.ORDERS))

    def test_whole_literal_binding(self):
        for c,row in self.cases.items():
            with self.subTest(case=c):
                raw=(ROOT/"corpus/must"/(c+".json")).read_bytes();obs=row["native_results"]["normal"]
                self.assertEqual(obs["literal_fixture"],json.loads(raw))
                for w in obs["snapshot"]["warrants"]:
                    self.assertEqual(w["binding"]["inputHashes"],[m.sha(raw),obs["bound_literal"]])
                self.assertEqual(obs["snapshot"]["warrants"][-1]["evidence"]["text"],obs["bound_literal"])

    def test_checked_certificate_is_the_pinned_object(self):
        lean=m.HARNESS.read_text(encoding="utf-8")
        self.assertIn(json.dumps(self.certs["checked"]),lean)
        self.assertIn(json.dumps(self.certs["mutated"]),lean)
        self.assertEqual(json.loads(self.certs["checked"])["section"],{"y":"x^2"})
        for row in self.cases.values():
            self.assertEqual(row["native_results"]["normal"]["checked_representation"],self.certs["checked"])

    def test_rejection_does_not_erase_prior_certificate(self):
        obs=self.cases["GP-X173"]["native_results"]["normal"]
        self.assertTrue(obs["actual_binding_check"])
        self.assertEqual(obs["state"]["held"],[1,2])
        self.assertEqual(obs["snapshot"]["retracted"],[])
        self.assertEqual(self.controls["rejected_before_success"]["observed"],"ACCEPT")

    def test_rejection_alone_supplies_no_authority(self):
        obs=self.cases["GP-X174"]["native_results"]["normal"]
        self.assertEqual(obs["state"]["held"],[2])
        self.assertEqual([w["id"] for w in obs["snapshot"]["warrants"]],[20,100])

    def test_mutated_stored_certificate_is_stale(self):
        obs=self.cases["GP-X175"]["native_results"]["normal"]
        self.assertEqual(obs["stored_representation"],self.certs["mutated"])
        self.assertFalse(obs["actual_binding_check"])
        self.assertEqual(obs["state"]["held"],[])
        self.assertEqual(self.controls["mutated_object_with_rejection"]["native_result"]["state"]["held"],[2])

    def test_missing_proof_object_is_refused(self):
        obs=self.cases["GP-X176"]["native_results"]["normal"]
        self.assertIsNone(obs["stored_representation"])
        self.assertFalse(obs["actual_binding_check"])
        self.assertEqual(obs["state"]["held"],[])
        self.assertEqual(self.controls["missing_object_with_rejection"]["observed"],"REFUSE")

    def test_positive_contrast_isolates_the_mutation(self):
        obs=self.controls["success_only"]["native_result"]
        self.assertTrue(obs["actual_binding_check"])
        self.assertEqual(obs["state"]["held"],[1])

    def test_verifier_and_verdict_identity_are_bound(self):
        for label in ("groebner_stamp","rejected_verdict_stamp"):
            with self.subTest(control=label):
                obs=self.controls[label]["native_result"]
                self.assertFalse(obs["actual_binding_check"])
                self.assertEqual(obs["state"]["held"],[2])

    def test_only_explicit_retraction_removes_support(self):
        obs=self.controls["rejection_as_retraction"]["native_result"]
        self.assertEqual(obs["snapshot"]["retracted"],[10])
        self.assertEqual(obs["state"]["held"],[2])
        self.assertFalse(self.controls["rejection_as_retraction"]["corpus_pass"])

    def test_malformed_inputs_fail_closed(self):
        for label in ("unknown_step","unknown_mutation","extra_input_field"):
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
        self.assertFalse(self.report["section_arithmetic_replayed"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["g2_pass"])

    def test_metadata_bytes_unchanged(self):
        for path,digest in self.report["metadata_hashes"].items():
            with self.subTest(path=path):
                self.assertEqual(m.sha(Path(path).read_bytes()),digest)

if __name__=="__main__":
    unittest.main()
