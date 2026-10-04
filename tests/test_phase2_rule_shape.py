"""Registered rule-shape closure tests, with scratch-only test reports."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("rule_shape",ROOT/"tools/run-phase2-rule-shape.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class RuleShapeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_three_complete_unchanged_contracts(self):
        self.assertEqual([self.cases[c]["observed"] for c in m.CASES],["REFUSE"]*3)
        self.assertEqual(self.report["corpus_executions"],12)
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertEqual(row["native_results"]["normal"]["literal_fixture"],json.loads((ROOT/"corpus/must"/(c+".json")).read_bytes()))

    def test_every_refusal_has_a_closed_countermodel_set(self):
        for c,row in self.cases.items():
            with self.subTest(case=c):
                obs=row["native_results"]["normal"]
                self.assertTrue(obs["closure_is_closed"])
                self.assertNotIn(obs["goal"],obs["closure"])
                self.assertTrue(set(obs["supplied"])<=set(obs["closure"]))
                self.assertEqual(obs["state"]["held"],[])

    def test_disconnected_path_does_not_start_at_claim(self):
        obs=self.cases["GP-A14"]["native_results"]["normal"]
        self.assertEqual(obs["supplied"],["NONEMPTY C"])
        self.assertEqual(obs["rules"][0]["premises"],["NONEMPTY A"])
        self.assertEqual(self.controls["A14_path_starts_at_claim_object"]["native_result"]["state"]["held"],[1])
        self.assertEqual(self.controls["A14_other_disconnected_object"]["observed"],"REFUSE")

    def test_partition_needs_every_branch_and_checked_cover(self):
        obs=self.cases["GP-X04"]["native_results"]["normal"]
        self.assertEqual(obs["supplied"],["EMPTY branch-1"])
        self.assertEqual(obs["rules"][0]["premises"],["EMPTY branch-1","EMPTY branch-2"])
        self.assertEqual(self.controls["X04_every_branch_warranted"]["observed"],"ACCEPT")
        unchecked=self.controls["X04_unchecked_cover"]["native_result"]
        self.assertEqual(unchecked["rules"],[])
        self.assertEqual(self.controls["X04_unchecked_cover"]["observed"],"REFUSE")

    def test_transport_preserves_kind(self):
        obs=self.cases["GP-X09"]["native_results"]["normal"]
        self.assertEqual(obs["goal"],"NONEMPTY target")
        self.assertEqual([r["name"] for r in obs["rules"]],["pure transport"])
        self.assertIn("PREDICATE target",obs["closure"])
        for label,verdict in (("X09_same_kind_conclusion","ACCEPT"),("X09_supplied_kind_changing_rule","ACCEPT"),
                              ("X09_emptiness_conclusion","REFUSE")):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["observed"],verdict)

    def test_malformed_inputs_fail_closed(self):
        for label in ("X09_unknown_kind","A14_extra_input_field","X04_non_boolean_cover"):
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

    def test_no_geometry_or_adoption_claims(self):
        self.assertFalse(self.report["geometric_content_certified"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["g2_pass"])

    def test_metadata_bytes_unchanged(self):
        for path,digest in self.report["metadata_hashes"].items():
            with self.subTest(path=path):
                self.assertEqual(m.sha(Path(path).read_bytes()),digest)

if __name__=="__main__":
    unittest.main()
