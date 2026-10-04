"""Exact conditional theorem-transport tests, with scratch-only test reports."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("theorem_transport",ROOT/"tools/run-phase2-conditional-theorem-transport.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


# The historical oracle (oracle/history/checkout) is private custody material. A public snapshot
# (marked by PUBLIC-SNAPSHOT-RECEIPT.json) excludes it, and workspace CI replays it; anywhere else
# its absence fails.
HISTORY_PRIVATE = ((ROOT / "PUBLIC-SNAPSHOT-RECEIPT.json").exists()
                   and not (ROOT / "oracle/history/checkout").is_dir())


@unittest.skipIf(HISTORY_PRIVATE, "public snapshot: the historical oracle is private")
class ConditionalTheoremTransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_three_complete_unchanged_contracts(self):
        self.assertEqual([self.cases[c]["observed"] for c in m.CASES],["ACCEPT","REFUSE","REFUSE"])
        self.assertEqual(self.report["corpus_executions"],12)
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertTrue(row["full_fixture_contract"])
                self.assertTrue(row["conditional_conclusion_only"])
                self.assertEqual(set(row["native_results"]),set(m.ORDERS))

    def test_whole_literal_binding(self):
        for c,row in self.cases.items():
            with self.subTest(case=c):
                raw=(ROOT/"corpus/must"/(c+".json")).read_bytes();obs=row["native_results"]["normal"]
                self.assertEqual(obs["literal_fixture"],json.loads(raw))
                for w in obs["snapshot"]["warrants"]:
                    self.assertEqual(w["binding"]["inputHashes"],[m.sha(raw),obs["bound_literal"]])
                    self.assertEqual(json.loads(w["binding"]["modelHash"]),obs["authority"])
                self.assertEqual(obs["snapshot"]["warrants"][-1]["evidence"]["text"],obs["bound_literal"])

    def test_three_premise_statements_and_statuses_preserved(self):
        view=m.ledger_view(self.report["source_contract"])
        self.assertEqual([p["status"] for p in view["premises"]],["OPEN","ASSUMED","OPEN"])
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["native_results"]["normal"]["authority"]["premises"],view["premises"])

    def test_retained_edge_is_held_only_as_conditional(self):
        obs=self.cases["GP-X60"]["native_results"]["normal"]
        self.assertTrue(obs["actual_license_check"])
        self.assertEqual(obs["consumer_edge"],obs["authority"])
        self.assertEqual(obs["state"]["held"],[1,5])
        self.assertEqual(obs["edge_dependencies"],[5])
        self.assertFalse(self.report["premises_discharged"])
        self.assertIn("consuming conditional derivation:",obs["snapshot"]["warrants"][0]["binding"]["statementHash"])

    def test_omitted_order_eight_premise_is_refused(self):
        obs=self.cases["GP-X61"]["native_results"]["normal"]
        self.assertNotIn(m.ORDER_EIGHT,[p["statement"] for p in obs["consumer_edge"]["premises"]])
        self.assertIn(m.ORDER_EIGHT,[p["statement"] for p in obs["authority"]["premises"]])
        self.assertFalse(obs["actual_license_check"])
        self.assertEqual(obs["state"]["held"],[5])

    def test_rebound_authority_keeps_endpoint_distinction(self):
        obs=self.cases["GP-X62"]["native_results"]["normal"]
        self.assertEqual(obs["authority"]["target"],m.RELAXED)
        self.assertEqual(obs["consumer_edge"]["target"],"first marked block vanishes")
        self.assertEqual(obs["authority"]["source"],obs["consumer_edge"]["source"])
        self.assertFalse(obs["actual_license_check"])
        self.assertEqual(obs["state"]["held"],[5])

    def test_exact_policy_refuses_every_edge_perturbation(self):
        for mode in m.EDGE_CONTROLS:
            with self.subTest(control=mode):
                row=self.controls[mode]
                self.assertEqual(row["observed"],"REFUSE")
                self.assertFalse(row["native_result"]["actual_license_check"])
                self.assertEqual(row["native_result"]["state"]["held"],[5])
                self.assertFalse(row["corpus_pass"])

    def test_authority_evidence_forms_supply_no_support(self):
        for mode in m.EVIDENCE_CONTROLS:
            with self.subTest(control=mode):
                self.assertEqual(self.controls[mode]["observed"],"REFUSE")
                self.assertEqual(self.controls[mode]["native_result"]["state"]["held"],[])

    def test_malformed_inputs_fail_closed(self):
        for label in ("unknown_premise_status","unknown_proposal","extra_input_field"):
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

    def test_pinned_history_sources(self):
        lines=sorted(c["line"] for c in self.report["source_contract"] if "line" in c)
        self.assertEqual(lines,[96,111,121,232,234])
        self.assertTrue(all(c["commit"]==m.HISTORY for c in self.report["source_contract"]))

    def test_no_adoption_or_replay_claims(self):
        self.assertFalse(self.report["g2_pass"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["theorem_replayed"])

    def test_metadata_bytes_unchanged(self):
        for path,digest in self.report["metadata_hashes"].items():
            with self.subTest(path=path):
                self.assertEqual(m.sha(Path(path).read_bytes()),digest)

if __name__=="__main__":
    unittest.main()
