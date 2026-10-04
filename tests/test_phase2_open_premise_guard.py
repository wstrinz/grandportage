"""Exact open-premise guard tests over frozen inference frames, with scratch-only test reports."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("open_premise_guard",ROOT/"tools/run-phase2-open-premise-guard.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class OpenPremiseGuardTests(unittest.TestCase):
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
                self.assertEqual(row["frozen_frame_lf_sha256"],row["literal_inputs"]["fixture_lf_sha256"])
                self.assertEqual(set(row["native_results"]),set(m.ORDERS))

    def test_frozen_frames_are_bound_whole(self):
        for c,row in self.cases.items():
            with self.subTest(case=c):
                obs=row["native_results"]["normal"]
                self.assertEqual(obs["frozen_frame"],json.loads(m.frame_bytes(c)))
                self.assertEqual(obs["literal_fixture"],json.loads((ROOT/"corpus/must"/(c+".json")).read_bytes()))

    def test_family_premise_needs_a_bridge(self):
        obs=self.cases["GP-X399"]["native_results"]["normal"]
        self.assertEqual(obs["inference"],"INF")
        self.assertEqual(obs["slots"],[{"claim":"C-COUNT","model_level":False}])
        self.assertFalse(obs["actual_license_check"])
        self.assertEqual(self.controls["D1_checked_family_bridge"]["observed"],"ACCEPT")

    def test_open_E5_slots_block_their_inferences(self):
        for c,infid,filled in (("GP-X402","INF-X8",["CL-E3B"]),("GP-X403","INF-X10",["CL-E5A","CL-E5B","CL-E5C"])):
            with self.subTest(case=c):
                obs=self.cases[c]["native_results"]["normal"]
                self.assertEqual(obs["inference"],infid)
                self.assertEqual([s["claim"] for s in obs["slots"] if "claim" in s],filled)
                self.assertTrue(all(s["model_level"] for s in obs["slots"] if "claim" in s))
                self.assertEqual(sum("missing_why" in s for s in obs["slots"]),1)
                self.assertEqual(obs["state"]["held"],[])

    def test_filled_slots_accept_only_at_supplied_authority(self):
        x9=self.controls["INF-X9_declared_E5_contrast"]["native_result"]
        self.assertEqual(x9["inference"],"INF-X9")
        self.assertEqual([s["claim"] for s in x9["slots"]],["CL-E3B","CL-E5-DECLARED"])
        self.assertIn("at the authority of E5 and no higher",x9["asserted"])
        for label in ("INF-X9_declared_E5_contrast","X8_supplied_E5_slot","X10_supplied_E5_gap_slot"):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["observed"],"ACCEPT")
                self.assertFalse(self.controls[label]["corpus_pass"])

    def test_dangling_references_refuse(self):
        for label in ("X10_dangling_reference","INF-X9_dangling_reference"):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["observed"],"REFUSE")
                self.assertFalse(self.controls[label]["native_result"]["actual_license_check"])

    def test_stated_premises_must_match_frozen_slots(self):
        for label in ("X402_wrong_available_premise","X403_partial_available_premises","X399_wrong_family"):
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

    def test_no_mathematics_or_adoption_claims(self):
        self.assertFalse(self.report["census_or_family_mathematics_certified"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["g2_pass"])

    def test_metadata_bytes_unchanged(self):
        for path,digest in self.report["metadata_hashes"].items():
            with self.subTest(path=path):
                self.assertEqual(m.sha(Path(path).read_bytes()),digest)

if __name__=="__main__":
    unittest.main()
