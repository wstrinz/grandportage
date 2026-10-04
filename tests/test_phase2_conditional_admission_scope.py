"""Exact conditional synthetic admission tests, with scratch-only test reports."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("admission_scope",ROOT/"tools/run-phase2-conditional-admission-scope.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class ConditionalAdmissionScopeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_six_complete_unchanged_contracts(self):
        self.assertEqual([self.cases[c]["observed"] for c in m.CASES],["ACCEPT","ACCEPT","REFUSE","REFUSE","REFUSE","REFUSE"])
        self.assertEqual(self.report["corpus_executions"],24)
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertTrue(row["full_fixture_contract"])
                self.assertTrue(row["conditional_conclusion_only"])
                self.assertEqual(set(row["native_results"]),{"normal","reverse","duplicates","reverse_duplicates"})

    def test_whole_claim_and_literal_binding(self):
        for c,row in self.cases.items():
            with self.subTest(case=c):
                raw=(ROOT/"corpus/must"/(c+".json")).read_bytes();case=json.loads(raw);obs=row["native_results"]["normal"]
                self.assertEqual(obs["literal_fixture"],case)
                self.assertEqual(obs["bound_claim"],m.CLAIM)
                self.assertEqual(json.loads(obs["fixed_claim_literal"]),m.CLAIM)
                self.assertEqual(case["inputs"]["claim_sha256"],"sha256:"+m.sha(m.encoded(m.CLAIM)))
                for w in obs["snapshot"]["warrants"]:
                    self.assertEqual(w["binding"]["inputHashes"],[m.sha(raw),obs["bound_literal"]])
                    self.assertEqual(json.loads(w["binding"]["modelHash"]),m.CLAIM)
                self.assertEqual(obs["snapshot"]["warrants"][-1]["evidence"]["text"],obs["bound_literal"])

    def test_named_premises_and_actual_supports(self):
        expected=[[1,2,5,6],[1,2,5,6],[1,5,6],[1,5,6],[],[]]
        for c,held in zip(m.CASES,expected):
            with self.subTest(case=c):
                obs=self.cases[c]["native_results"]["normal"]
                self.assertEqual(obs["state"]["held"],held)
                self.assertEqual(obs["result_dependencies"],[5,6])
        partial=self.cases["GP-A27-partial"]["native_results"]["normal"]
        self.assertIn("class_group_is_quotient_of_candidate",partial["snapshot"]["warrants"][2]["binding"]["statementHash"])
        self.assertFalse(partial["actual_narrow_check"])

    def test_GRH_scope_is_preserved(self):
        keep=self.cases["GP-A27-keep-GRH"]["native_results"]["normal"]
        drop=self.cases["GP-A27-drop-GRH"]["native_results"]["normal"]
        self.assertEqual(keep["effective_scope"],"assumptions=[GRH]")
        self.assertEqual(keep["requested_scope"],"assumptions=[GRH]")
        self.assertTrue(keep["actual_narrow_check"])
        self.assertFalse(drop["actual_narrow_check"])
        self.assertEqual(self.controls["drop_GRH_scope"]["observed"],"REFUSE")

    def test_unconditional_can_actually_narrow_to_GRH(self):
        obs=self.controls["unconditional_full_narrows_to_GRH"]["native_result"]
        self.assertTrue(obs["actual_narrow_check"])
        self.assertEqual(obs["effective_scope"],"assumptions=[]")
        self.assertEqual(obs["requested_scope"],"assumptions=[GRH]")
        self.assertEqual(obs["state"]["held"],[1,2,5,6])
        self.assertEqual(self.controls["retain_GRH_scope"]["observed"],"ACCEPT")

    def test_digest_and_version_mismatches(self):
        for label in ("checked_claim_digest_mismatch","declared_claim_digest_mismatch","contract_version_mismatch","producer_version_mismatch"):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["observed"],"REFUSE")
                self.assertFalse(self.controls[label]["native_result"]["successful_bound_check_registered"])

    def test_changed_polynomial_and_candidate_objects(self):
        for label in ("changed_defining_polynomial","changed_candidate_group"):
            with self.subTest(control=label):
                obs=self.controls[label]["native_result"]
                self.assertNotEqual(obs["bound_claim"],m.CLAIM)
                self.assertFalse(obs["successful_bound_check_registered"])
                self.assertNotIn(2,obs["state"]["held"])

    def test_successful_premise_must_be_present_and_current(self):
        for label in ("withheld_success","withheld_success_flag","wrong_binding"):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["native_result"]["state"]["held"],[5])
        self.assertEqual(self.controls["withheld_success"]["native_result"]["state"]["domain"],[1,2,5,100])

    def test_no_authority_from_theorem_pointer_or_producer_label(self):
        for label in ("theorem_pointer","producer_label_only"):
            with self.subTest(control=label):
                self.assertEqual(self.controls[label]["native_result"]["state"]["held"],[5])
        for label in ("label_raw_success_flags","heuristic_raw_success_flags"):
            with self.subTest(control=label):
                obs=self.controls[label]["native_result"]
                self.assertTrue(obs["admission_premise_registered"])
                self.assertFalse(obs["successful_bound_check_registered"])
                self.assertEqual(obs["state"]["held"],[5])

    def test_quotient_cannot_be_laundered_into_equality(self):
        obs=self.controls["quotient_equality_laundering"]["native_result"]
        self.assertEqual(obs["state"]["held"],[1,5,6])
        self.assertFalse(obs["actual_narrow_check"])

    def test_soundness_axiom_audit_and_boundary(self):
        build=self.report["build"]
        self.assertTrue(build["kernel_checked"])
        self.assertEqual(set(build["axioms"]),{"propext","Quot.sound","Classical.choice"})
        self.assertEqual(len(build["axiom_declarations"]),11)
        self.assertEqual(len(self.report["semantic_hypotheses"]),3)
        self.assertFalse(self.report["class_group_arithmetic_certified"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertFalse(self.report["g2_pass"])

    def test_controls_are_separate_from_corpus(self):
        self.assertEqual(self.report["case_count"],6)
        self.assertEqual(self.report["separate_control_executions"],17)
        self.assertTrue(all(c["corpus_pass"] is False and c["status"]=="EXECUTED" for c in self.report["controls"]))

    def test_cache_binds_local_sources_imports_toolchain(self):
        build=self.report["build"];inputs=build["build_input_hashes"]
        self.assertTrue(m.cache_matches(build,inputs,build["harness_sha256"]))
        for suffix in (".lean",".olean",("lean" + EXE_SUFFIX),("lake" + EXE_SUFFIX),("leanchecker" + EXE_SUFFIX)):
            key=next(k for k in inputs if k.endswith(suffix));changed=dict(inputs);changed[key]="changed"
            with self.subTest(dependency=key):
                self.assertFalse(m.cache_matches(build,changed,build["harness_sha256"]))

    def test_native_output_corruption_is_detected(self):
        raw=(ROOT/"corpus/must/GP-A27-full.json").read_bytes();case=json.loads(raw)
        good=self.cases["GP-A27-full"]["native_results"]["normal"]
        for field in ("literal_fixture","bound_claim","snapshot","state","result_dependencies","actual_narrow_check","successful_bound_check_registered"):
            bad=copy.deepcopy(good);bad[field]=False if isinstance(good[field],bool) else {}
            with self.subTest(field=field),self.assertRaises((ValueError,KeyError)):
                m.verify(case,raw,bad,"normal")

    def test_unknown_assumptions_fail_closed(self):
        c=json.loads((ROOT/"corpus/must/GP-A27-full.json").read_bytes());c["inputs"]["requested_scope_assumptions"]=["GRH","other"]
        obs,_=m.execute(m.encoded(c),"unknown-assumptions","normal",self.report["build"])
        self.assertEqual(obs,{"status":"MALFORMED","error":"unknown assumption scope"})

    def test_expected_metadata_is_not_authority(self):
        c=json.loads((ROOT/"corpus/must/GP-A27-drop-GRH.json").read_bytes());c["expected"]["verdict"]="ACCEPT"
        raw=m.encoded(c);obs,_=m.execute(raw,"expected-metadata","normal",self.report["build"])
        self.assertEqual(m.verify(c,raw,obs,"normal"),"REFUSE")

if __name__=="__main__": unittest.main()

