"""Native recorded-use contract tests; report writes stay in owned scratch."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("recorded_coverage",ROOT/"tools/run-phase2-recorded-use-coverage.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class RecordedUseCoverageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_all_six_unchanged_native_folds(self):
        self.assertEqual(self.report["corpus_executions"],24)
        self.assertEqual([self.cases[c]["observed"] for c in m.CASES],["REFUSE","REFUSE","REFUSE","ACCEPT","ACCEPT","REFUSE"])
        for c,row in self.cases.items():
            with self.subTest(case=c):
                self.assertEqual(row["source_sha256"],m.HASHES[c])
                self.assertTrue(row["full_fixture_contract"])
                self.assertEqual(set(row["native_results"]),{"normal","reverse","duplicates","reverse_duplicates"})

    def test_exact_dimension_gaps(self):
        expected=[{"place":["t"],"order":["-4","0","1","2"]},{"place":[],"order":["-4","0","1","2"]},
          {"place":["t"],"order":[]},{"place":[],"order":[]},{"place":[],"order":[]},{"place":[],"order":["0"]}]
        for c,gaps in zip(m.CASES,expected):
            with self.subTest(case=c):
                self.assertEqual(self.cases[c]["native_results"]["normal"]["missing_by_dimension"],gaps)

    def test_complete_rows_descriptions_and_binding(self):
        for c,row in self.cases.items():
            with self.subTest(case=c):
                raw=(ROOT/"corpus/must"/(c+".json")).read_bytes();case=json.loads(raw)
                obs=row["native_results"]["normal"]
                self.assertEqual(obs["literal_fixture"],case)
                self.assertEqual(obs["literal_inputs"],case["inputs"])
                self.assertEqual(json.loads(obs["bound_literal"]),case)
                for w in obs["snapshot"]["warrants"]:
                    self.assertEqual(w["binding"]["inputHashes"][:2],[m.sha(raw),obs["bound_literal"]])
                self.assertEqual(obs["snapshot"]["warrants"][-1]["evidence"]["text"],obs["bound_literal"])

    def test_no_cross_dimension_substitution(self):
        for label in ("repair_place_only","repair_order_only"):
            self.assertEqual(self.controls[label]["observed"],"REFUSE")
        self.assertEqual(self.controls["repair_both"]["observed"],"ACCEPT")

    def test_conclusion_only_read_is_required(self):
        x=self.cases["GP-X198"]["native_results"]["normal"]
        self.assertEqual(x["required_by_dimension"]["order"],["0"])
        self.assertEqual(x["missing_by_dimension"]["order"],["0"])
        self.assertEqual(self.controls["omitted_conclusion_read"]["observed"],"ACCEPT")
        self.assertFalse(self.controls["omitted_conclusion_read"]["corpus_pass"])

    def test_recorded_vacuity_boundary(self):
        self.assertEqual(self.cases["GP-X197"]["observed"],"ACCEPT")
        self.assertEqual(self.controls["empty_inventory_recorded_vacuity"]["observed"],"ACCEPT")
        self.assertEqual(self.controls["reintroduce_recorded_read"]["observed"],"REFUSE")
        self.assertFalse(self.report["mathematical_sufficiency_certified"])

    def test_literal_infinity_not_alias(self):
        self.assertEqual(self.controls["literal_infinity_covered"]["observed"],"ACCEPT")
        self.assertEqual(self.controls["no_infinity_alias"]["native_result"]["missing_by_dimension"]["place"],["infinity"])

    def test_withheld_declared_components(self):
        self.assertEqual(self.controls["withhold_interior_order"]["native_result"]["missing_by_dimension"]["order"],["-4"])
        self.assertEqual(self.controls["withhold_place_t"]["native_result"]["missing_by_dimension"]["place"],["t"])
        self.assertEqual(self.controls["withheld_order"]["native_result"]["state"]["held"],[1])

    def test_collision_and_binding_corruption(self):
        self.assertEqual(self.controls["dimension_collision"]["observed"],"MALFORMED")
        x=self.controls["wrong_binding"]["native_result"]
        self.assertEqual(x["checker_coverage"],{"place":True,"order":True})
        self.assertEqual(x["state"]["held"],[1])
        self.assertEqual(x["snapshot"]["warrants"][1]["binding"]["inputHashes"],["corrupt binding"])

    def test_soundness_axioms_and_separate_controls(self):
        self.assertTrue(self.report["build"]["kernel_checked"])
        self.assertEqual(self.report["build"]["axioms"],["Quot.sound","propext"])
        self.assertEqual(len(self.report["build"]["axiom_declarations"]),6)
        self.assertEqual(len(self.report["controls"]),13)
        self.assertTrue(all(c["corpus_pass"] is False for c in self.report["controls"]))
        self.assertFalse(self.report["g2_pass"])

    def test_cache_binds_source_olean_and_toolchain(self):
        b=self.report["build"];inputs=b["build_input_hashes"]
        self.assertTrue(m.cache_matches(b,inputs,b["harness_sha256"]))
        for suffix in (".lean",".olean",("lean" + EXE_SUFFIX),("lake" + EXE_SUFFIX),("leanchecker" + EXE_SUFFIX)):
            key=next(k for k in inputs if k.endswith(suffix))
            changed=dict(inputs);changed[key]="tampered"
            with self.subTest(dependency=key):
                self.assertFalse(m.cache_matches(b,changed,b["harness_sha256"]))
        self.assertFalse(m.cache_matches(b,inputs,"tampered source"))

    def test_corrupted_native_outputs_are_detected(self):
        raw=(ROOT/"corpus/must/GP-X196.json").read_bytes();case=json.loads(raw)
        good=self.cases["GP-X196"]["native_results"]["normal"]
        for field in ("literal_inputs","missing_by_dimension","checker_coverage","snapshot","state","joint_dependencies","bound_literal"):
            bad=copy.deepcopy(good)
            bad[field]=[] if field=="joint_dependencies" else ("{}" if field=="bound_literal" else {})
            with self.subTest(field=field),self.assertRaises((ValueError,KeyError)):
                m.verify(case,raw,bad,"normal")

    def test_native_decoder_rejects_unknown_dimension(self):
        case=json.loads((ROOT/"corpus/must/GP-X196.json").read_bytes())
        case["inputs"]["construction_uses"][0]["dimension"]="place-alias"
        obs,_=m.execute(m.encoded(case),"unknown-dimension","normal",self.report["build"])
        self.assertEqual(obs,{"status":"MALFORMED","error":"unknown dimension identity"})

    def test_expected_metadata_grants_no_authority(self):
        case=json.loads((ROOT/"corpus/must/GP-X193.json").read_bytes())
        case["expected"]["verdict"]="ACCEPT"
        raw=m.encoded(case);obs,_=m.execute(raw,"expectation-not-authority","normal",self.report["build"])
        self.assertEqual(m.verify(case,raw,obs,"normal"),"REFUSE")

if __name__=="__main__": unittest.main()
