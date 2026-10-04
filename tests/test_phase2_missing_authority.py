"""Native missing-authority and receipt-laundering controls."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("missing",ROOT/"tools/run-phase2-missing-authority.py")
mis=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mis)

class MissingAuthorityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tags=json.loads((ROOT/"corpus/LAYER-TAGS.json").read_bytes())
        cls.routes=json.loads((ROOT/"oracle/ROUTES.json").read_bytes())
        cls.rows={}
        for case_id in mis.CASES:
            case,raw,layer=mis.checked_case(case_id,cls.tags,cls.routes)
            cls.rows[case_id]=(case,raw,mis.translate(case,mis.sha(raw)))
        cls.checked=mis.positive()
        cls.report=mis.run(mis.SCRATCH/"tests.report.json")
        cls.results={r["id"]:r for r in cls.report["cases"]}
        cls.contrasts={r["label"]:r for r in cls.report["contrasts"]}

    def test_original_native_unheld_verdicts_complete_state_orders_and_duplicates(self):
        for case_id,(_,_,row) in self.rows.items():
            for order,run in self.results[case_id]["runs"].items():
                with self.subTest(case=case_id,order=order):
                    mis.verify(row,row["wire"],run["native_result"],run["native_custody_result"])
                    self.assertEqual(run["native_result"]["held"],[])
                    self.assertEqual(run["native_result"]["supports"],[])
                    self.assertFalse(run["query_held"])
                    self.assertEqual(run["native_result"],self.results[case_id]["runs"]["forward"]["native_result"])

    def test_literal_full_fixture_statement_inputs_scope_sources_are_immutable_custody(self):
        for case_id,(case,raw,row) in self.rows.items():
            warrant=row["wire"]["events"][-1]["value"]
            identity=json.loads(warrant["evidence"]["text"])
            with self.subTest(case=case_id):
                self.assertEqual(identity["literal_fixture"],case)
                self.assertEqual(identity,row["literal_identity"])
                self.assertEqual(warrant["binding"]["inputHashes"],
                    [mis.sha(raw),mis.digest(case),mis.digest(case["inputs"]),mis.digest({"literal_scope_or_region":case["scope_or_region"]})])
                self.assertEqual(warrant["binding"]["scopeHash"],mis.digest({"literal_scope_or_region":case["scope_or_region"]}))
                native=self.results[case_id]["runs"]["forward"]["native_custody_result"]
                self.assertEqual(native["snapshot"]["warrants"],[warrant])
                self.assertIn(warrant["id"],native["live_warrants"])
                self.assertEqual(row["registry"],{"schema_version":1,"clauses":[],"receipts":[]})

    def test_A15_keeps_missing_rule_and_disjoint_variables_without_invented_premises(self):
        case,_,row=self.rows["GP-A15"]
        self.assertIsNone(case["inputs"]["connecting_rule"])
        self.assertEqual(case["inputs"]["shared_variables"],[])
        self.assertEqual(len(row["wire"]["events"]),3)
        self.assertEqual(row["registry"]["clauses"],[])
        self.assertEqual(row["wire"]["events"][-1]["value"]["evidence"]["kind"],"citation")
        self.assertEqual(self.results["GP-A15"]["observed"],"REFUSE")

    def test_A26_unknown_VIBES_Q_and_absent_receipt_are_opaque_not_scope_grants(self):
        case,_,row=self.rows["GP-A26"]
        self.assertEqual(case["inputs"],{"certificate_name":"VIBES","target_context":"Q","receipt":None})
        self.assertEqual(case["scope_or_region"],"SCOPE")
        self.assertEqual(row["registry"]["receipts"],[])
        self.assertEqual(self.results["GP-A26"]["observed"],"REFUSE")

    def test_X82_all_polynomial_strings_are_literal_commitments_not_checker_inputs(self):
        case,_,row=self.rows["GP-X82"]
        self.assertEqual(case["inputs"]["equation"],"alpha*c7_5+beta=0")
        self.assertEqual(case["inputs"]["alpha"],"5/2*t*(c2_3^2-4*c4_5)")
        self.assertEqual(case["inputs"]["pin"],"15*t^3+1")
        self.assertEqual(case["inputs"]["source_binding"],"digest commitments only")
        self.assertEqual(row["registry"]["clauses"],[])
        self.assertEqual(self.results["GP-X82"]["observed"],"REFUSE")

    def test_actual_accepting_X164_control_uses_exact_Rat_replay_without_corpus_count(self):
        result=self.contrasts["separate_X164_checked_replay"]
        self.assertFalse(result["corpus_pass"])
        self.assertEqual(result["registry"]["clauses"][0]["generators"],[mis.helper.POLYNOMIALS["x"]])
        self.assertEqual(result["registry"]["clauses"][0]["target"],mis.helper.POLYNOMIALS["x"])
        self.assertEqual(result["registry"]["receipts"][0]["cofactors"],[mis.helper.ONE])
        for run in result["runs"].values():
            self.assertEqual(run["native_result"]["held"],[1])
            self.assertEqual(run["native_result"]["supports"],[10])
            self.assertTrue(run["query_held"])
            self.assertEqual(run["native_custody_result"]["held"],[])

    def test_invalid_cofactor_native_control_does_not_hold_even_when_binding_current(self):
        row=copy.deepcopy(self.checked)
        row["registry"]["receipts"][0]["cofactors"]=[[]]
        row["held"]=[];row["supports"]=[]
        run=mis.execute(row,"test-invalid-actual-cofactor",row["wire"])
        self.assertFalse(run["query_held"])
        self.assertEqual(run["native_result"]["live_warrants"],[10])

    def test_borrowed_receipt_name_cannot_launder_any_literal_statement(self):
        for case_id in mis.CASES:
            for suffix in ("borrowed_receipt_name","key_only_rebound","warrant_binding_only_rebound",
                           "registered_receipt_without_clause"):
                result=self.contrasts[case_id+"-"+suffix]
                with self.subTest(case=case_id,control=suffix):
                    self.assertFalse(result["corpus_pass"])
                    for run in result["runs"].values():
                        self.assertEqual(run["native_result"]["held"],[])
                        self.assertEqual(run["native_result"]["supports"],[])
                        self.assertFalse(run["query_held"])

    def test_accidental_registered_receipt_lacks_corresponding_source_clause(self):
        for case_id in mis.CASES:
            control=self.contrasts[case_id+"-registered_receipt_without_clause"]
            receipt=control["registry"]["receipts"][-1]
            self.assertEqual(receipt["claim"],mis.IDS[case_id])
            self.assertNotIn(receipt["claim"],[c["key"] for c in control["registry"]["clauses"]])
            self.assertEqual(receipt["name"],"registered-without-source-clause")
            self.assertEqual(control["runs"]["forward"]["native_result"]["held"],[])

    def test_key_only_rebinding_preserves_literal_binding_and_is_native_unsupported(self):
        for case_id,(_,_,row) in self.rows.items():
            control=self.contrasts[case_id+"-key_only_rebound"]
            record=control["native_inputs"]["events"][-1]["value"]
            self.assertEqual(record["claim"],1)
            self.assertEqual(record["binding"],row["wire"]["events"][-1]["value"]["binding"])
            self.assertEqual(control["runs"]["forward"]["native_result"]["live_warrants"],[mis.IDS[case_id]])
            self.assertEqual(control["runs"]["forward"]["native_result"]["supports"],[])

    def test_warrant_only_rebinding_is_inactive_under_original_current_binding(self):
        for case_id in mis.CASES:
            result=self.contrasts[case_id+"-warrant_binding_only_rebound"]["runs"]["forward"]
            self.assertEqual(result["native_result"]["live_warrants"],[])
            self.assertEqual(result["native_result"]["warrant_count"],1)
            self.assertEqual(result["native_result"]["held"],[])

    def test_absent_connecting_rule_unknown_label_and_verified_citation_text_native_refuse(self):
        for case_id,evidence in (
            ("GP-A15",{"kind":"derived","premises":[],"sideReceipt":"GI-BRIDGE"}),
            ("GP-A26",{"kind":"receipt","data":"VIBES"}),
            ("GP-X82",{"kind":"citation","text":"VERIFIED_SOURCE_DERIVATION: digest commitments only"})):
            row=copy.deepcopy(self.rows[case_id][2])
            row["wire"]["events"][-1]["value"]["evidence"]=evidence
            run=mis.execute(row,"test-evidence-"+case_id,row["wire"])
            with self.subTest(case=case_id):
                self.assertEqual(run["native_result"]["supports"],[])
                self.assertFalse(run["query_held"])

    def test_actual_checked_receipt_binding_mismatch_in_every_field_and_version_refuses(self):
        for field in self.checked["registry"]["receipts"][0]["binding"]:
            row=copy.deepcopy(self.checked)
            value=row["registry"]["receipts"][0]["binding"][field]
            row["registry"]["receipts"][0]["binding"][field]=(value+1 if type(value) is int else value+["wrong"] if isinstance(value,list) else value+"-wrong")
            row["held"]=[];row["supports"]=[]
            with self.subTest(field=field):
                self.assertFalse(mis.execute(row,"test-positive-binding-"+field,row["wire"])["query_held"])
        row=copy.deepcopy(self.checked)
        row["registry"]["receipts"][0]["version"]=2;row["held"]=[];row["supports"]=[]
        self.assertFalse(mis.execute(row,"test-positive-receipt-version",row["wire"])["query_held"])

    def test_unknown_literal_input_fields_and_fabricated_authority_fail_closed(self):
        for case_id,(case,raw,_) in self.rows.items():
            for location in ("root","inputs"):
                changed=copy.deepcopy(case)
                (changed if location=="root" else changed["inputs"])["verified"]=True
                with self.subTest(case=case_id,location=location),self.assertRaises(ValueError):
                    mis.translate(changed,mis.sha(raw))
        changed=copy.deepcopy(self.rows["GP-A15"][0]);changed["inputs"]["connecting_rule"]="GI-BRIDGE"
        with self.assertRaisesRegex(ValueError,"connecting authority"):
            mis.translate(changed,"control")
        changed=copy.deepcopy(self.rows["GP-A26"][0]);changed["inputs"]["receipt"]="VIBES"
        with self.assertRaisesRegex(ValueError,"certificate contract"):
            mis.translate(changed,"control")

    def test_native_asserted_verified_flag_unknown_fields_fail_closed(self):
        row=self.rows["GP-A26"][2]
        for kind in ("registry","event","evidence"):
            registry=copy.deepcopy(row["registry"]);wire=copy.deepcopy(row["wire"])
            node=registry if kind=="registry" else wire["events"][0] if kind=="event" else wire["events"][-1]["value"]["evidence"]
            node["verified"]=True
            paths=[mis.write_input("test-unknown-"+kind,"registry",registry),
                   mis.write_input("test-unknown-"+kind,"events",wire)]
            with self.subTest(kind=kind):
                self.assertEqual(mis.native(mis.RUNNERS["span"],paths),
                                 {"status":"MALFORMED","error":"unexpected field: verified"})

    def test_damaged_native_support_held_custody_bindings_or_record_loss_are_rejected(self):
        for case_id,(_,_,row) in self.rows.items():
            result=self.results[case_id]["runs"]["forward"]
            damaged=copy.deepcopy(result["native_custody_result"])
            damaged["snapshot"]["warrants"]=[]
            with self.assertRaisesRegex(ValueError,"custody"):
                mis.verify(row,row["wire"],result["native_result"],damaged)
            damaged=copy.deepcopy(result["native_custody_result"])
            damaged["snapshot"]["warrants"][0]["binding"]["statementHash"]="wrong"
            with self.assertRaises(ValueError):
                mis.verify(row,row["wire"],result["native_result"],damaged)
            for field in ("supports","held","domain","live_warrants"):
                damaged=copy.deepcopy(result["native_result"]);damaged[field]=[999]
                with self.subTest(case=case_id,field=field),self.assertRaises(ValueError):
                    mis.verify(row,row["wire"],damaged,result["native_custody_result"])

    def test_pinned_history_manifest_packet_anchors_routes_and_layer_guards(self):
        self.assertEqual(self.report["source_contract"],mis.source_contract())
        history=self.report["source_contract"]["tests/test_jc_source_depth6_authority.py"]
        self.assertEqual(history["commit"],mis.HISTORY_PIN)
        self.assertEqual(history["line"],73)
        self.assertEqual(history["git_blob"],"96e936e5c51b691091f7b3fdfb8c4f0ce640db9b")
        self.assertEqual([a["line"] for a in self.report["source_contract"]["packet"]["anchors"]],[555,566])
        for case_id in mis.CASES:
            tags=copy.deepcopy(self.tags)
            next(r for r in tags["cases"] if r["id"]==case_id)["sha256"]="wrong"
            with self.subTest(case=case_id),self.assertRaisesRegex(ValueError,"fixture bytes"):
                mis.checked_case(case_id,tags,self.routes)
        routes=copy.deepcopy(self.routes);routes["commit"]="wrong"
        with self.assertRaisesRegex(ValueError,"route"):
            mis.checked_case("GP-X82",self.tags,routes)

    def test_report_hashes_counts_boundaries_and_unchanged_originals(self):
        report=self.report
        self.assertFalse(report["g2_pass"])
        self.assertEqual(report["case_count"],3)
        self.assertEqual(report["corpus_native_checked_folds"],12)
        self.assertEqual(report["corpus_native_custody_folds"],12)
        self.assertEqual(report["separate_contrast_scenarios"],13)
        self.assertEqual(report["contrast_native_checked_folds"],52)
        self.assertEqual(report["adapter_sha256"],mis.sha(Path(mis.__file__).read_bytes()))
        self.assertEqual(report["tests_sha256"],mis.sha(Path(__file__).read_bytes()))
        for kind,path in mis.RUNNERS.items():
            self.assertEqual(report["executables"][kind]["sha256"],mis.sha(path.read_bytes()))
        for case_id,(case,raw,_) in self.rows.items():
            self.assertEqual((ROOT/"corpus/must"/(case_id+".json")).read_bytes(),raw)
            self.assertEqual(mis.sha(raw),mis.HASHES[case_id])
            self.assertEqual(self.results[case_id]["expected"],case["expected"])
        for row in report["cases"]+report["contrasts"]:
            for order,run in row["runs"].items():
                for suffix,h in run["inputs"].items():
                    path=mis.SCRATCH/(row["label"]+"-"+order+"."+suffix.removesuffix("_sha256")+".json")
                    self.assertEqual(mis.sha(path.read_bytes()),h)

if __name__=="__main__":
    unittest.main()
