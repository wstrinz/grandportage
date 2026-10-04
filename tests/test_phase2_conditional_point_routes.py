"""Checked conditional mixed-premise routes and adversarial controls."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("point_routes",ROOT/"tools/run-phase2-conditional-point-routes.py")
route=importlib.util.module_from_spec(spec)
spec.loader.exec_module(route)

class ConditionalPointRoutesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=route.run(route.SCRATCH/"tests.report.json")
        cls.compiled=cls.report["build"]
        cls.cases={r["id"]:r for r in cls.report["cases"]}
        cls.controls={(r["case"],r["mode"]):r for r in cls.report["controls"]}
        cls.raw={id:(ROOT/"corpus/must"/(id+".json")).read_bytes() for id in route.CASES}

    def test_original_source_orders_show_valid_universal_and_refused_point_leg(self):
        for id,licensed,deps in (("GP-X179",[True,False],[110,120]),("GP-X180",[False,True],[120,110])):
            for mode,observed in self.cases[id]["native_results"].items():
                with self.subTest(case=id,mode=mode):
                    self.assertEqual(observed["route_licensed"],licensed)
                    self.assertEqual(observed["argument_dependency_ids"],deps)
                    self.assertEqual(observed["narrow_checks"],{"universal":True,"exhibited_point":False})
                    self.assertEqual(observed["state"]["supports"],[10,20,110])
                    self.assertEqual(observed["state"]["held"],[1,2,11])
                    self.assertNotIn(3,observed["state"]["held"])

    def test_full_literal_inputs_premise_kinds_statements_contexts_and_routes_preserved(self):
        for id,row in self.cases.items():
            case=json.loads(self.raw[id])
            self.assertEqual(row["source_sha256"],route.HASHES[id])
            for observed in row["native_results"].values():
                self.assertEqual(observed["literal_fixture"],case)
                self.assertEqual(observed["literal_inputs"],case["inputs"])
                self.assertEqual([p["statement_class"] for p in observed["literal_inputs"]["premises"]],
                                 [p["statement_class"] for p in case["inputs"]["premises"]])
                self.assertEqual(observed["literal_inputs"]["relations"],case["inputs"]["relations"])
                self.assertEqual(observed["point_statement_scope"],"global-conditional-theory")

    def test_complete_snapshot_bindings_retained_unsupported_point_and_joint_records(self):
        for id,row in self.cases.items():
            case=json.loads(self.raw[id]);observed=row["native_results"]["normal"]
            records,deps=route.records(case,route.sha(self.raw[id]),"normal")
            self.assertEqual(observed["snapshot"]["warrants"],records)
            self.assertEqual([w["id"] for w in records],[10,20,30,110,120])
            self.assertEqual(observed["state"]["live_warrants"],[10,20,30,110,120])
            self.assertEqual(observed["snapshot"]["domain"],[1,2,3,11,12])
            self.assertEqual(observed["snapshot"]["retracted"],[])
            self.assertEqual(observed["snapshot"]["successors"],[])
            self.assertEqual(observed["snapshot"]["warrants"][-1]["evidence"],{"kind":"narrow","premise":20})
            self.assertEqual(observed["snapshot"]["warrants"][2]["evidence"]["premises"],deps)
            for record in records:
                self.assertEqual(record["binding"]["inputHashes"],[route.sha(self.raw[id])])
                self.assertEqual(record["binding"]["modelHash"],route.MODEL)

    def test_global_exhibited_point_keeps_selected_witness_and_model_identity(self):
        for row in self.cases.values():
            snapshot=row["native_results"]["normal"]["snapshot"]
            side=next(w for w in snapshot["warrants"] if w["id"]==20)
            tight=next(w for w in snapshot["warrants"] if w["id"]==120)
            self.assertIn("exhibited_point",side["binding"]["statementHash"])
            self.assertIn("selected-model:side",side["binding"]["statementHash"])
            self.assertIn("selected-model:tight",tight["binding"]["statementHash"])
            self.assertIn("selected-witness:side-premise",side["binding"]["statementHash"])
            self.assertNotEqual(side["binding"]["statementHash"],tight["binding"]["statementHash"])
            self.assertEqual(side["binding"]["scopeHash"],tight["binding"]["scopeHash"])
            self.assertTrue(side["binding"]["scopeHash"].endswith(":global-conditional-theory"))

    def test_checked_empty_tight_countermodel_and_soundness_contracts(self):
        self.assertTrue(self.compiled["kernel_checked"])
        self.assertEqual(self.compiled["compile_exit_code"],0)
        self.assertEqual(self.compiled["checker_exit_code"],0)
        self.assertEqual(set(self.compiled["axioms"]),{"propext","Quot.sound"})
        self.assertNotIn("sorryAx",(route.SCRATCH/"compile.log").read_text(encoding="utf-8"))
        for row in self.cases.values():
            self.assertEqual(row["native_results"]["normal"]["countermodel"],
                {"tight_empty":True,"side_inhabited":True,"same_witness_not_tight":True})
        source=route.HARNESS.read_text(encoding="utf-8")
        self.assertIn("structure World (Point : Type)",source)
        self.assertIn("theorem native_fold_held_sound (Point : Type)",source)
        self.assertIn("∃ x, x = ctx.1.exhibited ∧ ctx.1.side x",source)
        self.assertIn("theorem countermodel_join_not_global",source)
        self.assertIn("theorem accepting_theory_inhabited",source)

    def test_event_reversal_and_exact_duplicates_preserve_complete_results(self):
        for row in self.cases.values():
            first={k:v for k,v in row["native_results"]["normal"].items() if k!="mode"}
            for mode,observed in row["native_results"].items():
                with self.subTest(case=row["id"],mode=mode):
                    self.assertEqual({k:v for k,v in observed.items() if k!="mode"},first)

    def test_withheld_premises_remove_only_their_supported_closure_and_refuse_joint(self):
        for id in route.CASES:
            a=self.controls[(id,"withheld_universal")]["native_result"]
            b=self.controls[(id,"withheld_point")]["native_result"]
            self.assertEqual(a["state"]["supports"],[20])
            self.assertEqual(a["state"]["held"],[2])
            self.assertEqual(a["route_licensed"],[False,False])
            self.assertEqual(b["state"]["supports"],[10,110])
            self.assertEqual(b["state"]["held"],[1,11])
            self.assertNotIn(20,[w["id"] for w in b["snapshot"]["warrants"]])

    def test_wrong_binding_or_wrong_dependency_refuses_actual_universal_transfer(self):
        for id in route.CASES:
            for mode in ("wrong_binding","wrong_dependency"):
                observed=self.controls[(id,mode)]["native_result"]
                with self.subTest(case=id,mode=mode):
                    self.assertEqual(observed["state"]["supports"],[10,20])
                    self.assertEqual(observed["route_licensed"],[False,False])
                    self.assertNotIn(3,observed["state"]["held"])

    def test_point_identity_model_and_pointwise_laundering_cannot_create_tight_existence(self):
        for id in route.CASES:
            for mode in ("wrong_point_identity","wrong_model","pointwise_laundering"):
                observed=self.controls[(id,mode)]["native_result"]
                with self.subTest(case=id,mode=mode):
                    self.assertEqual(observed["state"]["supports"],[10,20,110])
                    self.assertNotIn(12,observed["state"]["held"])
                    self.assertNotIn(3,observed["state"]["held"])
                    self.assertFalse(observed["additional_tight_membership"])

    def test_extra_justified_same_witness_tight_membership_accepts_separate_join_control(self):
        for id in route.CASES:
            control=self.controls[(id,"justified_tight_membership")]
            observed=control["native_result"]
            self.assertFalse(control["corpus_pass"])
            self.assertEqual(control["observed"],"ACCEPT")
            self.assertEqual(observed["state"]["held"],[1,2,3,11,12])
            self.assertEqual(observed["state"]["supports"],[10,20,120,110,30])
            self.assertTrue(observed["additional_tight_membership"])
            self.assertEqual(observed["route_licensed"],[True,True])
            self.assertFalse(observed["narrow_checks"]["exhibited_point"])
            receipt=next(w for w in observed["snapshot"]["warrants"] if w["id"]==120)["evidence"]
            self.assertEqual(receipt,{"kind":"receipt","data":"additional:justified-tight-membership-of-same-witness"})

    def test_native_unknown_fields_wrong_identity_kind_or_selected_route_fail_closed(self):
        case=json.loads(self.raw["GP-X179"])
        paths=[("inputs",),("inputs","premises",1),("inputs","premises",1,"route",0)]
        for index,path in enumerate(paths):
            changed=copy.deepcopy(case);node=changed
            for key in path: node=node[key]
            node["verified"]=True
            observed,_=route.execute((route.encoded(changed)+"\n").encode(),"test-unknown-"+str(index),"normal",self.compiled)
            with self.subTest(path=path):
                self.assertEqual(observed,{"status":"MALFORMED","error":"unexpected field: verified"})
        for key,value in (("statement_class","universal_property"),("context","tight"),
                          ("statement","some other exhibited witness")):
            changed=copy.deepcopy(case);changed["inputs"]["premises"][1][key]=value
            observed,_=route.execute((route.encoded(changed)+"\n").encode(),"test-wrong-"+key,"normal",self.compiled)
            self.assertEqual(observed,{"status":"MALFORMED","error":"wrong literal premise kind/statement/model"})
        changed=copy.deepcopy(case);changed["inputs"]["premises"][1]["route"][0]["direction"]="forward"
        observed,_=route.execute((route.encoded(changed)+"\n").encode(),"test-wrong-route","normal",self.compiled)
        self.assertEqual(observed,{"status":"MALFORMED","error":"wrong literal selected route"})

    def test_complete_output_comparison_rejects_record_binding_domain_or_held_damage(self):
        case=json.loads(self.raw["GP-X179"]);original=self.cases["GP-X179"]["native_results"]["normal"]
        paths=[("snapshot","warrants"),("snapshot","currents"),("snapshot","domain"),("state","held"),
               ("state","supports"),("state","live_warrants"),("route_licensed",)]
        for path in paths:
            damaged=copy.deepcopy(original);node=damaged
            for key in path[:-1]: node=node[key]
            node[path[-1]]=[999]
            with self.subTest(path=path),self.assertRaises(ValueError):
                route.verify(case,self.raw["GP-X179"],damaged,"normal")
        damaged=copy.deepcopy(original);damaged["snapshot"]["warrants"][1]["binding"]["modelHash"]="changed"
        with self.assertRaises(ValueError): route.verify(case,self.raw["GP-X179"],damaged,"normal")

    def test_pin_layer_route_and_report_hashes_scope_boundaries(self):
        tags=json.loads((ROOT/"corpus/LAYER-TAGS.json").read_bytes())
        routes=json.loads((ROOT/"oracle/ROUTES.json").read_bytes())
        broken=copy.deepcopy(tags);next(r for r in broken["cases"] if r["id"]=="GP-X179")["sha256"]="wrong"
        with self.assertRaisesRegex(ValueError,"fixture bytes"): route.checked_case("GP-X179",broken,routes)
        broken=copy.deepcopy(routes);broken["commit"]="wrong"
        with self.assertRaisesRegex(ValueError,"route"): route.checked_case("GP-X180",tags,broken)
        self.assertEqual(self.report["source_contract"],route.source_contract())
        self.assertFalse(self.report["g2_pass"])
        self.assertFalse(self.report["underlying_algebraic_truth_certified"])
        self.assertFalse(self.report["production_profile_adoption"])
        self.assertEqual(self.report["corpus_executions"],8)
        self.assertEqual(self.report["separate_control_executions"],16)
        self.assertEqual(self.report["adapter_sha256"],route.sha(Path(route.__file__).read_bytes()))
        self.assertEqual(self.report["tests_sha256"],route.sha(Path(__file__).read_bytes()))
        self.assertEqual(self.compiled["harness_sha256"],route.sha(route.HARNESS.read_bytes()))
        self.assertEqual(self.compiled["olean_sha256"],route.sha(route.OLEAN.read_bytes()))
        for id in route.CASES:
            self.assertEqual((ROOT/"corpus/must"/(id+".json")).read_bytes(),self.raw[id])
            self.assertEqual(route.sha(self.raw[id]),route.HASHES[id])

if __name__=="__main__":
    unittest.main()
