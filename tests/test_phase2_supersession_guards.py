"""Native guard, repaired-record, and complete-chain controls."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("supersession",ROOT/"tools/run-phase2-supersession-guards.py")
sup=importlib.util.module_from_spec(spec)
spec.loader.exec_module(sup)

class SupersessionGuardsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tags=json.loads((ROOT/"corpus/LAYER-TAGS.json").read_bytes())
        cls.routes=json.loads((ROOT/"oracle/ROUTES.json").read_bytes())
        cls.rows={}
        for case_id in sup.CASES:
            case,raw,row=sup.checked_case(case_id,cls.tags,cls.routes)
            cls.rows[case_id]=(case,raw,sup.translate(case,sup.sha(raw)))
        cls.report=sup.run(sup.SCRATCH/"tests.report.json")
        cls.results={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_native_exact_guards_in_both_orders_and_duplicates(self):
        for case_id,error in sup.ERRORS.items():
            for order,run in self.results[case_id]["runs"].items():
                with self.subTest(case=case_id,order=order):
                    self.assertEqual(run["native_result"],{"status":"MALFORMED","error":error})
                    self.assertIsNone(run["native_live_query"])
                    self.assertNotIn("snapshot",run["native_result"])

    def test_all_literal_objects_properties_and_history_are_bound_and_sent(self):
        for case_id,(case,raw,plan) in self.rows.items():
            self.assertEqual(plan["history"],case["inputs"]["history"])
            self.assertEqual(len(plan["records"]),len(case["inputs"]["objects"]))
            for identity,record in zip(plan["identities"],plan["records"]):
                key=identity["source_key"]
                self.assertEqual(identity["object"],case["inputs"]["objects"][key])
                self.assertIn(identity["history_step"],case["inputs"]["history"])
                self.assertEqual(json.loads(record["evidence"]["text"]),identity)
                self.assertEqual(record["binding"]["statementHash"],sup.digest(identity))
                self.assertEqual(record["binding"]["inputHashes"],
                    [sup.sha(raw),sup.digest(identity["object"]),sup.digest(identity["history_step"])])
                for label,wire in plan["orders"].items():
                    with self.subTest(case=case_id,key=key,order=label):
                        self.assertIn({"kind":"warrant","value":record},wire["events"])

    def test_self_missing_cycle_and_conflicting_withdrawal_not_prefiltered(self):
        self.assertIn({"kind":"supersede","target":4,"successor":4},
                      self.rows["GP-X153"][2]["orders"]["forward"]["events"])
        self.assertIn({"kind":"supersede","target":9,"successor":4},
                      self.rows["GP-X154"][2]["orders"]["forward"]["events"])
        self.assertNotIn(9,self.rows["GP-X154"][2]["identifier_ids"].values())
        for edge in ({"kind":"supersede","target":6,"successor":7},
                     {"kind":"supersede","target":7,"successor":6}):
            self.assertIn(edge,self.rows["GP-X155"][2]["orders"]["forward"]["events"])
        wire=self.rows["GP-X152"][2]["orders"]["forward"]["events"]
        self.assertIn({"kind":"retract","target":3},wire)
        self.assertIn({"kind":"supersede","target":3,"successor":4},wire)

    def test_finite_chain_retains_complete_snapshot_and_exact_live_relation_head(self):
        _,_,plan=self.rows["GP-X158"]
        for order,run in self.results["GP-X158"]["runs"].items():
            with self.subTest(order=order):
                observed=run["native_result"]
                sup.verify(observed,plan)
                self.assertEqual(observed["snapshot"]["warrants"],plan["records"])
                self.assertEqual(observed["snapshot"]["currents"],plan["currents"])
                self.assertEqual(observed["snapshot"]["successors"],[[3,4],[4,8]])
                self.assertEqual(run["native_live_query"],{"live_context_ids":[1,2],"live_relation_ids":[8]})
                self.assertEqual(observed["live_warrants"],[1,2,8])

    def test_undeclared_final_link_exposes_competing_live_relation_records(self):
        result=self.controls["chain_link_missing_competing_heads"]["runs"]["forward"]
        self.assertEqual(result["native_result"]["status"],"OK")
        self.assertEqual(result["native_live_query"]["live_relation_ids"],[4,8])
        self.assertEqual(result["native_result"]["snapshot"]["successors"],[[3,4]])
        self.assertEqual(result["native_result"]["held"],[])

    def test_repaired_controls_are_native_ok_complete_and_order_independent(self):
        for control in self.report["controls"]:
            first=control["runs"]["forward"]["native_result"]
            self.assertEqual(first["status"],"OK")
            self.assertFalse(control["corpus_pass"])
            for run in control["runs"].values():
                self.assertEqual(run["native_result"],first)
                self.assertEqual(run["native_result"]["held"],[])
                self.assertEqual(run["native_result"]["supports"],[])

    def test_missing_endpoint_repaired_by_complete_same_category_declaration(self):
        control=self.controls["missing_relation_declared"]
        ghost=next(i for i in control["literal_bound_identities"] if i["object"]["name"]=="GHOST")
        self.assertEqual(ghost["object"]["category"],"relation")
        self.assertEqual(set(ghost["object"]["properties"]),
                         {"source_context","target_context","relation_class","justification","coordinate_action"})
        run=control["runs"]["forward"]
        self.assertEqual(run["native_result"]["snapshot"]["successors"],[[9,4]])
        self.assertEqual(run["native_live_query"]["live_relation_ids"],[4])
        self.assertIn(9,[w["id"] for w in run["native_result"]["snapshot"]["warrants"]])

    def test_withdrawal_record_stays_inert_in_withdrawal_only_repair(self):
        control=self.controls["withdrawal_without_replacement"]
        result=control["runs"]["forward"]["native_result"]
        self.assertEqual(result["snapshot"]["retracted"],[3])
        self.assertEqual(result["snapshot"]["successors"],[])
        self.assertEqual([w["id"] for w in result["snapshot"]["warrants"]],[1,2,3,5])
        self.assertEqual(result["live_warrants"],[1,2])
        self.assertNotIn(5,[c["claim"] for c in result["snapshot"]["currents"]])

    def test_cycle_refusal_prevents_clearing_without_claiming_predecessor_defect_query(self):
        row=self.results["GP-X155"]
        self.assertEqual(row["question"],{"concerns":["unresolved_relation"]})
        reasons=[i["object"]["properties"]["unresolved_reason"] for i in row["literal_bound_identities"]
                 if i["object"]["category"]=="relation"]
        self.assertEqual(len(reasons),2)
        self.assertTrue(all(reasons))
        self.assertTrue(row["construction_refusal"])
        self.assertFalse(row["native_snapshot_available"])
        self.assertIn("does not implement",self.report["X155_diagnostic_boundary"])
        repaired=self.controls["cycle_broken_debt_retained"]
        repaired_reasons=[i["object"]["properties"]["unresolved_reason"] for i in repaired["literal_bound_identities"]
                          if i["object"]["category"]=="relation"]
        self.assertEqual(repaired_reasons,reasons)
        self.assertEqual(repaired["runs"]["forward"]["native_live_query"]["live_relation_ids"],[7])

    def test_native_record_loss_fails_missing_endpoint_and_full_comparison(self):
        _,_,plan=self.rows["GP-X158"]
        wire=copy.deepcopy(plan["orders"]["forward"])
        wire["events"]=[e for e in wire["events"] if not(e["kind"]=="warrant" and e["value"]["id"]==8)]
        observed,_=sup.execute("test-lost-head",wire)
        self.assertEqual(observed,{"status":"MALFORMED","error":"missing supersession endpoint: 4->8"})
        wire=copy.deepcopy(plan["orders"]["forward"])
        wire["events"]=[e for e in wire["events"] if not(e["kind"]=="warrant" and e["value"]["id"]==1)]
        observed,_=sup.execute("test-lost-context-record",wire)
        self.assertEqual(observed["status"],"OK")
        with self.assertRaisesRegex(ValueError,"complete native"):
            sup.verify(observed,plan)

    def test_native_changed_current_binding_disables_head_and_comparison_rejects(self):
        _,_,plan=self.rows["GP-X158"]
        wire=copy.deepcopy(plan["orders"]["forward"])
        for event in wire["events"]:
            if event["kind"]=="current" and event["value"]["claim"]==8:
                event["value"]["binding"]["modelHash"]="wrong-model"
        observed,_=sup.execute("test-mismatched-current-head",wire)
        self.assertEqual(observed["status"],"OK")
        self.assertEqual(observed["live_warrants"],[1,2])
        with self.assertRaises(ValueError):
            sup.verify(observed,plan)

    def test_native_conflicting_immutable_identity_fails_closed(self):
        _,_,plan=self.rows["GP-X158"]
        wire=copy.deepcopy(plan["orders"]["forward"])
        bad=copy.deepcopy(plan["records"][-1])
        bad["binding"]["statementHash"]="changed"
        wire["events"].append({"kind":"warrant","value":bad})
        observed,_=sup.execute("test-conflicting-record",wire)
        self.assertEqual(observed,{"status":"MALFORMED","error":"conflicting warrant contents: 8"})

    def test_unknown_input_fields_and_lost_literal_history_fail_closed(self):
        case,raw,_=self.rows["GP-X158"]
        paths=[(),("inputs",),("inputs","objects","object-1"),("inputs","objects","object-1","properties"),
               ("inputs","objects","object-3","properties"),("inputs","history",3),
               ("inputs","history",3,"replacement"),("inputs","question")]
        for path in paths:
            changed=copy.deepcopy(case);node=changed
            for key in path:
                node=node[key]
            node["ignored"]=True
            with self.subTest(path=path),self.assertRaises(ValueError):
                sup.translate(changed,sup.sha(raw))
        changed=copy.deepcopy(case);changed["inputs"]["history"].pop()
        with self.assertRaisesRegex(ValueError,"history record loss"):
            sup.translate(changed,sup.sha(raw))

    def test_native_unknown_fields_fail_closed_without_host_diagnostics(self):
        _,_,plan=self.rows["GP-X158"]
        for location in ("root","event","binding"):
            wire=copy.deepcopy(plan["orders"]["forward"])
            node=wire if location=="root" else wire["events"][0] if location=="event" else wire["events"][1]["value"]["binding"]
            node["ignored"]=True
            observed,_=sup.execute("test-unknown-"+location,wire)
            with self.subTest(location=location):
                self.assertEqual(observed,{"status":"MALFORMED","error":"unexpected field: ignored"})

    def test_source_route_and_layer_guards_reject_mismatches(self):
        for case_id in sup.CASES:
            tags=copy.deepcopy(self.tags)
            next(r for r in tags["cases"] if r["id"]==case_id)["sha256"]="wrong"
            with self.subTest(case=case_id),self.assertRaisesRegex(ValueError,"fixture bytes"):
                sup.checked_case(case_id,tags,self.routes)
        routes=copy.deepcopy(self.routes);routes["commit"]="wrong"
        with self.assertRaisesRegex(ValueError,"route"):
            sup.checked_case("GP-X155",self.tags,routes)
        tags=copy.deepcopy(self.tags)
        next(r for r in tags["cases"] if r["id"]=="GP-X158")["full_contract_required"]=False
        with self.assertRaisesRegex(ValueError,"layer"):
            sup.checked_case("GP-X158",tags,self.routes)

    def test_actual_report_hashes_original_bytes_and_g2_boundary(self):
        self.assertFalse(self.report["g2_pass"])
        self.assertEqual(self.report["case_count"],5)
        self.assertEqual(self.report["corpus_native_executions"],20)
        self.assertEqual(self.report["control_native_executions"],24)
        self.assertEqual(self.report["runner_sha256"],sup.sha(sup.EXE.read_bytes()))
        self.assertEqual(self.report["adapter_sha256"],sup.sha(Path(sup.__file__).read_bytes()))
        self.assertEqual(self.report["tests_sha256"],sup.sha(Path(__file__).read_bytes()))
        self.assertEqual(self.report["source_contract"],sup.source_contract())
        for case_id,(case,raw,_) in self.rows.items():
            self.assertEqual((ROOT/"corpus/must"/(case_id+".json")).read_bytes(),raw)
            self.assertEqual(sup.sha(raw),sup.HASHES[case_id])
            self.assertEqual(self.results[case_id]["expected"],case["expected"])
        for row in self.report["cases"]+self.report["controls"]:
            label=row.get("id",row.get("label"))
            for order,run in row["runs"].items():
                self.assertEqual(run["input_sha256"],sup.sha((sup.SCRATCH/(label+"-"+order+".events.json")).read_bytes()))

if __name__=="__main__":
    unittest.main()
