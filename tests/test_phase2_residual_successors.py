"""Finite native controls for null priors, residual heads and split successors."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("residual",ROOT/"tools/run-phase2-residual-successors.py")
res=importlib.util.module_from_spec(spec)
spec.loader.exec_module(res)

class ResidualSuccessorsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tags=json.loads((ROOT/"corpus/LAYER-TAGS.json").read_bytes())
        cls.routes=json.loads((ROOT/"oracle/ROUTES.json").read_bytes())
        cls.rows={}
        for case_id in res.CASES:
            case,raw,row=res.checked_case(case_id,cls.tags,cls.routes)
            cls.rows[case_id]=(case,raw,res.translate(case,res.sha(raw)))
        cls.report=res.run(res.SCRATCH/"tests.report.json")
        cls.results={r["id"]:r for r in cls.report["cases"]}
        cls.controls={r["label"]:r for r in cls.report["controls"]}

    def test_complete_native_snapshots_both_orders_and_duplicates(self):
        for case_id,(_,_,plan) in self.rows.items():
            for order,run in self.results[case_id]["runs"].items():
                with self.subTest(case=case_id,order=order):
                    res.verify(run["native_result"],plan)
                    self.assertEqual(run["native_result"],self.results[case_id]["runs"]["forward"]["native_result"])

    def test_all_complete_literal_objects_and_history_steps_retained_and_bound(self):
        for case_id,(case,raw,plan) in self.rows.items():
            self.assertEqual(plan["history"],case["inputs"]["history"])
            self.assertEqual(plan["question"],case["inputs"]["question"])
            self.assertEqual(len(plan["records"]),len(case["inputs"]["objects"]))
            for identity,record in zip(plan["identities"],plan["records"]):
                with self.subTest(case=case_id,key=identity["source_key"]):
                    self.assertEqual(identity["object"],case["inputs"]["objects"][identity["source_key"]])
                    self.assertIn(identity["history_step"],case["inputs"]["history"])
                    self.assertEqual(json.loads(record["evidence"]["text"]),identity)
                    self.assertEqual(record["binding"]["statementHash"],res.digest(identity))
                    self.assertEqual(record["binding"]["inputHashes"],
                        [res.sha(raw),res.digest(identity["object"]),res.digest(identity["history_step"])])
                    for wire in plan["orders"].values():
                        self.assertIn({"kind":"warrant","value":record},wire["events"])

    def test_explicit_null_prior_is_retained_but_emits_no_fabricated_target(self):
        case,_,plan=self.rows["GP-X159"]
        self.assertIsNone(case["inputs"]["history"][4]["replacement"]["prior"])
        identity=next(i for i in plan["identities"] if i["object"]["name"]=="EXTRA")
        self.assertIsNone(identity["history_step"]["replacement"]["prior"])
        wire=plan["orders"]["forward"]["events"]
        self.assertEqual([e for e in wire if e["kind"]=="supersede"],
                         [{"kind":"supersede","target":3,"successor":4}])
        self.assertEqual([e["value"]["id"] for e in wire if e["kind"]=="warrant"],[1,2,3,4,5])
        self.assertEqual(plan["links"],[[3,4]])

    def test_native_residual_relation_heads_exactly_at_IV_PD_refuse_literal_clearance(self):
        run=self.results["GP-X159"]["runs"]["forward"]
        self.assertEqual(run["native_result"]["status"],"OK")
        self.assertEqual(run["native_result"]["live_warrants"],[1,2,4,5])
        q=run["native_identity_projection"]
        self.assertEqual(q["live_context_ids"],[1,2])
        self.assertEqual(q["live_relation_heads"],[
            {"id":4,"name":"E-IV-PD-RESTRICT","source_context":"IV","target_context":"PD"},
            {"id":5,"name":"EXTRA","source_context":"IV","target_context":"PD"}])
        self.assertFalse(q["old_record_live"])
        self.assertTrue(q["old_record_retained"])
        self.assertEqual(q["literal_conclusion_verdict"],"REFUSE")

    def test_native_split_preserves_both_exact_links_live_successors_and_old_history(self):
        run=self.results["GP-X161"]["runs"]["forward"]
        self.assertEqual(run["native_result"]["snapshot"]["successors"],[[8,9],[8,10]])
        q=run["native_identity_projection"]
        self.assertEqual(q["successors"],[{"id":9,"name":"C2","live":True},{"id":10,"name":"C3","live":True}])
        self.assertTrue(q["old_record_retained"])
        self.assertFalse(q["old_record_live"])
        self.assertEqual(q["literal_conclusion_verdict"],"ACCEPT")
        case,_,plan=self.rows["GP-X161"]
        self.assertEqual(case["inputs"]["objects"]["object-4"]["properties"],
                         case["inputs"]["objects"]["object-5"]["properties"])
        self.assertNotEqual(plan["records"][-1]["id"],plan["records"][-2]["id"])

    def test_repair_extra_with_explicit_supersession_removes_only_named_head(self):
        q=self.controls["extra_explicitly_replaces_head"]["runs"]["forward"]["native_identity_projection"]
        self.assertEqual([h["name"] for h in q["live_relation_heads"]],["EXTRA"])
        self.assertEqual(q["literal_conclusion_verdict"],"ACCEPT")
        result=self.controls["extra_explicitly_replaces_head"]["runs"]["forward"]["native_result"]
        self.assertEqual(result["snapshot"]["successors"],[[3,4],[4,5]])
        self.assertEqual(result["live_warrants"],[1,2,5])

    def test_endpoint_control_projects_exact_pair_and_does_not_prefilter_native(self):
        run=self.controls["extra_at_different_endpoint_pair"]["runs"]["forward"]
        self.assertEqual(run["native_result"]["live_warrants"],[1,2,4,5])
        self.assertEqual([h["name"] for h in run["native_identity_projection"]["live_relation_heads"]],
                         ["E-IV-PD-RESTRICT"])
        extra=next(w for w in run["native_result"]["snapshot"]["warrants"] if w["id"]==5)
        self.assertEqual(json.loads(extra["evidence"]["text"])["object"]["properties"]["target_context"],"IV")
        self.assertEqual(run["native_identity_projection"]["literal_conclusion_verdict"],"ACCEPT")

    def test_missing_second_link_cannot_be_confused_with_retained_independent_record(self):
        run=self.controls["second_successor_link_missing"]["runs"]["forward"]
        self.assertEqual(run["native_result"]["live_warrants"],[6,7,9,10])
        self.assertEqual(run["native_result"]["snapshot"]["successors"],[[8,9]])
        self.assertEqual(run["native_identity_projection"]["successors"],[{"id":9,"name":"C2","live":True}])
        self.assertEqual(run["native_identity_projection"]["literal_conclusion_verdict"],"REFUSE")
        repaired=self.controls["both_split_links_repaired"]["runs"]["forward"]
        self.assertEqual(repaired["native_result"]["snapshot"]["successors"],[[8,9],[8,10]])

    def test_controls_order_independent_and_never_manufacture_held_authority(self):
        for row in self.report["cases"]+self.report["controls"]:
            first=row["runs"]["forward"]["native_result"]
            for run in row["runs"].values():
                self.assertEqual(run["native_result"],first)
                self.assertEqual(run["native_result"]["admission"],"refuseAll")
                self.assertEqual(run["native_result"]["held"],[])
                self.assertEqual(run["native_result"]["supports"],[])
                self.assertTrue(all(not q["held"] for q in run["native_result"]["held_queries"]))

    def test_native_missing_successor_record_is_exact_endpoint_failure(self):
        _,_,plan=self.rows["GP-X161"]
        wire=copy.deepcopy(plan["orders"]["forward"])
        wire["events"]=[e for e in wire["events"] if not(e["kind"]=="warrant" and e["value"]["id"]==10)]
        observed,_=res.execute("test-lost-successor-record",wire)
        self.assertEqual(observed,{"status":"MALFORMED","error":"missing supersession endpoint: 8->10"})

    def test_native_binding_mismatch_preserves_custody_but_disables_independent_head(self):
        _,_,plan=self.rows["GP-X159"]
        for field in plan["currents"][-1]["binding"]:
            wire=copy.deepcopy(plan["orders"]["forward"])
            current=next(e["value"] for e in wire["events"] if e["kind"]=="current" and e["value"]["claim"]==5)
            value=current["binding"][field]
            current["binding"][field]=(value+1 if type(value) is int else value+["wrong"] if isinstance(value,list) else value+"-wrong")
            observed,_=res.execute("test-binding-"+field,wire)
            with self.subTest(field=field):
                self.assertEqual(observed["status"],"OK")
                self.assertEqual(observed["live_warrants"],[1,2,4])
                self.assertIn(5,[w["id"] for w in observed["snapshot"]["warrants"]])
                with self.assertRaises(ValueError):
                    res.verify(observed,plan)

    def test_native_conflicting_identity_and_cycle_fail_closed(self):
        _,_,plan=self.rows["GP-X161"]
        wire=copy.deepcopy(plan["orders"]["forward"])
        bad=copy.deepcopy(plan["records"][-1]);bad["id"]=9
        wire["events"].append({"kind":"warrant","value":bad})
        observed,_=res.execute("test-identity-collision",wire)
        self.assertEqual(observed,{"status":"MALFORMED","error":"conflicting warrant contents: 9"})
        wire=copy.deepcopy(plan["orders"]["forward"])
        wire["events"].append({"kind":"supersede","target":9,"successor":8})
        observed,_=res.execute("test-back-cycle",wire)
        self.assertEqual(observed,{"status":"MALFORMED","error":"supersession cycle: 8"})

    def test_unknown_source_fields_unresolved_context_and_history_loss_fail_closed(self):
        case,raw,_=self.rows["GP-X159"]
        paths=[(),("inputs",),("inputs","objects","object-1"),("inputs","objects","object-1","properties"),
               ("inputs","objects","object-5","properties"),("inputs","history",4),
               ("inputs","history",4,"replacement"),("inputs","question")]
        for path in paths:
            changed=copy.deepcopy(case);node=changed
            for key in path:
                node=node[key]
            node["ignored"]=True
            with self.subTest(path=path),self.assertRaises(ValueError):
                res.translate(changed,res.sha(raw))
        changed=copy.deepcopy(case);changed["inputs"]["history"].pop()
        with self.assertRaisesRegex(ValueError,"history record loss"):
            res.translate(changed,res.sha(raw))
        changed=copy.deepcopy(case);changed["inputs"]["objects"]["object-5"]["properties"]["target_context"]="unknown"
        with self.assertRaisesRegex(ValueError,"unresolved source context"):
            res.translate(changed,res.sha(raw))

    def test_native_unknown_fields_fail_closed(self):
        _,_,plan=self.rows["GP-X159"]
        for kind in ("root","event","binding"):
            wire=copy.deepcopy(plan["orders"]["forward"])
            node=wire if kind=="root" else wire["events"][0] if kind=="event" else wire["events"][1]["value"]["binding"]
            node["ignored"]=True
            observed,_=res.execute("test-unknown-"+kind,wire)
            with self.subTest(kind=kind):
                self.assertEqual(observed,{"status":"MALFORMED","error":"unexpected field: ignored"})

    def test_complete_comparison_rejects_damaged_records_bindings_links_domain_and_liveness(self):
        for case_id,(_,_,plan) in self.rows.items():
            original=self.results[case_id]["runs"]["forward"]["native_result"]
            paths=[("snapshot","domain"),("snapshot","warrants"),("snapshot","currents"),
                   ("snapshot","successors"),("snapshot","retracted"),("live_warrants",),("held",),("supports",)]
            for path in paths:
                damaged=copy.deepcopy(original);node=damaged
                for key in path[:-1]:
                    node=node[key]
                node[path[-1]]=[999]
                with self.subTest(case=case_id,path=path),self.assertRaises(ValueError):
                    res.verify(damaged,plan)
            damaged=copy.deepcopy(original)
            damaged["snapshot"]["warrants"][0]["binding"]["modelHash"]="wrong"
            with self.assertRaises(ValueError):
                res.verify(damaged,plan)

    def test_source_layer_route_guards_and_final_hashes(self):
        tags=copy.deepcopy(self.tags)
        next(r for r in tags["cases"] if r["id"]=="GP-X159")["sha256"]="wrong"
        with self.assertRaisesRegex(ValueError,"fixture bytes"):
            res.checked_case("GP-X159",tags,self.routes)
        routes=copy.deepcopy(self.routes);routes["routes"]["GP-X161"]["action"]="no_rule"
        with self.assertRaisesRegex(ValueError,"route"):
            res.checked_case("GP-X161",self.tags,routes)
        self.assertEqual(self.report["source_contract"],res.source_contract())
        self.assertEqual(self.report["runner_sha256"],res.sha(res.EXE.read_bytes()))
        self.assertEqual(self.report["adapter_sha256"],res.sha(Path(res.__file__).read_bytes()))
        self.assertEqual(self.report["tests_sha256"],res.sha(Path(__file__).read_bytes()))
        self.assertFalse(self.report["g2_pass"])
        self.assertEqual(self.report["corpus_native_executions"],8)
        self.assertEqual(self.report["control_native_executions"],16)
        for case_id,(case,raw,_) in self.rows.items():
            self.assertEqual((ROOT/"corpus/must"/(case_id+".json")).read_bytes(),raw)
            self.assertEqual(res.sha(raw),res.HASHES[case_id])
            self.assertEqual(self.results[case_id]["expected"],case["expected"])
        for row in self.report["cases"]+self.report["controls"]:
            label=row.get("id",row.get("label"))
            for order,run in row["runs"].items():
                self.assertEqual(run["input_sha256"],res.sha((res.SCRATCH/(label+"-"+order+".events.json")).read_bytes()))

if __name__=="__main__":
    unittest.main()
