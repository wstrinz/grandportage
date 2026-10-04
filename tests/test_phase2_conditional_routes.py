"""Native controls for exact conditional K2 routes and the final K3 join."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("routes_slice",ROOT / "tools/run-phase2-conditional-routes-slice.py")
slice = importlib.util.module_from_spec(spec); spec.loader.exec_module(slice)
RUNNER = Path(os.environ.get("GP_ROUTES_EXE",str(slice.EXE)))
def encoded(case):
    return (json.dumps(case,indent=2) + "\n").encode("utf-8")

class ConditionalRoutesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = slice.source_contract()
        cls.tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
        cls.routes = json.loads((ROOT / "oracle/ROUTES.json").read_bytes())
        cls.baseline = json.loads((ROOT / "reports/PHASE-2-BASELINE.json").read_bytes())
        cls.rows = {}
        for case_id in slice.CASES:
            case,raw,tag = slice.checked_case(case_id,cls.tags,cls.routes,cls.baseline)
            outputs = {mode:slice.execute(raw,"test-"+case_id+"-"+mode,mode,RUNNER)[0]
                       for mode in ("normal","reverse","duplicates")}
            cls.rows[case_id] = case,raw,tag,outputs

    def test_original_verdicts_complete_records_and_actual_fold(self):
        for case_id,(case,raw,_,outputs) in self.rows.items():
            for mode,output in outputs.items():
                with self.subTest(case=case_id,mode=mode):
                    self.assertEqual(slice.verify(case,raw,output),case["expected"]["verdict"])

    def test_orders_and_duplicates_agree(self):
        for case_id,(_,_,_,outputs) in self.rows.items():
            normalized = [{k:v for k,v in o.items() if k!="mode"} for o in outputs.values()]
            with self.subTest(case=case_id):
                self.assertTrue(all(o==normalized[0] for o in normalized))

    def test_empty_second_route_remains_physically_empty_at_side(self):
        case,_,_,outputs = self.rows["GP-X178"]; o=outputs["normal"]
        self.assertEqual(case["inputs"]["premises"][1]["route"],[])
        self.assertEqual(o["literal_inputs"]["premises"][1]["route"],[])
        self.assertEqual(o["route_endpoints"],["tight","side"])
        self.assertEqual(o["argument_dependency_ids"],[110,20])
        self.assertNotIn(120,[w["id"] for w in o["snapshot"]["warrants"]])
        self.assertNotIn(12,o["snapshot"]["domain"])
        self.assertNotIn(3,o["state"]["held"])

    def test_fixed_predicate_model_and_input_data_survive_actual_k2_restrictions(self):
        _,_,_,outputs=self.rows["GP-X177"]; records={w["id"]:w for w in outputs["normal"]["snapshot"]["warrants"]}
        for root,dest in ((10,110),(20,120)):
            with self.subTest(source=root):
                self.assertEqual(records[dest]["evidence"],{"kind":"narrow","premise":root})
                for field in ("statementHash","modelHash","inputHashes","kernelVersion"):
                    self.assertEqual(records[root]["binding"][field],records[dest]["binding"][field])
                self.assertNotEqual(records[root]["binding"]["scopeHash"],records[dest]["binding"]["scopeHash"])
        self.assertNotEqual(records[10]["binding"]["statementHash"],records[20]["binding"]["statementHash"])
        self.assertEqual(outputs["normal"]["narrow_checker"],"GP50.Semantic.acceptsNarrow")

    def test_actual_wrong_binding_predicate_dependency_model_and_withheld_premise_refuse(self):
        _,raw,_,_=self.rows["GP-X177"]
        for mode in ("wrong_binding","wrong_selected_predicate","wrong_dependency","wrong_model","withheld_second"):
            o,_=slice.execute(raw,"test-route-control-"+mode,mode,RUNNER)
            with self.subTest(mode=mode):
                self.assertNotIn(3,o["state"]["held"])
                self.assertNotIn(30,o["state"]["supports"])
                if mode=="withheld_second":
                    self.assertNotIn(20,[w["id"] for w in o["snapshot"]["warrants"]])

    def test_wrong_known_route_direction_or_endpoint_cannot_create_a_tight_restriction(self):
        case,_,_,_=self.rows["GP-X177"]
        for field,value in (("direction","forward"),("relation","second")):
            changed=copy.deepcopy(case);changed["inputs"]["premises"][0]["route"][0][field]=value
            raw=encoded(changed);o,_=slice.execute(raw,"test-wrong-route-"+field,runner=RUNNER)
            with self.subTest(field=field):
                self.assertEqual(slice.verify(changed,raw,o),"REFUSE")
                self.assertEqual(o["route_endpoints"][0],"loose")
                self.assertNotIn(110,[w["id"] for w in o["snapshot"]["warrants"]])

    def test_repair_only_empty_route_supplies_second_restriction(self):
        case,_,_,_=self.rows["GP-X178"]
        changed=copy.deepcopy(case)
        changed["inputs"]["premises"][1]["route"]=[{"relation":"second","direction":"reverse"}]
        raw=encoded(changed);o,_=slice.execute(raw,"test-repaired-second-route",runner=RUNNER)
        self.assertEqual(slice.verify(changed,raw,o),"ACCEPT")
        self.assertEqual(o["route_endpoints"],["tight","tight"])
        self.assertEqual(o["argument_dependency_ids"],[110,120])

    def test_expected_metadata_cannot_confer_or_revoke_authority(self):
        for case_id,(case,_,_,outputs) in self.rows.items():
            changed=copy.deepcopy(case);changed["expected"]={"verdict":"REFUSE" if case_id=="GP-X177" else "ACCEPT","reason":"force","verified":True}
            raw=encoded(changed);o,_=slice.execute(raw,"test-metadata-"+case_id,runner=RUNNER)
            with self.subTest(case=case_id):
                self.assertEqual(o["state"],outputs["normal"]["state"])
                self.assertEqual(slice.verify(changed,raw,o),case["expected"]["verdict"])

    def test_unknown_fields_wrong_selected_model_and_omitted_premise_fail_closed(self):
        case,_,_,_=self.rows["GP-X177"]
        mutations=[
            lambda c:c["inputs"].update(extra=True),
            lambda c:c["inputs"]["relations"][0].update(extra=True),
            lambda c:c["inputs"]["premises"][0].update(verified=True),
            lambda c:c["inputs"]["premises"][0]["route"][0].update(extra=True),
            lambda c:c["inputs"]["relations"][0].update(target="side"),
            lambda c:c["inputs"]["relations"][1].update(source="loose"),
            lambda c:c["inputs"]["premises"][0].update(context="side"),
            lambda c:c["inputs"]["premises"].pop(),
            lambda c:c["inputs"]["premises"][0]["route"][0].update(direction="sideways"),
            lambda c:c["inputs"].update(conclusion_text="both properties true"),
        ]
        for i,mutate in enumerate(mutations):
            changed=copy.deepcopy(case);mutate(changed)
            o,_=slice.execute(encoded(changed),"test-route-malformed-"+str(i),runner=RUNNER)
            with self.subTest(mutation=i):self.assertEqual(o["status"],"MALFORMED")

    def test_complete_snapshot_bindings_routes_and_hypotheses_are_compared(self):
        case,raw,_,outputs=self.rows["GP-X177"]
        mutations=[
            lambda o:o["snapshot"]["warrants"].pop(),
            lambda o:o["snapshot"]["currents"].pop(),
            lambda o:o.update(route_endpoints=["tight","side"]),
            lambda o:o.update(argument_dependency_ids=[110,20]),
            lambda o:o.update(named_hypotheses=["success"]),
            lambda o:o.update(conditional=False),
            lambda o:o["state"].update(held=[3]),
        ]
        for field in outputs["normal"]["snapshot"]["warrants"][0]["binding"]:
            value=[] if field=="inputHashes" else (99 if field.endswith("Version") else "changed")
            mutations.append(lambda o,f=field,v=value:o["snapshot"]["warrants"][0]["binding"].update({f:v}))
        for i,mutate in enumerate(mutations):
            o=copy.deepcopy(outputs["normal"]);mutate(o)
            with self.subTest(mutation=i),self.assertRaises(ValueError):slice.verify(case,raw,o)

    def test_case_bytes_expectations_pins_and_input_hashes_unchanged(self):
        self.assertEqual(slice.source_contract(),self.source)
        for case_id,(case,raw,tag,outputs) in self.rows.items():
            c,r,t=slice.checked_case(case_id,self.tags,self.routes,self.baseline)
            with self.subTest(case=case_id):
                self.assertEqual((c,r,t),(case,raw,tag))
                for mode,o in outputs.items():
                    self.assertEqual(o["source_digest"],slice.sha(raw))
                    self.assertEqual((slice.SCRATCH/("test-"+case_id+"-"+mode+".json")).read_bytes(),raw)

if __name__=="__main__":
    unittest.main()
