"""Finite controls for native retraction identity, complete custody, and isolation."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("retraction_slice", ROOT / "tools/run-phase2-retraction-slice.py")
slice = importlib.util.module_from_spec(spec)
spec.loader.exec_module(slice)
RUNNER = Path(os.environ.get("GP_LIFECYCLE_EXE", str(slice.EXE)))

class RetractionSliceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = slice.source_contract()
        cls.tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
        cls.routes = json.loads((ROOT / "oracle/ROUTES.json").read_bytes())
        cls.rows = {}
        for case_id in slice.CASES:
            case, raw, row = slice.checked_case(case_id, cls.tags, cls.routes)
            plan = slice.translate(case, slice.sha(raw))
            outputs = {label: slice.execute("test-" + case_id + "-" + label, wire, RUNNER)[0]
                       for label, wire in plan["orders"].items()}
            cls.rows[case_id] = case, raw, row, plan, outputs
        cls.controls = slice.controls(cls.rows["GP-X148"][3], RUNNER)

    def test_complete_native_outputs_in_both_orders_with_duplicates(self):
        for case_id, (_, _, _, plan, outputs) in self.rows.items():
            for label, observed in outputs.items():
                with self.subTest(case=case_id, order=label):
                    slice.verify(observed, plan)
                    self.assertEqual(observed, outputs["forward"])

    def test_identical_context_repeat_retains_one_complete_record(self):
        case, _, _, plan, outputs = self.rows["GP-X142"]
        self.assertEqual(len(case["inputs"]["history"]), 2)
        self.assertEqual(len([e for e in plan["orders"]["forward"]["events"] if e["kind"] == "warrant"]), 2)
        self.assertEqual(outputs["forward"]["snapshot"]["warrants"], plan["records"])
        self.assertEqual(len(plan["records"]), 1)
        self.assertEqual(json.loads(plan["records"][0]["evidence"]["text"])["object"],
                         case["inputs"]["objects"]["object-1"])

    def test_same_identifier_keeps_same_native_id_across_fixtures_and_history_order(self):
        for case, raw, _, plan, _ in self.rows.values():
            self.assertEqual(plan["ids"], {n: slice.IDENTIFIERS[n] for n in plan["ids"]})
            changed = copy.deepcopy(case)
            changed["inputs"]["history"].reverse()
            other = slice.translate(changed, slice.sha(raw))
            self.assertEqual(other["ids"], plan["ids"])
            self.assertEqual(other["records"], plan["records"])
            self.assertEqual(other["targets"], plan["targets"])
        self.assertEqual(self.rows["GP-X147"][3]["ids"]["I"], self.rows["GP-X148"][3]["ids"]["I"])

    def test_every_literal_object_and_history_step_is_retained_and_bound(self):
        for case, raw, _, plan, outputs in self.rows.values():
            for record, identity in zip(plan["records"], plan["identities"]):
                key = identity["source_key"]
                self.assertEqual(identity["object"], case["inputs"]["objects"][key])
                self.assertIn(identity["history_step"], case["inputs"]["history"])
                self.assertEqual(json.loads(record["evidence"]["text"]), identity)
                self.assertEqual(record["binding"]["statementHash"], slice.digest(identity))
                self.assertEqual(record["binding"]["inputHashes"],
                                 [slice.sha(raw), slice.digest(identity["object"]), slice.digest(identity["history_step"])])
                self.assertIn(record, outputs["forward"]["snapshot"]["warrants"])
            self.assertEqual(plan["history"], case["inputs"]["history"])

    def test_native_targeted_retraction_keeps_history_and_removes_I_liveness(self):
        for case_id in ("GP-X147", "GP-X148"):
            _, _, _, plan, outputs = self.rows[case_id]
            observed = outputs["forward"]
            self.assertEqual(observed["snapshot"]["retracted"], [plan["ids"]["I"]])
            self.assertNotIn(plan["ids"]["I"], observed["live_warrants"])
            self.assertIn(plan["ids"]["I"], [r["id"] for r in observed["snapshot"]["warrants"]])
            self.assertIn(plan["ids"]["I"], [e["value"]["id"] for e in plan["orders"]["forward"]["events"]
                                           if e["kind"] == "warrant"])
            self.assertEqual(observed["snapshot"]["successors"], [])

    def test_identical_inference_properties_do_not_collapse_separate_identity(self):
        case, _, _, plan, outputs = self.rows["GP-X148"]
        self.assertEqual(case["inputs"]["objects"]["object-4"]["properties"],
                         case["inputs"]["objects"]["object-5"]["properties"])
        self.assertNotEqual(plan["ids"]["I"], plan["ids"]["I2"])
        self.assertIn(plan["ids"]["I2"], outputs["forward"]["live_warrants"])
        self.assertEqual(plan["query_id"], plan["ids"]["I2"])

    def test_withdrawal_is_complete_inert_custody_not_live_successor(self):
        for case_id in ("GP-X147", "GP-X148"):
            _, _, _, plan, outputs = self.rows[case_id]
            withdrawal = next(r for r in plan["records"] if r["id"] == plan["ids"]["R-I"])
            identity = json.loads(withdrawal["evidence"]["text"])
            self.assertEqual(identity["object"]["properties"], {"justification": "argument withdrawn"})
            self.assertEqual(identity["role"], "withdrawal-custody")
            self.assertNotIn(plan["ids"]["R-I"], outputs["forward"]["live_warrants"])
            self.assertNotIn(plan["ids"]["R-I"], [c["claim"] for c in plan["currents"]])
            self.assertIn(withdrawal, outputs["forward"]["snapshot"]["warrants"])

    def test_no_checked_truth_means_no_held_or_supports(self):
        for _, _, _, _, outputs in self.rows.values():
            for observed in outputs.values():
                self.assertEqual(observed["admission"], "refuseAll")
                self.assertEqual(observed["held"], [])
                self.assertEqual(observed["supports"], [])
                self.assertTrue(all(not q["held"] for q in observed["held_queries"]))

    def test_wrong_target_unknown_target_and_repaired_controls_are_native(self):
        controls = self.controls
        for label in ("missing_retraction", "wrong_neighbor_target", "unknown_target"):
            self.assertTrue(controls[label]["I_live"])
        self.assertFalse(controls["wrong_neighbor_target"]["I2_live"])
        self.assertEqual(controls["unknown_target"]["native_result"]["snapshot"]["retracted"], [999])
        self.assertFalse(controls["repaired_target_and_identity"]["I_live"])
        self.assertTrue(controls["repaired_target_and_identity"]["I2_live"])

    def test_wrong_immutable_identity_is_native_malformed(self):
        self.assertEqual(self.controls["wrong_immutable_identity"]["native_result"],
                         {"status": "MALFORMED", "error": "conflicting warrant contents: 4"})

    def test_unknown_native_wire_fields_fail_closed(self):
        for label in ("unknown_root_field", "unknown_event_field"):
            self.assertEqual(self.controls[label]["native_result"],
                             {"status": "MALFORMED", "error": "unexpected field: ignored"})

    def test_unknown_source_fields_fail_closed_at_every_input_level(self):
        case, raw, *_ = self.rows["GP-X148"]
        paths = [(), ("inputs",), ("inputs", "objects", "object-1"),
                 ("inputs", "objects", "object-1", "properties"),
                 ("inputs", "objects", "object-3", "properties"),
                 ("inputs", "objects", "object-4", "properties"),
                 ("inputs", "objects", "object-6", "properties"),
                 ("inputs", "history", 0), ("inputs", "history", 5, "replacement"),
                 ("inputs", "question")]
        for path in paths:
            changed = copy.deepcopy(case)
            node = changed
            for key in path:
                node = node[key]
            node["ignored"] = True
            with self.subTest(path=path), self.assertRaises(ValueError):
                slice.translate(changed, slice.sha(raw))

    def test_unresolved_premise_context_target_and_query_fail_closed(self):
        case, raw, *_ = self.rows["GP-X148"]
        paths = [("objects", "object-3", "properties", "context"),
                 ("objects", "object-4", "properties", "premise"),
                 ("history", 5, "replacement", "prior"), ("question", "object")]
        for path in paths:
            changed = copy.deepcopy(case)
            node = changed["inputs"]
            for key in path[:-1]:
                node = node[key]
            node[path[-1]] = "unknown"
            with self.subTest(path=path), self.assertRaises(ValueError):
                slice.translate(changed, slice.sha(raw))

    def test_nonempty_transport_route_is_precise_unexecuted_mismatch(self):
        case, raw, *_ = self.rows["GP-X148"]
        changed = copy.deepcopy(case)
        changed["inputs"]["objects"]["object-4"]["properties"]["transport_route"] = ["unknown"]
        with self.assertRaisesRegex(ValueError, "unsupported transport route"):
            slice.translate(changed, slice.sha(raw))

    def test_full_comparison_rejects_domain_record_binding_target_or_liveness_damage(self):
        _, _, _, plan, outputs = self.rows["GP-X148"]
        paths = [("snapshot", "domain"), ("snapshot", "currents"), ("snapshot", "warrants"),
                 ("snapshot", "retracted"), ("snapshot", "successors"), ("live_warrants"),
                 ("held"), ("supports")]
        for path in paths:
            changed = copy.deepcopy(outputs["forward"])
            path = (path,) if isinstance(path, str) else path
            node = changed
            for key in path[:-1]:
                node = node[key]
            node[path[-1]] = [999]
            with self.subTest(path=path), self.assertRaises(ValueError):
                slice.verify(changed, plan)
        changed = copy.deepcopy(outputs["forward"])
        changed["snapshot"]["warrants"][0]["binding"]["scopeHash"] = "wrong"
        with self.assertRaises(ValueError):
            slice.verify(changed, plan)

    def test_changed_pin_route_layer_or_fixture_hash_fails_closed(self):
        altered_tags = copy.deepcopy(self.tags)
        next(r for r in altered_tags["cases"] if r["id"] == "GP-X142")["sha256"] = "wrong"
        with self.assertRaisesRegex(ValueError, "fixture bytes"):
            slice.checked_case("GP-X142", altered_tags, self.routes)
        altered_routes = copy.deepcopy(self.routes)
        altered_routes["routes"]["GP-X147"]["action"] = "fold"
        with self.assertRaisesRegex(ValueError, "route"):
            slice.checked_case("GP-X147", self.tags, altered_routes)
        altered_routes["commit"] = "wrong"
        with self.assertRaisesRegex(ValueError, "route"):
            slice.checked_case("GP-X148", self.tags, altered_routes)
        altered_tags = copy.deepcopy(self.tags)
        next(r for r in altered_tags["cases"] if r["id"] == "GP-X148")["full_contract_required"] = False
        with self.assertRaisesRegex(ValueError, "layer"):
            slice.checked_case("GP-X148", altered_tags, self.routes)

    def test_unchanged_fixture_bytes_and_pinned_source_contract(self):
        for case_id, (_, raw, _, _, _) in self.rows.items():
            self.assertEqual((ROOT / "corpus/must" / (case_id + ".json")).read_bytes(), raw)
            self.assertEqual(slice.sha(raw), slice.HASHES[case_id])
        self.assertEqual(slice.source_contract(), self.source)

if __name__ == "__main__":
    unittest.main()
