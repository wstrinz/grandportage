"""Adversarial component controls for the three literal lifecycle slice fixtures."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("lifecycle_slice", ROOT / "tools/run-phase2-lifecycle-slice.py")
slice = importlib.util.module_from_spec(spec)
spec.loader.exec_module(slice)
RUNNER = Path(os.environ.get("GP_LIFECYCLE_EXE", str(slice.EXE)))

class LifecycleSliceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = slice.source_contract()
        tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
        cls.rows = {}
        for case_id in slice.CASES:
            case, raw = slice.checked_case(case_id, tags)
            records, links, orders = slice.translate(case, slice.sha(raw))
            outputs = {}
            for order, events in orders.items():
                outputs[order], _ = slice.execute("test-" + case_id + "-" + order, events, RUNNER)
            cls.rows[case_id] = (case, raw, records, links, orders, outputs)

    def test_both_native_orders_and_complete_contract(self):
        for case_id, (_, _, records, links, _, outputs) in self.rows.items():
            with self.subTest(case_id=case_id):
                for observed in outputs.values():
                    slice.verify(observed, records, links)
                self.assertEqual(outputs["old_then_new"], outputs["new_then_old"])

    def test_literal_identity_fields_and_annotations_preserved(self):
        for case_id, (case, raw, records, _, _, _) in self.rows.items():
            before = slice.encoded(case)
            steps = {step["object"]: step for step in case["inputs"]["history"]}
            for record in records:
                identity = record["identity"]
                key = identity["key"]
                obj = case["inputs"]["objects"][key]
                with self.subTest(case_id=case_id, key=key):
                    self.assertEqual(identity, dict(fixture=case_id, key=key, **obj,
                                                    replacement=steps[key].get("replacement")))
                    self.assertEqual(record["binding"]["statementHash"], slice.digest(identity))
                    self.assertEqual(record["binding"]["inputHashes"],
                                     [slice.sha(raw), slice.digest(obj), slice.digest(steps[key])])
                    self.assertEqual(record["binding"]["authority"], slice.AUTHORITY)
            self.assertEqual(before, slice.encoded(case))

    def test_each_source_field_affects_native_identity_binding(self):
        case, raw, _, _, _, outputs = self.rows["GP-X144"]
        for field in ("category", "name", "properties"):
            changed = copy.deepcopy(case)
            obj = changed["inputs"]["objects"]["object-1"]
            obj[field] = {"new": "literal property"} if field == "properties" else (
                "assertion" if field == "category" else "Renamed-M")
            records, links, _ = slice.translate(changed, slice.sha(raw))
            with self.subTest(field=field), self.assertRaises(ValueError):
                slice.verify(outputs["old_then_new"], records, links)
        changed = copy.deepcopy(case)
        changed["inputs"]["objects"]["renamed-key"] = changed["inputs"]["objects"].pop("object-1")
        for history in [changed["inputs"]["history"], changed["inputs"]["branch_comparison"]["common"]]:
            for step in history:
                if step["object"] == "object-1":
                    step["object"] = "renamed-key"
        records, links, _ = slice.translate(changed, slice.sha(raw))
        with self.assertRaises(ValueError):
            slice.verify(outputs["old_then_new"], records, links)

    def test_all_binding_fields_compared(self):
        _, _, records, links, _, outputs = self.rows["GP-X146"]
        for field in ("statementHash", "scopeHash", "modelHash", "inputHashes",
                      "authority", "authorityVersion", "kernelVersion"):
            observed = copy.deepcopy(outputs["old_then_new"])
            binding = observed["snapshot"]["warrants"][0]["binding"]
            binding[field] = [] if field == "inputHashes" else (
                99 if field.endswith("Version") else "tampered")
            with self.subTest(field=field), self.assertRaises(ValueError):
                slice.verify(observed, records, links)

    def test_retained_records_cannot_be_dropped_or_reassigned(self):
        _, _, records, links, _, outputs = self.rows["GP-X145"]
        mutations = [
            lambda s: s["warrants"].pop(),
            lambda s: s["currents"].pop(),
            lambda s: s["domain"].pop(),
            lambda s: s["warrants"][0].update(id=99),
            lambda s: s["warrants"][0].update(claim=99),
            lambda s: s["warrants"][0].update(version=99),
            lambda s: s["currents"][0].update(version=99),
            lambda s: s["retracted"].append(1),
            lambda s: s["warrants"][0].update(evidence={"kind": "citation", "text": "changed"}),
        ]
        for index, mutate in enumerate(mutations):
            observed = copy.deepcopy(outputs["old_then_new"])
            mutate(observed["snapshot"])
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                slice.verify(observed, records, links)

    def test_successor_endpoints_and_direction_compared(self):
        _, _, records, links, _, outputs = self.rows["GP-X144"]
        for altered in ([], [[links[0][1], links[0][0]]], [[1, links[0][1]]],
                        links + [[1, 2]]):
            observed = copy.deepcopy(outputs["old_then_new"])
            observed["snapshot"]["successors"] = altered
            with self.subTest(links=altered), self.assertRaises(ValueError):
                slice.verify(observed, records, links)

    def test_authority_and_held_query_outputs_compared(self):
        _, _, records, links, _, outputs = self.rows["GP-X146"]
        for field, value in (("held", [1]), ("supports", [1]),
                             ("resolve_fold_snapshot_equal", False),
                             ("admission", "receipt"), ("live_warrants", []),
                             ("held_queries", [{"claim": 1, "held": True}])):
            observed = copy.deepcopy(outputs["old_then_new"])
            observed[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                slice.verify(observed, records, links)

    def test_native_exact_duplicates_are_idempotent(self):
        for case_id, (_, _, records, links, orders, outputs) in self.rows.items():
            wire = copy.deepcopy(orders["old_then_new"])
            wire["events"] *= 2
            observed, _ = slice.execute("test-" + case_id + "-duplicates", wire, RUNNER)
            with self.subTest(case_id=case_id):
                slice.verify(observed, records, links)
                self.assertEqual(observed, outputs["old_then_new"])

    def test_native_conflicting_identity_refused(self):
        for case_id, (_, _, _, _, orders, _) in self.rows.items():
            wire = copy.deepcopy(orders["old_then_new"])
            duplicate = copy.deepcopy(next(e for e in wire["events"] if e["kind"] == "warrant"))
            duplicate["value"]["claim"] = 99
            wire["events"].append(duplicate)
            observed, _ = slice.execute("test-" + case_id + "-conflict", wire, RUNNER)
            with self.subTest(case_id=case_id):
                self.assertEqual(observed["status"], "MALFORMED")
                self.assertIn("conflicting warrant", observed["error"])

    def test_native_invalid_successor_links_refused(self):
        _, _, _, _, orders, _ = self.rows["GP-X144"]
        for label, mutation, error in (
                ("self", lambda e: e.update(target=e["successor"]), "self supersession"),
                ("missing", lambda e: e.update(target=999), "missing supersession endpoint")):
            wire = copy.deepcopy(orders["new_then_old"])
            mutation(next(e for e in wire["events"] if e["kind"] == "supersede"))
            observed, _ = slice.execute("test-link-" + label, wire, RUNNER)
            with self.subTest(label=label):
                self.assertEqual(observed["status"], "MALFORMED")
                self.assertIn(error, observed["error"])

    def test_native_decoder_unknown_field_refused(self):
        _, _, _, _, orders, _ = self.rows["GP-X144"]
        wire = copy.deepcopy(orders["old_then_new"])
        wire["events"][0]["unknown"] = True
        observed, _ = slice.execute("test-unknown-field", wire, RUNNER)
        self.assertEqual(observed["status"], "MALFORMED")
        self.assertIn("unexpected field", observed["error"])

    def test_adapter_unsupported_contracts_refused(self):
        case, raw, _, _, _, _ = self.rows["GP-X146"]
        mutations = [
            lambda c: c["inputs"].update(question={"mathematical": True}),
            lambda c: c["inputs"].update(extra=True),
            lambda c: c["inputs"]["objects"]["object-1"].update(category="proof"),
            lambda c: c["inputs"]["history"].reverse(),
            lambda c: c["inputs"]["history"][-1]["replacement"].update(change="unknown"),
            lambda c: c["inputs"]["branch_comparison"].update(extra=[]),
        ]
        for index, mutate in enumerate(mutations):
            changed = copy.deepcopy(case)
            mutate(changed)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                slice.translate(changed, slice.sha(raw))

    def test_fixture_bytes_expectations_and_source_pins_unchanged(self):
        for case_id, (case, raw, _, _, _, _) in self.rows.items():
            with self.subTest(case_id=case_id):
                self.assertEqual((ROOT / "corpus/must" / (case_id + ".json")).read_bytes(), raw)
                self.assertEqual(case["expected"]["verdict"], "ACCEPT")
                self.assertEqual(case["sources"][0]["commit"], self.source["commit"])
                self.assertEqual(self.source["line"], 3297)

if __name__ == "__main__":
    unittest.main()
