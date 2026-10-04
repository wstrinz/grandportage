"""Finite native and adapter controls for declaration collision/idempotence."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("declaration_slice", ROOT / "tools/run-phase2-declaration-slice.py")
slice = importlib.util.module_from_spec(spec)
spec.loader.exec_module(slice)
RUNNER = Path(os.environ.get("GP_LIFECYCLE_EXE", str(slice.EXE)))

class DeclarationSliceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = slice.source_contract()
        cls.tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
        cls.routes = json.loads((ROOT / "oracle/ROUTES.json").read_bytes())
        cls.rows = {}
        for case_id in slice.CASES:
            case, raw, layer = slice.checked_case(case_id, cls.tags, cls.routes)
            payloads, records, orders = slice.translate(case, slice.sha(raw))
            outputs, hashes = {}, {}
            for label, wire in orders.items():
                outputs[label], hashes[label] = slice.execute("test-" + case_id + "-" + label, wire, RUNNER)
            cls.rows[case_id] = (case, raw, layer, payloads, records, orders, outputs, hashes)

    def test_original_native_contracts_both_orders_and_duplicates(self):
        for case_id, (case, _, _, _, records, _, outputs, _) in self.rows.items():
            with self.subTest(case_id=case_id):
                for observed in outputs.values():
                    if case["expected"]["verdict"] == "ACCEPT":
                        slice.verify_ok(observed, records)
                    else:
                        slice.verify_collision(observed, records)
                self.assertTrue(all(value == outputs["forward"] for value in outputs.values()))

    def test_identical_declaration_retains_exactly_one_full_native_record(self):
        _, _, _, _, records, _, outputs, _ = self.rows["GP-C03"]
        self.assertEqual(records[0], records[1])
        self.assertEqual(outputs["forward"]["snapshot"]["warrants"], [records[0]])
        self.assertEqual(outputs["forward"]["snapshot"]["domain"], [1])
        self.assertEqual(outputs["forward"]["held"], [])

    def test_conflict_is_a_native_warrant_collision_without_prefilter(self):
        for case_id in ("GP-A25a", "GP-X143"):
            _, _, _, _, records, orders, outputs, _ = self.rows[case_id]
            with self.subTest(case_id=case_id):
                self.assertEqual(records[0]["id"], records[1]["id"])
                self.assertNotEqual(records[0], records[1])
                self.assertEqual(len([e for e in orders["forward"]["events"] if e["kind"] == "warrant"]), 2)
                self.assertEqual(outputs["forward"], {"status": "MALFORMED", "error": "conflicting warrant contents: 1"})

    def test_every_literal_declaration_is_retained_in_bound_inert_payload(self):
        for case_id, (case, raw, _, payloads, records, _, _, _) in self.rows.items():
            self.assertEqual(payloads, slice.declarations(case))
            for payload, record in zip(payloads, records):
                with self.subTest(case_id=case_id, payload=payload):
                    identity = {"fixture": case_id, "declaration": payload}
                    self.assertEqual(json.loads(record["evidence"]["text"]), identity)
                    self.assertEqual(record["evidence"]["kind"], "citation")
                    self.assertEqual(record["binding"]["statementHash"], slice.digest(identity))
                    self.assertEqual(record["binding"]["inputHashes"], [slice.sha(raw), slice.digest(payload)])
                    self.assertEqual(record["binding"]["authority"], slice.AUTHORITY)
            if case_id == "GP-X143":
                for obj, payload in zip(case["inputs"]["objects"].values(), payloads):
                    self.assertEqual({k: payload[k] for k in obj}, obj)

    def test_order_changes_do_not_reassign_identifier_identity(self):
        for case_id, (case, raw, _, _, records, _, _, _) in self.rows.items():
            reversed_case = copy.deepcopy(case)
            if case_id == "GP-A25a":
                reversed_case["inputs"]["declarations"].reverse()
            elif case_id == "GP-X143":
                reversed_case["inputs"]["history"].reverse()
            _, reversed_records, _ = slice.translate(reversed_case, slice.sha(raw))
            with self.subTest(case_id=case_id):
                self.assertEqual(sorted(map(slice.encoded, records)),
                                 sorted(map(slice.encoded, reversed_records)))

    def test_repaired_equal_contents_and_distinct_identifiers_in_native_both_orders(self):
        for case_id in ("GP-A25a", "GP-X143"):
            case, raw, *_ = self.rows[case_id]
            for label, rename in (("equal_contents", False), ("distinct_identifiers", True)):
                repaired = slice.repaired_case(case, rename)
                _, records, orders = slice.translate(repaired, slice.sha(raw))
                outputs = []
                for order, wire in orders.items():
                    observed, _ = slice.execute("test-" + case_id + "-repair-" + label + "-" + order, wire, RUNNER)
                    slice.verify_ok(observed, records)
                    outputs.append(observed)
                with self.subTest(case_id=case_id, repair=label):
                    self.assertTrue(all(value == outputs[0] for value in outputs))
                    self.assertEqual(len(outputs[0]["snapshot"]["warrants"]), 2 if rename else 1)
                    self.assertEqual(outputs[0]["held"], [])
                    self.assertEqual((ROOT / "corpus/must" / (case_id + ".json")).read_bytes(), raw)

    def test_full_positive_record_and_snapshot_mutations_are_detected(self):
        _, _, _, _, records, _, outputs, _ = self.rows["GP-C03"]
        mutations = [
            lambda o: o["snapshot"]["warrants"].clear(),
            lambda o: o["snapshot"]["warrants"].append(copy.deepcopy(records[0])),
            lambda o: o["snapshot"]["domain"].append(2),
            lambda o: o["snapshot"]["currents"].append({"claim": 1}),
            lambda o: o["snapshot"]["retracted"].append(1),
            lambda o: o["snapshot"]["successors"].append([1, 2]),
        ]
        for field, value in (("id", 2), ("claim", 2), ("version", 2),
                             ("evidence", {"kind": "assertion"})):
            mutations.append(lambda o, f=field, v=value: o["snapshot"]["warrants"][0].update({f: v}))
        for field in records[0]["binding"]:
            value = [] if field == "inputHashes" else (99 if field.endswith("Version") else "changed")
            mutations.append(lambda o, f=field, v=value: o["snapshot"]["warrants"][0]["binding"].update({f: v}))
        for index, mutate in enumerate(mutations):
            observed = copy.deepcopy(outputs["forward"])
            mutate(observed)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                slice.verify_ok(observed, records)

    def test_authority_outputs_and_extra_output_fields_are_detected(self):
        _, _, _, _, records, _, outputs, _ = self.rows["GP-C03"]
        for field, value in (("admission", "receipt"), ("supports", [1]), ("held", [1]),
                             ("resolve_fold_snapshot_equal", False), ("live_warrants", [1]),
                             ("held_queries", [{"claim": 1, "held": True}]), ("unknown", True)):
            observed = copy.deepcopy(outputs["forward"])
            observed[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                slice.verify_ok(observed, records)

    def test_malformed_decoder_results_cannot_masquerade_as_collision_pass(self):
        _, _, _, _, records, _, _, _ = self.rows["GP-A25a"]
        for observed in ({"status": "OK"}, {"status": "MALFORMED", "error": "unexpected field"},
                         {"status": "MALFORMED", "error": "conflicting warrant contents: 99"},
                         {"status": "MALFORMED", "error": "conflicting warrant contents: 1", "held": []}):
            with self.subTest(observed=observed), self.assertRaises(ValueError):
                slice.verify_collision(observed, records)

    def test_unknown_adapter_input_fields_fail_closed_at_each_level(self):
        for case_id, (case, raw, *_rest) in self.rows.items():
            mutations = [lambda c: c["inputs"].update(extra=True)]
            if case_id == "GP-A25a":
                mutations.append(lambda c: c["inputs"]["declarations"][0].update(extra=True))
            elif case_id == "GP-X143":
                mutations.extend([
                    lambda c: c["inputs"]["objects"]["object-1"].update(extra=True),
                    lambda c: c["inputs"]["objects"]["object-1"]["properties"].update(extra=True),
                    lambda c: c["inputs"]["history"][0].update(extra=True),
                    lambda c: c["inputs"].update(question={"extra": True}),
                ])
            for index, mutate in enumerate(mutations):
                changed = copy.deepcopy(case)
                mutate(changed)
                with self.subTest(case_id=case_id, level=index), self.assertRaises(ValueError):
                    slice.translate(changed, slice.sha(raw))

    def test_unsupported_types_categories_and_incomplete_history_fail_closed(self):
        mutations = {
            "GP-A25a": [
                lambda c: c["inputs"]["declarations"][0].update(id=True),
                lambda c: c["inputs"]["declarations"][0].update(description=None),
                lambda c: c["inputs"].update(declarations=[]),
            ],
            "GP-C03": [
                lambda c: c["inputs"].update(repetitions=True),
                lambda c: c["inputs"].update(repetitions=3),
                lambda c: c["inputs"].update(id=""),
            ],
            "GP-X143": [
                lambda c: c["inputs"]["objects"]["object-1"].update(category="proof"),
                lambda c: c["inputs"]["objects"]["object-1"]["properties"].update(description=42),
                lambda c: c["inputs"]["history"][1].update(object="object-1"),
                lambda c: c["inputs"]["history"][1].update(object="missing"),
                lambda c: c["inputs"].update(vocabulary="other/v1"),
            ],
        }
        for case_id, changes in mutations.items():
            case, raw, *_ = self.rows[case_id]
            for index, mutate in enumerate(changes):
                changed = copy.deepcopy(case)
                mutate(changed)
                with self.subTest(case_id=case_id, mutation=index), self.assertRaises(ValueError):
                    slice.translate(changed, slice.sha(raw))

    def test_native_unknown_fields_fail_closed_at_wire_levels(self):
        _, _, _, _, _, orders, _, _ = self.rows["GP-C03"]
        locations = [
            lambda w: w,
            lambda w: w["events"][0],
            lambda w: w["events"][1]["value"],
            lambda w: w["events"][1]["value"]["binding"],
            lambda w: w["events"][1]["value"]["evidence"],
        ]
        for index, locate in enumerate(locations):
            wire = copy.deepcopy(orders["forward"])
            locate(wire)["unknown"] = True
            observed, _ = slice.execute("test-declaration-unknown-" + str(index), wire, RUNNER)
            with self.subTest(level=index):
                self.assertEqual(observed["status"], "MALFORMED")
                self.assertIn("unexpected field", observed["error"])

    def test_native_changed_duplicate_content_is_not_idempotent(self):
        _, _, _, _, _, orders, _, _ = self.rows["GP-C03"]
        wire = copy.deepcopy(orders["forward"])
        wire["events"][-1]["value"]["evidence"]["text"] += "different"
        observed, _ = slice.execute("test-identical-opposite-content", wire, RUNNER)
        self.assertEqual(observed, {"status": "MALFORMED", "error": "conflicting warrant contents: 1"})

    def test_case_bytes_source_pins_routes_and_layer_contracts_unchanged(self):
        self.assertEqual(slice.source_contract(), self.source)
        for case_id, (case, raw, layer, *_rest) in self.rows.items():
            checked, checked_raw, checked_layer = slice.checked_case(case_id, self.tags, self.routes)
            with self.subTest(case_id=case_id):
                self.assertEqual(checked_raw, raw)
                self.assertEqual(checked, case)
                self.assertEqual(checked_layer, layer)
                self.assertEqual(slice.sha(raw), slice.CASE_HASHES[case_id])
        self.assertEqual(self.source["functions"]["identical"]["line"], 36)
        self.assertEqual(self.source["functions"]["conflicting"]["line"], 43)

    def test_native_input_hashes_attest_exact_written_bytes(self):
        for case_id, (_, _, _, _, _, orders, _, hashes) in self.rows.items():
            for label, wire in orders.items():
                raw = (slice.SCRATCH / ("test-" + case_id + "-" + label + ".events.json")).read_bytes()
                with self.subTest(case_id=case_id, order=label):
                    self.assertEqual(slice.sha(raw), hashes[label])
                    self.assertEqual(json.loads(raw), wire)

    def test_checked_case_refuses_changed_registry_pin_or_expectation(self):
        for field, value in (("primary_layer", "profile"), ("sha256", "changed"),
                             ("full_contract_required", False), ("g2_kernel_eligible", False)):
            tags = copy.deepcopy(self.tags)
            next(row for row in tags["cases"] if row["id"] == "GP-C03")[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                slice.checked_case("GP-C03", tags, self.routes)
        routes = copy.deepcopy(self.routes)
        routes["routes"]["GP-A25a"]["conflict"] = False
        with self.assertRaises(ValueError):
            slice.checked_case("GP-A25a", self.tags, routes)

if __name__ == "__main__":
    unittest.main()
