"""Host/native mutation and preservation controls for the commissioned provenance slice."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("provenance_slice", ROOT / "tools/run-phase2-provenance-slice.py")
slice = importlib.util.module_from_spec(spec)
spec.loader.exec_module(slice)


# The historical oracle (oracle/history/checkout) is private custody material. A public snapshot
# (marked by PUBLIC-SNAPSHOT-RECEIPT.json) excludes it, and workspace CI replays it; anywhere else
# its absence fails.
HISTORY_PRIVATE = ((ROOT / "PUBLIC-SNAPSHOT-RECEIPT.json").exists()
                   and not (ROOT / "oracle/history/checkout").is_dir())


@unittest.skipIf(HISTORY_PRIVATE, "public snapshot: the historical oracle is private")
class ProvenanceSliceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.initial_cases = slice.checked_cases()
        cls.original_shared = (ROOT / "tools/run-phase2-slice.py").read_bytes()
        cls.original_aggregate = (ROOT / "reports/PHASE-2-SLICE.json").read_bytes()
        cls.source = slice.source_contract()
        cls.rows = {}
        for case, raw, route in cls.initial_cases:
            translated = slice.translate(case)
            if translated is None:
                cls.rows[case["id"]] = (case, raw, None)
                continue
            registry, events, baseline, literal, provenance, fidelity = translated
            observed, _ = slice.execute("test-" + case["id"], registry, events)
            positive = None if baseline is None else slice.execute("test-" + case["id"] + "-positive", *baseline)[0]
            cls.rows[case["id"]] = (case, raw, (registry, events, baseline, observed, positive,
                                                   literal, provenance, fidelity))

    def test_all_eight_native_results_and_six_separate_positive_contrasts(self):
        for case_id, (_, _, translated) in self.rows.items():
            if translated is not None:
                _, events, baseline, observed, positive, *_ = translated
                with self.subTest(case_id=case_id):
                    slice.verify(observed, events, [1] if case_id in slice.CASES[-2:] else [])
                    if positive is not None:
                        slice.verify(positive, baseline[1], [1])

    def test_literal_claim_model_and_polynomial_inputs(self):
        for case_id, (_, _, translated) in self.rows.items():
            if translated is None:
                continue
            registry, _, _, _, _, literal, *_ = translated
            generator = "x^2" if case_id == "GP-X169" else "x"
            with self.subTest(case_id=case_id):
                self.assertEqual(literal, slice.source_records(generator))
                self.assertEqual(registry["clauses"][0]["generators"],
                                 [slice.shared.POLYNOMIALS[generator]])
                self.assertEqual(registry["clauses"][0]["target"], slice.shared.POLYNOMIALS["x"])
                self.assertEqual(literal["model"]["id"], "M")
                self.assertEqual(literal["claim"]["id"], "C")
                self.assertEqual(literal["claim"]["model"], "M")

    def test_literal_producer_backend_version_epoch_values_retained(self):
        for case_id in slice.CASES[:4]:
            case, _, translated = self.rows[case_id]
            registry, events, baseline, *_ = translated
            field, value = next(iter(case["inputs"]["mutation"].items()))
            current = baseline[0]["clauses"][0]["binding"]
            for binding in (registry["receipts"][0]["binding"], events["events"][1]["value"]["binding"]):
                with self.subTest(case_id=case_id):
                    if field in ("verifier", "backend"):
                        self.assertEqual(json.loads(binding["authority"])[field], value)
                        self.assertNotEqual(binding["authority"], current["authority"])
                    else:
                        native = {"verifier_version": "authorityVersion", "kernel_epoch": "kernelVersion"}[field]
                        self.assertEqual(binding[native], value)
                        self.assertNotEqual(binding[native], current[native])
            self.assertEqual(registry["receipts"][0]["name"], "v.C.mismatch." + field)
            self.assertEqual(registry["clauses"][0]["binding"], current)
            self.assertEqual(events["events"][0]["value"]["binding"], current)

    def test_repairing_mismatched_artifact_binding_restores_actual_replay(self):
        for case_id in slice.CASES[:4]:
            _, _, translated = self.rows[case_id]
            registry, events, *_ = copy.deepcopy(translated)
            binding = registry["clauses"][0]["binding"]
            registry["receipts"][0]["binding"] = copy.deepcopy(binding)
            events["events"][1]["value"]["binding"] = copy.deepcopy(binding)
            observed, _ = slice.execute("test-repaired-" + case_id, registry, events)
            with self.subTest(case_id=case_id):
                slice.verify(observed, events, [1])

    def test_semantic_input_keeps_old_artifact_and_new_current(self):
        _, _, translated = self.rows["GP-X169"]
        registry, events, baseline, *_ = translated
        self.assertEqual(registry["receipts"], baseline[0]["receipts"])
        self.assertEqual(events["events"][1], baseline[1]["events"][1])
        old = baseline[0]["clauses"][0]["binding"]
        new = registry["clauses"][0]["binding"]
        self.assertEqual(new["statementHash"], old["statementHash"])
        self.assertNotEqual(new["modelHash"], old["modelHash"])
        self.assertNotEqual(new["inputHashes"], old["inputHashes"])
        self.assertEqual(new["authority"], old["authority"])

    def test_fresh_binding_cannot_fake_false_x_in_x_squared_replay(self):
        _, _, translated = self.rows["GP-X169"]
        registry, events, *_ = copy.deepcopy(translated)
        binding = registry["clauses"][0]["binding"]
        registry["receipts"][0]["binding"] = copy.deepcopy(binding)
        events["events"][1]["value"]["binding"] = copy.deepcopy(binding)
        observed, _ = slice.execute("test-semantic-fresh-binding-false-identity", registry, events)
        slice.verify(observed, events, [])
        self.assertEqual(observed["authority"]["live_warrants"], [10])
        self.assertEqual(observed["authority"]["supports"], [])

    def test_legacy_event_fully_readable_and_inactive(self):
        _, _, translated = self.rows["GP-X170"]
        registry, events, _, observed, _, _, provenance, _ = translated
        self.assertEqual(registry["receipts"], [])
        w = observed["identity"]["warrants"][0]
        self.assertEqual(w["evidence"]["kind"], "citation")
        self.assertEqual(json.loads(w["evidence"]["text"]), provenance["retained_legacy_event"])
        self.assertEqual(w["binding"]["authorityVersion"], 0)
        self.assertEqual(w["binding"]["kernelVersion"], 0)
        self.assertEqual(observed["authority"]["held"], [])
        self.assertEqual(observed["authority"]["live_warrants"], [])
        self.assertEqual(provenance["absent_source_producer_fields"],
                         ["verifier", "verifier_version", "kernel_epoch", "backend"])
        self.assertEqual(w, events["events"][1]["value"])

    def test_complete_native_identity_not_just_counts_is_compared(self):
        _, _, translated = self.rows["GP-X165"]
        _, events, _, observed, *_ = translated
        for field in ("statementHash", "scopeHash", "modelHash", "inputHashes",
                      "authority", "authorityVersion", "kernelVersion"):
            tampered = copy.deepcopy(observed)
            binding = tampered["identity"]["warrants"][0]["binding"]
            binding[field] = [] if field == "inputHashes" else (
                77 if field.endswith("Version") else "tampered")
            with self.subTest(field=field), self.assertRaises(ValueError):
                slice.verify(tampered, events, [])
        tampered = copy.deepcopy(observed)
        tampered["identity"]["warrants"][0]["id"] = 11
        with self.assertRaises(ValueError):
            slice.verify(tampered, events, [])

    def test_support_held_current_results_cannot_be_forged(self):
        _, _, translated = self.rows["GP-X168"]
        _, events, _, observed, *_ = translated
        for field, value in (("held", [1]), ("supports", [10]), ("live_warrants", [10]),
                             ("domain", [2]), ("retracted", [10]), ("successors", [[10,11]])):
            tampered = copy.deepcopy(observed)
            tampered["authority"][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                slice.verify(tampered, events, [])

    def test_unknown_inputs_rejected_and_orders_bound_to_retained_constructor(self):
        for case_id, (case, _, _) in self.rows.items():
            changed = copy.deepcopy(case)
            changed["inputs"]["unrecorded"] = True
            with self.subTest(case_id=case_id), self.assertRaises(ValueError):
                slice.translate(changed)
        source = slice.retained_order_contract()
        self.assertEqual(source["source_current_epoch"], 12)
        self.assertEqual(source["source_stale_epoch"], 11)
        a = self.rows["GP-X171"][2]
        b = self.rows["GP-X172"][2]
        self.assertEqual(a[3], b[3])
        self.assertEqual(a[1]["events"][1:], list(reversed(b[1]["events"][1:])))
        self.assertEqual(a[3]["authority"]["supports"], [10])
        self.assertEqual([w["id"] for w in a[3]["identity"]["warrants"]], [10, 11])
        self.assertEqual([w["binding"]["kernelVersion"] for w in a[3]["identity"]["warrants"]], [1, 0])

    def test_report_executed_unexecuted_and_positive_counts_honest(self):
        output = slice.SCRATCH / "test-provenance-report.json"
        report = slice.run(output)
        self.assertEqual(report["executed_case_count"], 8)
        self.assertEqual(report["unexecuted_case_count"], 0)
        self.assertEqual(report["positive_contrasts"], 6)
        self.assertFalse(report["complete_ten_case_slice"])
        self.assertFalse(report["g2_pass"])
        for row in report["cases"][-2:]:
            self.assertEqual(row["status"], "EXECUTED")
            self.assertEqual(row["expected"]["verdict"], "ACCEPT")
            self.assertTrue(row["full_fixture_contract"])
            self.assertEqual(row["observed"], "ACCEPT")
            self.assertIsNone(row["positive_contrast"])

    def test_all_fixture_bytes_pins_and_shared_aggregate_unchanged(self):
        for case, raw, route in self.initial_cases:
            with self.subTest(case_id=case["id"]):
                self.assertEqual((ROOT / "corpus/must" / (case["id"] + ".json")).read_bytes(), raw)
                self.assertEqual(case["sources"][0]["commit"], slice.PIN)
                self.assertEqual(route["kind"], "lifecycle")
        self.assertEqual((ROOT / "tools/run-phase2-slice.py").read_bytes(), self.original_shared)
        self.assertEqual((ROOT / "reports/PHASE-2-SLICE.json").read_bytes(), self.original_aggregate)
        self.assertEqual(self.source["commit"], slice.PIN)

if __name__ == "__main__":
    unittest.main()
