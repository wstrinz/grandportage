"""Native and proof-bound controls for the three conditional named partitions."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("conditional_partition", ROOT / "tools/run-phase2-conditional-partition-slice.py")
slice = importlib.util.module_from_spec(spec)
spec.loader.exec_module(slice)
RUNNER = Path(os.environ.get("GP_PARTITION_EXE", str(slice.EXE)))

def raw_case(case):
    return (json.dumps(case, ensure_ascii=True, indent=2) + "\n").encode("utf-8")

class ConditionalPartitionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = slice.source_contract()
        cls.tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
        cls.routes = json.loads((ROOT / "oracle/ROUTES.json").read_bytes())
        cls.baseline = json.loads((ROOT / "reports/PHASE-2-BASELINE.json").read_bytes())
        cls.rows = {}
        for case_id in slice.CASES:
            case, raw, tag = slice.checked_case(case_id, cls.tags, cls.routes, cls.baseline)
            outputs, hashes = {}, {}
            for mode in ("normal", "reverse", "duplicates"):
                outputs[mode], hashes[mode] = slice.execute(raw, "test-" + case_id + "-" + mode, mode, RUNNER)
            cls.rows[case_id] = (case, raw, tag, outputs, hashes)

    def test_original_conditional_verdicts_actual_fold_and_complete_records(self):
        for case_id, (case, raw, _, outputs, _) in self.rows.items():
            for mode, observed in outputs.items():
                with self.subTest(case_id=case_id, mode=mode):
                    self.assertEqual(slice.verify(case, raw, observed), case["expected"]["verdict"])

    def test_both_event_orders_and_duplicates_preserve_complete_native_result(self):
        for case_id, (_, _, _, outputs, _) in self.rows.items():
            normal = {k: v for k, v in outputs["normal"].items() if k != "mode"}
            for mode, observed in outputs.items():
                with self.subTest(case_id=case_id, mode=mode):
                    self.assertEqual({k: v for k, v in observed.items() if k != "mode"}, normal)

    def test_x183_right_premise_is_physically_absent(self):
        case, raw, _, outputs, _ = self.rows["GP-X183"]
        observed = outputs["normal"]
        self.assertEqual(case["inputs"]["premises"],
            [{"context": "left", "statement_class": "empty", "statement": "left branch is empty"}])
        self.assertEqual([w["id"] for w in observed["snapshot"]["warrants"]], [10,30,40])
        self.assertEqual(observed["argument_dependency_ids"], [10,40])
        self.assertEqual(observed["state"]["held"], [1,4])
        self.assertNotIn(2, observed["snapshot"]["domain"])
        self.assertNotIn("right branch is empty", observed["given"])
        self.assertNotIn(3, observed["state"]["held"])

    def test_x186_verified_coverage_is_held_but_omitted_from_argument(self):
        _, _, _, outputs, _ = self.rows["GP-X186"]
        observed = outputs["normal"]
        self.assertIn("exhaustive parent:[left,right]", observed["given"])
        self.assertEqual(observed["argument_dependency_ids"], [10,20])
        self.assertEqual(observed["state"]["supports"], [10,20,40])
        self.assertIn(4, observed["state"]["held"])
        self.assertNotIn(3, observed["state"]["held"])
        self.assertEqual(next(w for w in observed["snapshot"]["warrants"] if w["id"] == 30)["evidence"]["premises"], [10,20])

    def test_literal_names_statements_branch_list_and_all_premise_records_preserved(self):
        for case_id, (case, raw, _, outputs, _) in self.rows.items():
            records, dependencies = slice.expected_records(case, slice.sha(raw))
            observed = outputs["normal"]
            with self.subTest(case_id=case_id):
                self.assertEqual(observed["literal_inputs"], case["inputs"])
                self.assertEqual(observed["snapshot"]["warrants"], records)
                self.assertEqual(observed["literal_inputs"]["contexts"], ["parent","left","right"])
                self.assertEqual(observed["literal_inputs"]["cover"]["branches"], ["left","right"])
                self.assertEqual(observed["argument_dependency_ids"], dependencies)
            for record in records:
                with self.subTest(case_id=case_id, wid=record["id"]):
                    self.assertEqual(record["binding"]["statementHash"], slice.STATEMENTS[record["claim"]])
                    self.assertEqual(record["binding"]["modelHash"], slice.MODEL)
                    self.assertEqual(record["binding"]["inputHashes"], [slice.sha(raw)])

    def test_withheld_right_and_omitted_coverage_argument_block_actual_rule(self):
        case, raw, *_ = self.rows["GP-X184"]
        for mode in ("withheld_right", "omit_exhaustive_argument"):
            observed, _ = slice.execute(raw, "test-composition-" + mode, mode, RUNNER)
            with self.subTest(mode=mode):
                self.assertNotIn(3, observed["state"]["held"])
                self.assertNotIn(30, observed["state"]["supports"])
                self.assertIn(40, observed["state"]["supports"])
                if mode == "withheld_right":
                    self.assertNotIn(20, [w["id"] for w in observed["snapshot"]["warrants"]])
                else:
                    self.assertEqual(observed["argument_dependency_ids"], [10,20])
                    self.assertIn(20, observed["state"]["supports"])

    def test_wrong_selected_branch_model_binding_or_premise_identity_cannot_hold_parent(self):
        _, raw, *_ = self.rows["GP-X184"]
        expected_supports = {
            "wrong_branch": [10,40], "wrong_model": [10,20],
            "wrong_binding": [20,40], "wrong_premise_id": [10,40],
            "unverified_cover": [10,20],
        }
        for mode, supports in expected_supports.items():
            observed, _ = slice.execute(raw, "test-exact-registered-" + mode, mode, RUNNER)
            with self.subTest(mode=mode):
                self.assertEqual(observed["state"]["supports"], supports)
                self.assertNotIn(3, observed["state"]["held"])
                self.assertNotIn(30, observed["state"]["supports"])

    def test_removing_literal_right_premise_removes_its_record_without_failed_receipt(self):
        case, _, *_ = self.rows["GP-X184"]
        changed = copy.deepcopy(case)
        changed["inputs"]["premises"].pop()
        raw = raw_case(changed)
        observed, _ = slice.execute(raw, "test-literal-withheld-right", runner=RUNNER)
        self.assertEqual(slice.verify(changed, raw, observed), "REFUSE")
        self.assertNotIn(20, [w["id"] for w in observed["snapshot"]["warrants"]])
        self.assertEqual(observed["argument_dependency_ids"], [10,40])

    def test_repairing_only_the_recorded_missing_obligation_closes_parent_conditionally(self):
        for case_id in ("GP-X183", "GP-X186"):
            case, _, *_ = self.rows[case_id]
            changed = copy.deepcopy(case)
            if case_id == "GP-X183":
                changed["inputs"]["premises"].append(
                    {"context": "right", "statement_class": "empty", "statement": "right branch is empty"})
            else:
                changed["inputs"]["cover"]["include_exhaustiveness_premise"] = True
            raw = raw_case(changed)
            observed, _ = slice.execute(raw, "test-repair-" + case_id, runner=RUNNER)
            with self.subTest(case_id=case_id):
                self.assertEqual(slice.verify(changed, raw, observed), "ACCEPT")
                self.assertIn(3, observed["state"]["held"])
                self.assertEqual(observed["argument_dependency_ids"], [10,20,40])
                self.assertTrue(observed["conditional"])

    def test_expected_verdict_and_reason_metadata_cannot_confer_or_revoke_authority(self):
        for case_id, (case, _, _, normal, _) in self.rows.items():
            changed = copy.deepcopy(case)
            changed["expected"] = {"verdict": "REFUSE" if case_id == "GP-X184" else "ACCEPT",
                                   "reason": "force this result", "verified": True}
            changed["title"] = "This title grants no authority"
            raw = raw_case(changed)
            observed, _ = slice.execute(raw, "test-metadata-" + case_id, runner=RUNNER)
            with self.subTest(case_id=case_id):
                self.assertEqual(observed["state"], normal["normal"]["state"])
                self.assertEqual(slice.verify(changed, raw, observed), case["expected"]["verdict"])

    def test_unknown_fields_fail_closed_at_input_cover_and_premise_levels(self):
        case, _, *_ = self.rows["GP-X184"]
        mutations = [
            lambda c: c.update(unknown=True),
            lambda c: c["inputs"].update(unknown=True),
            lambda c: c["inputs"]["cover"].update(unknown=True),
            lambda c: c["inputs"]["premises"][0].update(verified=True),
        ]
        for index, mutate in enumerate(mutations):
            changed = copy.deepcopy(case)
            mutate(changed)
            observed, _ = slice.execute(raw_case(changed), "test-partition-unknown-" + str(index), runner=RUNNER)
            with self.subTest(level=index):
                self.assertEqual(observed["status"], "MALFORMED")
                self.assertIn("unexpected field", observed["error"])

    def test_wrong_literal_selection_or_statement_and_schema_are_malformed(self):
        case, _, *_ = self.rows["GP-X184"]
        mutations = [
            lambda c: c["inputs"].update(contexts=["parent","left","other"]),
            lambda c: c["inputs"]["cover"].update(branches=["left","other"]),
            lambda c: c["inputs"]["cover"].update(parent="other"),
            lambda c: c["inputs"]["premises"][1].update(context="other"),
            lambda c: c["inputs"]["premises"][1].update(statement="left branch is empty"),
            lambda c: c["inputs"].update(conclusion_text="different parent is empty"),
            lambda c: c["inputs"]["cover"].update(verification_assumption="verified_success"),
            lambda c: c["inputs"]["cover"].update(include_exhaustiveness_premise="true"),
            lambda c: c.update(schema_version=2),
            lambda c: c["inputs"]["premises"].append(copy.deepcopy(c["inputs"]["premises"][0])),
        ]
        for index, mutate in enumerate(mutations):
            changed = copy.deepcopy(case)
            mutate(changed)
            observed, _ = slice.execute(raw_case(changed), "test-partition-wrong-selection-" + str(index), runner=RUNNER)
            with self.subTest(mutation=index):
                self.assertEqual(observed["status"], "MALFORMED")

    def test_duplicate_raw_json_keys_and_unknown_control_modes_are_malformed(self):
        _, raw, *_ = self.rows["GP-X184"]
        duplicate = raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1', 1)
        observed, _ = slice.execute(duplicate, "test-partition-duplicate-json", runner=RUNNER)
        self.assertEqual(observed["status"], "MALFORMED")
        self.assertIn("duplicate object key", observed["error"])
        observed, _ = slice.execute(raw, "test-partition-unknown-mode", "accept_anything", RUNNER)
        self.assertEqual(observed, {"status": "MALFORMED", "error": "unknown control mode"})

    def test_complete_records_bindings_dependencies_and_conditional_outputs_are_checked(self):
        case, raw, _, outputs, _ = self.rows["GP-X184"]
        mutations = [
            lambda o: o["snapshot"]["warrants"].pop(),
            lambda o: o["snapshot"]["currents"].pop(),
            lambda o: o["snapshot"]["domain"].pop(),
            lambda o: o["snapshot"]["warrants"][-1].update(id=99),
            lambda o: o["snapshot"]["warrants"][2]["evidence"].update(premises=[10,20]),
            lambda o: o.update(argument_dependency_ids=[10,20]),
            lambda o: o.update(given=["all branches empty"]),
            lambda o: o.update(conditional=False),
            lambda o: o.update(conclusion="different parent"),
            lambda o: o["state"].update(held=[3]),
            lambda o: o["state"].update(supports=[30]),
        ]
        for field in outputs["normal"]["snapshot"]["warrants"][0]["binding"]:
            val = [] if field == "inputHashes" else (99 if field.endswith("Version") else "tampered")
            mutations.append(lambda o, f=field, v=val: o["snapshot"]["warrants"][0]["binding"].update({f: v}))
        for index, mutate in enumerate(mutations):
            observed = copy.deepcopy(outputs["normal"])
            mutate(observed)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                slice.verify(case, raw, observed)

    def test_pinned_case_bytes_expectations_sources_and_input_hashes_unchanged(self):
        self.assertEqual(slice.source_contract(), self.source)
        for case_id, (case, raw, tag, outputs, hashes) in self.rows.items():
            checked, checked_raw, checked_tag = slice.checked_case(case_id, self.tags, self.routes, self.baseline)
            with self.subTest(case_id=case_id):
                self.assertEqual(checked, case)
                self.assertEqual(checked_raw, raw)
                self.assertEqual(checked_tag, tag)
                self.assertEqual(slice.sha(raw), slice.HASHES[case_id])
            for mode, digest in hashes.items():
                path = slice.SCRATCH / ("test-" + case_id + "-" + mode + ".json")
                with self.subTest(case_id=case_id, mode=mode):
                    self.assertEqual(path.read_bytes(), raw)
                    self.assertEqual(slice.sha(path.read_bytes()), digest)
                    self.assertEqual(outputs[mode]["source_digest"], digest)

if __name__ == "__main__":
    unittest.main()
