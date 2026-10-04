"""Finite native adversarial controls for X164 checked lifecycle supplements."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("checked_supplement",
    ROOT / "tools/run-phase2-checked-lifecycle-supplement.py")
supp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(supp)

class CheckedLifecycleSupplementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.case, cls.raw, cls.registry, cls.events, _ = supp.prepared()
        cls.rows = {r["label"]: r for r in supp.scenarios(cls.registry, cls.events)}
        cls.report = supp.run(supp.SCRATCH / "tests.report.json")
        cls.results = {r["label"]: r for r in cls.report["scenarios"]}

    def observed(self, label):
        return self.results[label]["runs"]["forward"]["native_result"]

    def run_control(self, row, label):
        return supp.execute(row, "test-control-" + label, row["wire"])["native_result"]

    def test_every_scenario_native_orders_duplicates_and_complete_custody(self):
        for label, result in self.results.items():
            row = self.rows[label]
            for order, run in result["runs"].items():
                with self.subTest(scenario=label, order=order):
                    supp.verify(row, row["wire"], run["native_result"], run["native_custody_result"])
                    self.assertEqual(run["native_result"], result["runs"]["forward"]["native_result"])
                    self.assertEqual(run["native_custody_result"], result["runs"]["forward"]["native_custody_result"])

    def test_selected_statement_model_inputs_version_bindings_are_unchanged(self):
        binding = self.registry["clauses"][0]["binding"]
        self.assertEqual(self.registry["clauses"][0]["generators"], [supp.helper.POLYNOMIALS["x"]])
        self.assertEqual(self.registry["clauses"][0]["target"], supp.helper.POLYNOMIALS["x"])
        self.assertEqual(binding["statementHash"], supp.helper.digest(
            {"id":"C","model":"M","lhs":"x","rhs":"0","kind":"identity","identity_origin":"derived"}))
        self.assertEqual(binding["modelHash"], supp.helper.digest(
            {"id":"M","ring_vars":["x"],"characteristic":0,"generators":[supp.helper.POLYNOMIALS["x"]]}))
        for row in self.rows.values():
            clause = row["registry"]["clauses"][0]
            clause = clause["algebra"] if row["kind"] == "scoped" else clause
            self.assertEqual(clause, self.registry["clauses"][0])
            for event in row["wire"]["events"]:
                if "value" in event:
                    self.assertEqual(event["value"]["binding"], binding)
                    self.assertEqual(event["value"]["version"], 1)

    def test_both_receipts_are_checked_separate_names_and_warrant_ids(self):
        row = self.rows["two_independent_receipts"]
        self.assertEqual([r["name"] for r in row["registry"]["receipts"]], ["receipt-1","receipt-2"])
        self.assertTrue(all(r["cofactors"] == [supp.helper.ONE] for r in row["registry"]["receipts"]))
        self.assertEqual(self.observed("two_independent_receipts")["supports"], [10,11])
        for index, support in ((0,10),(1,11)):
            single = copy.deepcopy(row)
            single["registry"]["receipts"] = [single["registry"]["receipts"][index]]
            single["wire"]["events"] = [single["wire"]["events"][0], single["wire"]["events"][index+1]]
            single["supports"] = [support]
            with self.subTest(receipt=index):
                result = self.run_control(single, "independent-" + str(index))
                self.assertEqual(result["held"], [1])
                self.assertEqual(result["supports"], [support])

    def test_retract_one_keeps_claim_and_independent_support_retract_both_refuses(self):
        self.assertEqual(self.observed("retract_first_support")["supports"], [11])
        self.assertEqual(self.observed("retract_first_support")["held"], [1])
        self.assertEqual(self.observed("retract_first_support")["retracted"], [10])
        self.assertEqual(self.observed("retract_both_supports")["supports"], [])
        self.assertEqual(self.observed("retract_both_supports")["held"], [])
        for label in ("retract_first_support","retract_both_supports"):
            snapshot = self.results[label]["runs"]["forward"]["native_custody_result"]["snapshot"]
            self.assertEqual([w["id"] for w in snapshot["warrants"]], [10,11])

    def test_targeting_neighbor_in_native_retracts_only_neighbor(self):
        row = copy.deepcopy(self.rows["retract_first_support"])
        row["wire"]["events"][-1]["target"] = 11
        row["supports"] = [10]
        result = self.run_control(row, "wrong-neighbor-target")
        self.assertEqual(result["supports"], [10])
        self.assertEqual(result["retracted"], [11])
        self.assertEqual(result["held"], [1])

    def test_invalid_cofactor_refuses_each_receipt_without_affecting_neighbor(self):
        for label, support in (("invalid_cofactor_receipt_1",11),("invalid_cofactor_receipt_2",10)):
            self.assertEqual(self.observed(label)["supports"], [support])
            self.assertEqual(self.observed(label)["held"], [1])

    def test_receipt_binding_mismatch_in_each_field_and_version_is_native_refusal(self):
        original = self.rows["two_independent_receipts"]
        binding = original["registry"]["receipts"][0]["binding"]
        for field in binding:
            row = copy.deepcopy(original)
            old = row["registry"]["receipts"][0]["binding"][field]
            row["registry"]["receipts"][0]["binding"][field] = (
                old + 1 if type(old) is int else old + ["wrong"] if isinstance(old,list) else old + "-wrong")
            row["supports"] = [11]
            with self.subTest(field=field):
                self.assertEqual(self.run_control(row, "binding-" + field)["supports"], [11])
        row = copy.deepcopy(original)
        row["registry"]["receipts"][0]["version"] = 2
        row["supports"] = [11]
        self.assertEqual(self.run_control(row, "receipt-version")["supports"], [11])

    def test_receipt_name_is_registered_identity_not_verified_label(self):
        row = copy.deepcopy(self.rows["two_independent_receipts"])
        row["wire"]["events"][1]["value"]["evidence"]["data"] = "VERIFIED"
        row["supports"] = [11]
        self.assertEqual(self.run_control(row, "unknown-receipt-name")["supports"], [11])

    def test_failed_and_timeout_retry_preserve_checked_success_in_all_orders(self):
        for status, attempt_id in (("failed",20),("timeout",21)):
            result = self.observed("success_then_" + status)
            self.assertEqual(result["supports"], [10])
            self.assertEqual(result["held"], [1])
            self.assertEqual(result["live_warrants"], [10,attempt_id])
            self.assertEqual(self.observed(status + "_only")["supports"], [])
            self.assertEqual(self.observed(status + "_only")["held"], [])
            self.assertEqual(self.observed(status + "_only")["live_warrants"], [attempt_id])

    def test_earned_reports_unclaimed_held_identity_with_only_open_linked_obligations(self):
        result = self.observed("earned_unclaimed")
        self.assertEqual(result["earned"], [{"claim":1,"open_obligations":[7]}])
        self.assertEqual(result["state"]["held"], [1])
        self.assertEqual(result["why_not"][1], {"claim":2,"held":False,"warrants":[]})

    def test_claiming_identity_removes_earned_without_changing_native_held(self):
        self.assertEqual(self.observed("earned_claimed")["earned"], [])
        self.assertEqual(self.observed("earned_claimed")["state"],
                         self.observed("earned_unclaimed")["state"])

    def test_bogus_claim_and_open_metadata_cannot_create_unsupported_claim(self):
        result = self.observed("earned_metadata_only")
        self.assertEqual(result["earned"], [{"claim":1,"open_obligations":[8]}])
        self.assertEqual(result["state"], self.observed("earned_unclaimed")["state"])
        self.assertEqual(self.observed("earned_unsupported_control")["earned"], [])
        self.assertEqual(self.observed("earned_unsupported_control")["state"]["held"], [])

    def test_duplicate_caller_metadata_is_canonical_and_cannot_admit_truth(self):
        row = copy.deepcopy(self.rows["earned_unclaimed"])
        row["request"]["links"].append({"claim":1,"obligations":[7,7,999]})
        row["request"]["open_obligations"] = [7,7,9]
        result = self.run_control(row, "duplicate-query-metadata")
        self.assertEqual(result["earned"], [{"claim":1,"open_obligations":[7]}])
        self.assertEqual(result["state"], self.observed("earned_unclaimed")["state"])

    def test_unknown_native_registry_event_query_fields_fail_closed(self):
        row = self.rows["earned_unclaimed"]
        for location in ("registry","event","query"):
            registry, wire, request = copy.deepcopy(row["registry"]), copy.deepcopy(row["wire"]), copy.deepcopy(row["request"])
            (registry if location == "registry" else wire["events"][0] if location == "event" else request)["verified"] = True
            paths = [supp.write_input("unknown-" + location,"registry",registry),
                     supp.write_input("unknown-" + location,"events",wire),
                     supp.write_input("unknown-" + location,"queries",request)]
            with self.subTest(location=location):
                self.assertEqual(supp.native(supp.RUNNERS["scoped"],paths),
                                 {"status":"MALFORMED","error":"unexpected field: verified"})

    def test_native_conflicting_warrant_id_does_not_merge_independent_receipts(self):
        row = copy.deepcopy(self.rows["two_independent_receipts"])
        row["wire"]["events"][2]["value"]["id"] = 10
        paths = [supp.write_input("conflicting-id","registry",row["registry"]),
                 supp.write_input("conflicting-id","events",row["wire"])]
        self.assertEqual(supp.native(supp.RUNNERS["span"], paths),
                         {"status":"MALFORMED","error":"conflicting warrant contents: 10"})

    def test_complete_verification_rejects_binding_snapshot_support_or_earned_damage(self):
        row = self.rows["earned_unclaimed"]
        run = self.results["earned_unclaimed"]["runs"]["forward"]
        bad = copy.deepcopy(run["native_custody_result"])
        bad["snapshot"]["warrants"][0]["binding"]["inputHashes"] = []
        with self.assertRaisesRegex(ValueError,"custody"):
            supp.verify(row,row["wire"],run["native_result"],bad)
        for path in (("state","supports"),("state","held"),("state","live_warrants"),("earned",)):
            bad = copy.deepcopy(run["native_result"])
            node = bad
            for key in path[:-1]:
                node = node[key]
            node[path[-1]] = [999]
            with self.subTest(path=path), self.assertRaises(ValueError):
                supp.verify(row,row["wire"],bad,run["native_custody_result"])

    def test_report_hashes_boundaries_and_no_new_corpus_passes(self):
        report = self.report
        self.assertEqual(report["distinct_corpus_passes_added"],0)
        self.assertEqual(report["component_passes_added"],0)
        self.assertEqual(report["new_corpus_cases"],0)
        self.assertFalse(report["g2_pass"])
        self.assertEqual(report["supplemental_scenario_count"],13)
        self.assertEqual(report["supplemental_checked_folds"],52)
        self.assertEqual(report["supplemental_custody_folds"],52)
        self.assertIn("reproduction plumbing",report["scope_boundary"])
        self.assertIn("custody comparison only",report["snapshot_boundary"])
        self.assertEqual(report["source_fixture"]["sha256"],supp.CASE_HASH)
        self.assertEqual(report["adapter_sha256"],supp.sha(Path(supp.__file__).read_bytes()))
        for kind, executable in supp.RUNNERS.items():
            self.assertEqual(report["executables"][kind]["sha256"],supp.sha(executable.read_bytes()))
        for result in report["scenarios"]:
            for order, run in result["runs"].items():
                for suffix, expected in run["inputs"].items():
                    path = supp.SCRATCH / (result["label"] + "-" + order + "." + suffix.removesuffix("_sha256") + ".json")
                    self.assertEqual(supp.sha(path.read_bytes()),expected)

    def test_original_fixture_bytes_and_expectation_unchanged(self):
        self.assertEqual((ROOT / "corpus/must/GP-X164.json").read_bytes(),self.raw)
        self.assertEqual(supp.sha(self.raw),supp.CASE_HASH)
        self.assertEqual(self.report["source_fixture"]["expected"],self.case["expected"])
        self.assertEqual(supp.source_contract(),self.report["source_contract"])

if __name__ == "__main__":
    unittest.main()
