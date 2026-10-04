"""Layer metadata contract tests using byte copies of existing cases only."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / "tools" / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
gen = load("layer_generator_test", "tag-corpus-layers.py")
check = load("layer_validator_test", "check-layer-tags.py")

class LayerTagsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=ROOT / "tests", prefix="layer-tags-")
        self.addCleanup(self.temp.cleanup)
        self.cases = Path(self.temp.name)
        for name in ("GP-A17.json", "GP-C04.json"):
            (self.cases / name).write_bytes((ROOT / "corpus/must" / name).read_bytes())
        self.before = {p.name: p.read_bytes() for p in self.cases.glob("*.json")}
        self.tags = gen.generate(self.cases, expected_count=2)

    def assertInvalid(self, data):
        with self.assertRaises(ValueError):
            check.validate(data, self.cases, expected_count=2)

    def test_generation_and_validation_preserve_case_bytes(self):
        check.validate(self.tags, self.cases, expected_count=2)
        self.assertEqual(self.before, {p.name: p.read_bytes() for p in self.cases.glob("*.json")})

    def test_duplicate_missing_extra_and_wrong_count_rejected(self):
        for mutation in ("duplicate", "missing", "extra", "count"):
            with self.subTest(mutation=mutation):
                bad = copy.deepcopy(self.tags)
                if mutation == "duplicate": bad["cases"].append(copy.deepcopy(bad["cases"][0]))
                elif mutation == "missing": bad["cases"].pop()
                elif mutation == "extra": bad["cases"][0]["id"] = "NOT-A-CASE"
                else: bad["case_count"] += 1
                self.assertInvalid(bad)

    def test_stale_hash_and_changed_expectation_rejected(self):
        bad = copy.deepcopy(self.tags)
        bad["cases"][0]["sha256"] = "0" * 64
        self.assertInvalid(bad)
        target = self.cases / "GP-A17.json"
        changed = json.loads(target.read_text(encoding="utf-8"))
        changed["expected"]["verdict"] = "ACCEPT"
        target.write_text(json.dumps(changed), encoding="utf-8")
        self.assertInvalid(self.tags)

    def test_layer_enum_path_status_and_pointer_rejected(self):
        for field, value in (("primary_layer", "oracle"), ("path", "../outside.json"),
                             ("status", "unresolved"), ("evidence_pointers", ["/missing"]),
                             ("rationale", ""), ("candidate_layers", ["kernel", "kernel"]),
                             ("g2_kernel_eligible", 1)):
            with self.subTest(field=field):
                bad = copy.deepcopy(self.tags)
                bad["cases"][0][field] = value
                self.assertInvalid(bad)

    def test_pending_kernel_cannot_be_silently_excluded(self):
        bad = copy.deepcopy(self.tags)
        pending = gen.decision(None, "Needs full-contract review.", ["kernel", "profile"])
        bad["cases"][0].update(pending)
        with patch.dict(check._generator.CATALOG, {"GP-A17": pending}):
            summary = check.validate(bad, self.cases, expected_count=2)
            self.assertEqual(summary["g2_pending"], ["GP-A17"])
            with self.assertRaises(ValueError):
                check.kernel_case_ids(bad, self.cases, expected_count=2)
            bad["cases"][0]["g2_kernel_eligible"] = False
            self.assertInvalid(bad)

    def test_unknown_future_case_remains_unresolved_not_excluded(self):
        source = json.loads((self.cases / "GP-A17.json").read_text(encoding="utf-8"))
        source["id"] = "GP-X999"
        (self.cases / "GP-A17.json").unlink()
        (self.cases / "GP-X999.json").write_text(json.dumps(source), encoding="utf-8")
        generated = gen.generate(self.cases, expected_count=2)
        row = next(r for r in generated["cases"] if r["id"] == "GP-X999")
        self.assertIsNone(row["primary_layer"])
        self.assertIsNone(row["g2_kernel_eligible"])
        check.validate(generated, self.cases, expected_count=2)
        with self.assertRaises(ValueError):
            check.kernel_case_ids(generated, self.cases, expected_count=2)
        self.assertIsNone(gen.CATALOG.get("GP-FUTURE"))
        proposal = gen.decision(None, "Needs review.")
        self.assertIsNone(proposal["g2_kernel_eligible"])
        self.assertIn("kernel", proposal["candidate_layers"])

    def test_contract_layers_ignore_old_routing_labels(self):
        case = json.loads((self.cases / "GP-A17.json").read_text(encoding="utf-8"))
        case["oracle_adapter"] = "algebra"
        (self.cases / "GP-A17.json").write_text(json.dumps(case), encoding="utf-8")
        tags = gen.generate(self.cases, expected_count=2)
        self.assertEqual(next(r for r in tags["cases"] if r["id"] == "GP-A17")["primary_layer"], "kernel")
        self.assertEqual(gen.CATALOG["GP-X206"]["primary_layer"], "adapter")
        self.assertEqual(gen.CATALOG["GP-A03a"]["primary_layer"], "profile")
        self.assertEqual(gen.CATALOG["GP-X171"]["primary_layer"], "kernel")

    def test_missing_fields_and_boolean_schema_rejected(self):
        for field in self.tags["cases"][0]:
            with self.subTest(field=field):
                bad = copy.deepcopy(self.tags)
                del bad["cases"][0][field]
                self.assertInvalid(bad)
        bad = copy.deepcopy(self.tags)
        bad["schema_version"] = True
        self.assertInvalid(bad)

    def test_source_duplicate_or_filename_mismatch_rejected(self):
        target = self.cases / "GP-C04.json"
        case = json.loads(target.read_text(encoding="utf-8"))
        case["id"] = "GP-A17"
        target.write_text(json.dumps(case), encoding="utf-8")
        with self.assertRaises(ValueError):
            gen.generate(self.cases)

    def test_real_registry_accounts_for_all_462_without_mutation(self):
        actual_dir = ROOT / "corpus/must"
        before = {p.name: p.read_bytes() for p in actual_dir.glob("*.json")}
        generated = gen.generate(actual_dir, expected_count=462)
        saved = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_text(encoding="utf-8"))
        self.assertEqual(generated, saved)
        self.assertEqual(check.validate(saved, actual_dir)["case_count"], 462)
        self.assertEqual(before, {p.name: p.read_bytes() for p in actual_dir.glob("*.json")})


    def test_parent_full_contract_decisions(self):
        expected = {"GP-X211": "host", "GP-X230": "host", "GP-X302": "adapter",
                    "GP-X370": "adapter", "GP-X388": "surface",
                    "GP-A27-partial": "kernel", "GP-X09": "kernel",
                    "GP-A01": "kernel", "GP-A08a": "kernel",
                    "GP-X02": "profile", "GP-X45": "profile",
                    "GP-X134": "profile", "GP-X308": "profile"}
        for ident, layer in expected.items():
            with self.subTest(ident=ident):
                row = gen.CATALOG[ident]
                self.assertEqual(row["primary_layer"], layer)
                self.assertEqual(row["g2_kernel_eligible"], layer == "kernel")
                self.assertIs(row["full_contract_required"], True)

    def test_secondary_kernel_and_projection_cannot_count_as_g2(self):
        for ident in ("GP-X02", "GP-X211", "GP-X302", "GP-X370", "GP-X388"):
            row = {"id": ident, **gen.CATALOG[ident]}
            self.assertIn("kernel", row["secondary_layers"])
            self.assertFalse(check.g2_result_eligible(row, full_fixture_passed=True))
        forged = {"id": "GP-X211", **gen.CATALOG["GP-X211"]}
        forged.update(primary_layer="kernel", g2_kernel_eligible=True)
        self.assertFalse(check.g2_result_eligible(forged, full_fixture_passed=True))
        row = {"id": "GP-A27-partial", **gen.CATALOG["GP-A27-partial"]}
        self.assertFalse(check.g2_result_eligible(row, full_fixture_passed=False))
        self.assertFalse(check.g2_result_eligible(row, full_fixture_passed=True, projection_only=True))
        self.assertTrue(check.g2_result_eligible(row, full_fixture_passed=True))
        with self.assertRaises(ValueError):
            check.g2_result_eligible(row, full_fixture_passed=1)

    def test_secondary_contract_and_reviewed_policy_mutations_rejected(self):
        for field, value in (("secondary_layers", ["kernel"]), ("secondary_layers", ["oracle"]),
                             ("secondary_duties", [{"layer": "host", "duty": ""}]),
                             ("full_contract_required", False), ("review_group", ""),
                             ("rationale", "Custody projection is enough.")):
            with self.subTest(field=field, value=value):
                bad = copy.deepcopy(self.tags)
                bad["cases"][0][field] = value
                self.assertInvalid(bad)
        bad = copy.deepcopy(self.tags)
        row = bad["cases"][1]  # C04 is a complete parser/program-construction fixture.
        row.update(primary_layer="kernel", candidate_layers=["kernel"],
                   g2_kernel_eligible=True, secondary_layers=[], secondary_duties=[])
        self.assertInvalid(bad)

    def test_missing_reviewed_id_has_no_numeric_default(self):
        original = gen.CATALOG.pop("GP-X412")
        try:
            generated = gen.generate(ROOT / "corpus/must", expected_count=462)
            row = next(r for r in generated["cases"] if r["id"] == "GP-X412")
            self.assertIsNone(row["primary_layer"])
            self.assertIsNone(row["g2_kernel_eligible"])
            self.assertEqual(row["review_group"], "unreviewed")
        finally:
            gen.CATALOG["GP-X412"] = original


    def test_finite_recorded_use_coverage_is_kernel_despite_domain_labels(self):
        expected_gaps = {
            "GP-X193": {"place": {"t"}, "order": {"-4", "0", "1", "2"}},
            "GP-X194": {"place": set(), "order": {"-4", "0", "1", "2"}},
            "GP-X195": {"place": {"t"}, "order": set()},
            "GP-X196": {"place": set(), "order": set()},
            "GP-X197": {"place": set(), "order": set()},
            "GP-X198": {"place": set(), "order": {"0"}},
        }
        for ident, gaps in expected_gaps.items():
            case = json.loads((ROOT / "corpus/must" / (ident + ".json")).read_text(encoding="utf-8-sig"))
            inputs = case["inputs"]
            self.assertEqual(inputs["asserted_dimensions"], ["place", "order"])
            recorded = inputs["construction_uses"] + inputs["conclusion_uses"]
            actual = {dimension: {index for use in recorded if use["dimension"] == dimension
                                  for index in use["indices"]} - set(inputs["represented_indices"][dimension])
                      for dimension in inputs["asserted_dimensions"]}
            self.assertEqual(actual, gaps)
            self.assertEqual(case["expected"]["verdict"], "REFUSE" if any(gaps.values()) else "ACCEPT")
            # Labels resembling mathematical profile work cannot override supplied finite obligations.
            case["title"] = "Algebraic place and coefficient-order mathematical profile"
            case["oracle_adapter"] = "algebra"
            for use in recorded:
                use["description"] = "mathematical coefficient-domain profile inventory"
            (self.cases / (ident + ".json")).write_text(json.dumps(case), encoding="utf-8")
        generated = gen.generate(self.cases, expected_count=8)
        for row in generated["cases"]:
            if row["id"] in expected_gaps:
                self.assertEqual(row["primary_layer"], "kernel")
                self.assertEqual(row["review_group"], "finite-recorded-use-coverage")
                self.assertTrue(check.g2_result_eligible(row, full_fixture_passed=True))
                self.assertFalse(check.g2_result_eligible(row, full_fixture_passed=True, projection_only=True))
        check.validate(generated, self.cases, expected_count=8)

    def test_stored_proof_mutation_is_kernel_with_replacement_profile_duty(self):
        case = json.loads((ROOT / "corpus/must/GP-X175.json").read_text(encoding="utf-8-sig"))
        self.assertEqual(case["inputs"], {"sequence": ["success"], "mutation": "proof"})
        self.assertIn("test_mutating_stored_section_certificate_makes_verdict_stale",
                      case["sources"][0]["anchor"])
        row = {"id": "GP-X175", **gen.CATALOG["GP-X175"]}
        self.assertEqual(row["primary_layer"], "kernel")
        self.assertEqual(row["review_group"], "stored-certificate-binding")
        self.assertEqual(row["secondary_layers"], ["profile"])
        self.assertIn("replacement section certificate", row["secondary_duties"][0]["duty"])
        self.assertTrue(check.g2_result_eligible(row, full_fixture_passed=True))
        self.assertFalse(check.g2_result_eligible(row, full_fixture_passed=False))

if __name__ == "__main__":
    unittest.main()
