"""post-G2 §1.11: every profile-layer case has exactly one gate owner (or is pending review)."""
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
OWNERS = {"3a", "3b", "census", "campaign-op", "admission-control"}


class GateOwnerTests(unittest.TestCase):
    def test_owners_cover_profile_layer_exactly(self):
        tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_text(encoding="utf-8"))["cases"]
        profile = sorted(r["id"] for r in tags if r["primary_layer"] == "profile")
        owners = json.loads((ROOT / "corpus/GATE-OWNERS.json").read_text(encoding="utf-8"))
        ids = [c["id"] for c in owners["cases"]]
        self.assertEqual(sorted(ids), profile)
        self.assertEqual(len(ids), len(set(ids)))
        for case in owners["cases"]:
            with self.subTest(case=case["id"]):
                if case["owner"] == "ambiguous":
                    self.assertIn(case["proposed_owner"], OWNERS)
                else:
                    self.assertIn(case["owner"], OWNERS)


if __name__ == "__main__":
    unittest.main()
