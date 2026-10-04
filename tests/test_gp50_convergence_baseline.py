"""A5 convergence baseline: every held claim in the committed slice carries exactly one tag."""
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
TAGS = {"REACH", "CUSTODY", "COVERAGE", "EARNED", "NONE"}


class ConvergenceBaselineTests(unittest.TestCase):
    def test_baseline_tags_every_held_claim(self):
        baseline = json.loads((ROOT / "reports/PHASE-2.5-CONVERGENCE.json").read_text(encoding="utf-8"))
        slice_ = json.loads((ROOT / baseline["source"]).read_text(encoding="utf-8"))
        held = sorted(c["id"] for c in slice_["cases"] if c["observed"] == "ACCEPT")
        self.assertEqual([c["id"] for c in baseline["claims"]], held)
        self.assertTrue(all(c["tag"] in TAGS for c in baseline["claims"]))
        counts = {t: sum(1 for c in baseline["claims"] if c["tag"] == t) for t in TAGS}
        self.assertEqual(counts, baseline["tag_counts"])
        self.assertEqual(baseline["held_claims"], len(held))


if __name__ == "__main__":
    unittest.main()
