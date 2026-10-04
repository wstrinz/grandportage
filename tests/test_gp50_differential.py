"""post-G2 §3.8: every oracle inference in the JC(2) and matroid fixtures is triaged, none disagrees."""
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class DifferentialTests(unittest.TestCase):
    def test_every_inference_triaged_without_disagreement(self):
        report = json.loads((ROOT / "reports/PHASE-3A-DIFFERENTIAL.json").read_text(encoding="utf-8"))
        triaged = {r["id"]: r for r in report["inferences"]}
        for d in ("matroid", "jc2"):
            base = ROOT / "oracle/checkout/fixtures" / d
            if not base.exists():
                self.skipTest("oracle checkout not present")
            expect = json.loads((base / "expect.json").read_text(encoding="utf-8"))
            for line in (base / "graph.jsonl").read_text(encoding="utf-8").splitlines():
                if not line.strip() or line.startswith("#"):
                    continue
                row = json.loads(line)
                if row.get("ev") != "inference":
                    continue
                with self.subTest(inference=row["id"]):
                    oracle = "clean" if row["id"] in expect["clean_inferences"] else "finding"
                    self.assertEqual(triaged[row["id"]]["oracle"], oracle)
                    self.assertNotEqual(triaged[row["id"]]["triage"], "disagrees")


if __name__ == "__main__":
    unittest.main()
