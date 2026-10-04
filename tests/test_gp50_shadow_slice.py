"""§3.6a shadow slice: Lean files match their generator; the receipt is internally consistent."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SHADOW = ROOT / "binding/GPBinding/Shadow"
RECEIPT = ROOT / "reports/PHASE-3A-SHADOW.json"
STANDARD = {"propext", "Quot.sound", "Classical.choice"}


class ShadowSliceTests(unittest.TestCase):
    def test_generated_files_are_current(self):
        with tempfile.TemporaryDirectory() as out:
            subprocess.run([sys.executable, str(ROOT / "tools/gen-shadow-claims.py"), "--out", out],
                           check=True, capture_output=True)
            for path in sorted(Path(out).glob("*.lean")):
                with self.subTest(file=path.name):
                    self.assertEqual(path.read_text(encoding="utf-8"),
                                     (SHADOW / path.name).read_text(encoding="utf-8"))

    def test_receipt(self):
        receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
        for name, axioms in receipt["axioms"].items():
            with self.subTest(theorem=name):
                self.assertLessEqual(set(axioms), STANDARD)
        for claim, timing in receipt["timing_seconds"].items():
            if isinstance(timing, dict) and "total_s" in timing:
                self.assertLess(timing["total_s"], receipt["a4_budget_seconds"], claim)
        conv = receipt["convergence"]
        self.assertEqual(sorted(conv["tags"]), sorted(conv["held"]))


if __name__ == "__main__":
    unittest.main()
