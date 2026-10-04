"""Post-G3a handoff §3: STATUS.md names the latest gate ratified in DECISIONS.md."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


class StatusTests(unittest.TestCase):
    def test_status_names_latest_ratified_gate(self):
        decisions = (ROOT / "DECISIONS.md").read_text(encoding="utf-8")
        gates = re.findall(r"\b(G[0-9][0-9A-Za-z.]*?) ratified\b", decisions)
        self.assertTrue(gates)
        latest = gates[-1]
        status = (ROOT / "STATUS.md").read_text(encoding="utf-8")
        self.assertIn(f"{latest} ratified", status)


if __name__ == "__main__":
    unittest.main()
