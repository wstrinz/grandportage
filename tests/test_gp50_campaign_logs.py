"""Post-G3a §3: the cost and friction log schemas accept well-formed entries and refuse the rest."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("campaign_logs", ROOT / "tools/check-campaign-logs.py")
logs = importlib.util.module_from_spec(spec)
spec.loader.exec_module(logs)

COST = {"task": "F0-fano", "stage": "F0", "started": "2026-10-04T10:00:00Z", "ended": "2026-10-04T10:20:00Z",
        "wall_seconds": 1200, "agent_turns": 14, "tokens": None, "catches": [], "false_refusals": 0,
        "near_misses": []}
FRICTION = {"at": "2026-10-04T10:05:00Z", "task": "F0-fano", "command": "gp submit receipts/fano-c1.json",
            "claim": "fano-empty-char2", "refusal": {"message": "reach excludes 2", "rule": "C1 reach",
                                                     "scope": "char 2"},
            "class": "useful", "rationale": "the certificate divides by 2"}


def run(cost, friction):
    with tempfile.TemporaryDirectory() as d:
        Path(d, "cost-log.jsonl").write_text("".join(json.dumps(e) + "\n" for e in cost), encoding="utf-8")
        Path(d, "friction-log.jsonl").write_text("".join(json.dumps(e) + "\n" for e in friction), encoding="utf-8")
        return logs.check(d)


class CampaignLogTests(unittest.TestCase):
    def test_well_formed_logs_pass(self):
        self.assertEqual(run([COST], [FRICTION]), [])

    def test_unclassified_refusal_is_refused(self):
        bad = dict(FRICTION, **{"class": "annoying"})
        self.assertTrue(run([COST], [bad]))

    def test_friction_needs_a_cost_task(self):
        self.assertTrue(run([COST], [dict(FRICTION, task="F1-unknown")]))

    def test_unknown_fields_are_refused(self):
        self.assertTrue(run([dict(COST, mood="good")], []))


if __name__ == "__main__":
    unittest.main()
