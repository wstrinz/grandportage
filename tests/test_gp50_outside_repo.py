"""Release plan C2: `gp` runs a campaign that lives outside the repository.

`tools/gp.py` runs as a subprocess with its working directory in one temporary directory and the
campaign in another, neither inside the repository: init, claim, a held submit, status, frontier,
a refused submit, and `gp --version`. A ledger written before restate, receipt references and
`gp_version` still folds (the C2 compatibility statement in docs/USING-GP.md). The runners are the
repository's own; `gp` builds them if they are missing or stale.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
GP = ROOT / "tools/gp.py"
VERSION = re.search(r'^GP_VERSION = "([^"]+)"', GP.read_text(encoding="utf-8"), re.M).group(1)


class OutsideRepo(unittest.TestCase):
    def setUp(self):
        base = Path(tempfile.mkdtemp(prefix="gp-outside-"))
        self.addCleanup(shutil.rmtree, base, ignore_errors=True)
        self.cwd, self.campaign = base / "cwd", base / "elsewhere" / "campaign"
        self.cwd.mkdir()
        self.campaign.mkdir(parents=True)
        for d in (self.cwd, self.campaign):
            self.assertFalse(d.resolve().is_relative_to(ROOT.resolve()), f"{d} is inside the repository")

    def gp(self, *args, campaign=True):
        argv = [sys.executable, str(GP)] + (["--campaign", str(self.campaign)] if campaign else []) + list(args)
        env = dict(os.environ, PYTHONUNBUFFERED="1", PYTHONIOENCODING="utf-8")
        p = subprocess.run(argv, cwd=self.cwd, env=env, capture_output=True, timeout=1800)
        return p.returncode, p.stdout.decode("utf-8"), p.stderr.decode("utf-8")

    def write(self, name, body, where=None):
        path = (where or self.cwd) / name
        path.write_bytes((json.dumps(body) + "\n").encode("utf-8"))
        return path

    def test_version_needs_no_campaign(self):
        code, out, err = self.gp("--version", campaign=False)
        self.assertEqual(code, 0, err)
        self.assertEqual(out.strip(), f"gp {VERSION}")

    def test_campaign_loop(self):
        # Commands before init refuse with exit 2 and say what to do.
        code, out, err = self.gp("status")
        self.assertEqual(code, 2)
        self.assertIn("run `gp init`", err)
        self.write("campaign.json", {"name": "outside", "family": []}, where=self.campaign)
        code, out, err = self.gp("init")
        self.assertEqual(code, 0, err)
        self.assertIn("ledger started for", out)
        init = json.loads((self.campaign / "ledger.jsonl").read_text(encoding="utf-8").splitlines()[0])
        self.assertEqual((init["op"], init["schema"], init["gp_version"]), ("init", "gp-ledger/v1", VERSION))

        # x = 1 and x = -1 have no common point over Q; the certificate divides by 2, so its reach
        # stops short of characteristic 2, where the two equations coincide.
        system = self.write("two-points.json", {"variables": ["x"], "equations": ["x - 1", "x + 1"], "nonzero": []})
        receipt = self.write("empty-q.json", {"certificate": {"type": "ideal", "cofactors": ["-1/2", "1/2"],
                                                              "m": 0, "k": 0}})
        code, out, err = self.gp("claim", "distinct-q", "--system", "two-points.json", "--kind", "EMPTY", "--char0")
        self.assertEqual(code, 0, err)
        self.assertIn("filed: EMPTY at characteristic 0; open", out)
        code, out, err = self.gp("submit", "distinct-q", "empty-q.json")
        self.assertEqual(code, 0, err)
        self.assertEqual(out.strip(), "held: distinct-q at characteristic 0; "
                                      "earned, unclaimed: 0 and every prime except {2}")
        # The receipt is filed by reference, inside the campaign.
        self.assertEqual(len(list((self.campaign / "receipts").glob("*.json"))), 1)

        code, out, err = self.gp("claim", "distinct-all", "--system", str(system), "--kind", "EMPTY", "--outside", "")
        self.assertEqual(code, 0, err)
        code, out, err = self.gp("submit", "distinct-all", str(receipt))
        self.assertEqual(code, 1, out)
        self.assertTrue(err.startswith("refused: "), err)
        self.assertIn("smallest fix:", err)

        code, out, err = self.gp("status")
        self.assertEqual(code, 0, err)
        rows = {line.split()[1]: line.split()[0] for line in out.splitlines() if line.strip()}
        self.assertEqual(rows, {"distinct-q": "held", "distinct-all": "refused"}, out)
        self.assertIn("earned, unclaimed: 0 and every prime except {2}", out)

        code, out, err = self.gp("frontier")
        self.assertEqual(code, 0, err)
        self.assertTrue(out.startswith("distinct-all: refused: "), out)
        self.assertNotIn("frontier empty", out)
        self.assertNotIn("distinct-q", out)

    def test_old_ledger_keeps_folding(self):
        # The C2 compatibility statement: an init record without gp_version, a counter-scheme claim key,
        # a support with its receipt inline, and no restate record. The init hash binds the statement.
        statement = self.write("campaign.json", {"name": "old", "family": []}, where=self.campaign)
        bound = hashlib.sha256(statement.read_bytes()).hexdigest()
        system = {"variables": ["x"], "equations": ["x - 1", "x + 1"], "nonzero": []}
        receipt = {"certificate": {"type": "ideal", "cofactors": ["-1/2", "1/2"], "m": 0, "k": 0}}
        records = [
            {"op": "init", "schema": "gp-ledger/v1", "statement_sha256": bound},
            {"op": "claim", "key": 1, "label": "old-empty", "matroid": None, "system": system, "kind": "EMPTY",
             "target": None, "scope": {"char0": True}, "named_premises": [],
             "inputs": ["system:" + hashlib.sha256(json.dumps(system, sort_keys=True).encode()).hexdigest()]},
            {"op": "support", "label": "old-empty", "key": 1, "receipt": receipt, "reach": None,
             "receipt_sha256": hashlib.sha256(json.dumps(receipt).encode()).hexdigest()}]
        (self.campaign / "ledger.jsonl").write_bytes("".join(
            json.dumps(dict(r, at="2026-10-01T00:00:00Z"), sort_keys=True) + "\n" for r in records).encode("utf-8"))
        code, out, err = self.gp("status")
        self.assertEqual(code, 0, err)
        self.assertTrue(out.startswith("held     old-empty"), out)
        code, out, err = self.gp("frontier")
        self.assertEqual((code, out.strip()), (0, "frontier empty: every claim is held"), err)
        self.write("campaign.json", {"name": "old, edited", "family": []}, where=self.campaign)
        code, out, err = self.gp("status")
        self.assertEqual(code, 1)
        self.assertIn("the campaign statement changed since it was bound", err)
        code, out, err = self.gp("restate", "--reason", "edited")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.gp("status")[0], 0)


if __name__ == "__main__":
    unittest.main()
