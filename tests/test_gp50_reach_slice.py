"""Post-G2 §3.6 receipt reach slice: the Lean runner reproduces the committed aggregate receipt."""
import json
import os
from pathlib import Path
import subprocess
import unittest

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / "profile"
RECEIPT = ROOT / "reports/PHASE-3A-SLICE.json"
TOOLCHAIN = ELAN_HOME / "toolchains" / (PROFILE / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")


def strip(receipt):
    for case in receipt["cases"]:
        case.pop("elapsed_ms", None)
    return receipt


def run_slice():
    env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"])
    subprocess.run([str(TOOLCHAIN / ("bin/lake" + EXE_SUFFIX)), "build", "gp_reach_slice"], cwd=PROFILE,
                   env=env, check=True, capture_output=True)
    out = subprocess.run([str(PROFILE / (".lake/build/bin/gp_reach_slice" + EXE_SUFFIX)), str(ROOT),
                          str(PROFILE / "slice/manifest.json")], check=True, capture_output=True, text=True)
    return json.loads(out.stdout)


class ReachSliceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fresh = strip(run_slice())
        cls.cases = {c["id"]: c for c in cls.fresh["cases"]}

    def test_matches_committed_receipt(self):
        self.assertEqual(self.fresh, strip(json.loads(RECEIPT.read_text(encoding="utf-8"))))

    def test_every_case_agrees(self):
        for case in self.fresh["cases"]:
            with self.subTest(case=case["id"]):
                self.assertEqual(case["observed"], case["expected"])

    def test_reach_demonstrations(self):
        c = self.cases
        self.assertEqual(c["GP-A08b"]["widened"]["scope"], {"char0": True, "all_primes_except": []})
        self.assertEqual(c["GP-A08b"]["earned"], [2])
        self.assertEqual(c["GP-A08c"]["widened"]["scope"]["all_primes_except"], [2])
        self.assertEqual(c["GP-A05"]["check"]["result"], "ILL_FORMED")
        for refused in ("GP-A04[p=3]", "GP-A04[p=5]", "GP-X126", "GP-FANO-C1-CHAR2"):
            self.assertEqual(c[refused]["check"]["result"], "OUTSIDE_REACH", refused)
        self.assertEqual(c["GP-X15"]["check"]["reach"], {"char0": False, "primes": [2]})
        self.assertEqual(c["GP-FANO-C1"]["check"]["reach"], {"char0": True, "all_primes_except": [2]})
        self.assertEqual(c["GP-FANO-F2"]["check"]["reach"], {"char0": False, "primes": [2]})


if __name__ == "__main__":
    unittest.main()
