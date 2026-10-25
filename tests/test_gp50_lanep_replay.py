"""GP 0.55 Lane P replay safety (a defect a trial campaign found): `gp bind --replay` ran every module of the
package in one leanchecker process, whose memory grew module by module; on its timeout gp killed `lake env` but not
leanchecker, which ran on orphaned to 49 GB. Each fix has a regression test that fails before it:

1. A capped command that times out is killed with everything it started.
2. The replay runs leanchecker once per module, and a kernel rejection is recorded with its module.
"""
import importlib.util
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_lanep_p2_tests_replay", ROOT / "tests/test_gp50_lanep_p2.py")
p2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2)
p1, gp = p2.p1, p2.gp

# A parent that starts a grandchild (as `lake env` starts leanchecker), records its pid, and waits on it.
PARENT = """import subprocess, sys
child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(300)"])
open(sys.argv[1], "w").write(str(child.pid))
child.wait()
"""


def alive(pid):
    if os.name == "nt":
        out = subprocess.run(["tasklist", "/FI", f"PID eq {pid}", "/NH"], capture_output=True, text=True).stdout
        return str(pid) in out
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    return True


class KillTree(unittest.TestCase):
    def test_timeout_kills_the_whole_tree(self):
        with tempfile.TemporaryDirectory() as d:
            script, pidfile = Path(d) / "parent.py", Path(d) / "child.pid"
            script.write_text(PARENT, encoding="utf-8")
            t0 = time.time()
            rc, out, err = gp.lanep.run_capped([sys.executable, str(script), str(pidfile)], d, None, 5)
            self.assertIsNone(rc)
            self.assertLess(time.time() - t0, 120)  # it returned: no orphan held its pipes open
            pid = int(pidfile.read_text(encoding="utf-8"))
            for _ in range(20):
                if not alive(pid):
                    break
                time.sleep(0.5)
            self.assertFalse(alive(pid), f"the grandchild {pid} outlived the timeout")


@unittest.skipUnless(p1.have_toolchain(), "the pinned Lean toolchain is not installed")
class PerModuleReplay(p2.Base, unittest.TestCase):
    def leanchecker_calls(self):
        calls, orig = [], gp.lanep.run_capped

        def counted(cmd, *a, **k):
            if any("leanchecker" in Path(str(x)).name for x in cmd):
                calls.append([str(x) for x in cmd])
            return orig(cmd, *a, **k)
        gp.lanep.run_capped = counted
        self.addCleanup(setattr, gp.lanep, "run_capped", orig)
        return calls

    def test_one_leanchecker_process_per_module(self):
        c = self.copy("per-module")
        calls = self.leanchecker_calls()
        self.assertIn("tier 2 is final", self.ok(c, "bind", "--replay"))
        rec = [r for r in gp.Ledger(c).records if r["op"] == "replay"][-1]
        self.assertGreater(len(rec["modules"]), 1)
        checked = []
        for cmd in calls:
            i = next(j for j, x in enumerate(cmd) if "leanchecker" in Path(x).name)
            self.assertEqual(len(cmd) - i - 1, 1, cmd)  # exactly one module per process
            checked.append(cmd[-1])
        self.assertEqual(checked, rec["modules"])

    def test_kernel_rejection_names_its_module(self):
        c = self.copy("per-module-skip")
        (c / "lean/Tiny/Skip.lean").write_bytes(p2.SKIP.encode("utf-8"))
        self.ok(c, "claim", "A-bad", "--lean", "A", "--theorem", "Tiny.bad")
        out = self.no(c, "bind", "--replay")
        self.assertIn("the lean4checker replay failed", out)
        rec = [r for r in gp.Ledger(c).records if r["op"] == "replay"][-1]
        self.assertEqual((rec["ok"], rec["class"], rec["module"]), (False, "kernel", "Tiny.Skip"))


if __name__ == "__main__":
    unittest.main()
