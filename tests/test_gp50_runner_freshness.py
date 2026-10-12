"""Release plan A3: a runner is fresh only if its stamp records the content identity of the sources it
was built from. Modification times play no part: a touch is not a change, an edit always is."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_runner_freshness", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)


class TreeIdentity(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="gp-fresh-"))
        self.addCleanup(shutil.rmtree, self.dir, ignore_errors=True)
        self.a, self.b = self.dir / "A.lean", self.dir / "B.lean"
        self.a.write_bytes(b"def a := 1\n")
        self.b.write_bytes(b"def b := 2\n")

    def identity(self):
        return gp.tree_identity([self.a, self.b], base=self.dir)

    def test_touch_is_not_a_change(self):
        before = self.identity()
        os.utime(self.a, (1, 1))
        os.utime(self.b, None)
        self.assertEqual(self.identity(), before)

    def test_edit_with_an_old_timestamp_is_a_change(self):
        before = self.identity()
        stamp = self.a.stat().st_mtime
        self.a.write_bytes(b"def a := 3\n")
        os.utime(self.a, (stamp - 3600, stamp - 3600))
        self.assertNotEqual(self.identity(), before)

    def test_moving_content_between_files_is_a_change(self):
        before = self.identity()
        self.a.write_bytes(b"def b := 2\n")
        self.b.write_bytes(b"def a := 1\n")
        self.assertNotEqual(self.identity(), before)


class Stamp(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="gp-stamp-"))
        self.addCleanup(shutil.rmtree, self.dir, ignore_errors=True)
        self.exe = self.dir / "runner.exe"
        self.exe.write_bytes(b"binary")

    def test_missing_runner_or_stamp_is_stale(self):
        self.assertTrue(gp.stale(self.dir / "absent.exe"))
        self.assertTrue(gp.stale(self.exe))

    def test_matching_stamp_is_fresh(self):
        gp.write_stamp(self.exe, gp.tree_identity(gp.runner_sources()))
        self.assertFalse(gp.stale(self.exe))

    def test_mismatched_or_corrupt_stamp_is_stale(self):
        gp.write_stamp(self.exe, "0" * 64)
        self.assertTrue(gp.stale(self.exe))
        gp.stamp_path(self.exe).write_text("not json", encoding="utf-8")
        self.assertTrue(gp.stale(self.exe))

    def test_stamp_records_only_the_identity(self):
        gp.write_stamp(self.exe, "ab" * 32)
        self.assertEqual(json.loads(gp.stamp_path(self.exe).read_text(encoding="utf-8")),
                         {"sources_sha256": "ab" * 32})


if __name__ == "__main__":
    unittest.main()
