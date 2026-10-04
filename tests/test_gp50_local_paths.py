"""Local machine paths only fall (alpha prerequisite, Will 2026-10-03): no new file gains one."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("local_paths", ROOT / "tools/check-local-paths.py")
lp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lp)


class LocalPathTests(unittest.TestCase):
    def test_no_new_local_paths(self):
        _, problems = lp.check()
        self.assertEqual(problems, [])

    def test_pattern_catches_the_known_forms(self):
        for text in [b"C:/Users/x/dev", b"F:/repos/gp", b"C:\\Users\\x", b"F:\\\\repos\\\\gp", b"/c/Users/x/.elan"]:
            with self.subTest(text=text):
                self.assertTrue(lp.PATTERN.search(text))
        for text in [b"https://github.com/wstrinz/grandportage", b"corpus/must/GP-A01.json", b"x:/tmp"]:
            with self.subTest(text=text):
                self.assertFalse(lp.PATTERN.search(text))


if __name__ == "__main__":
    unittest.main()
