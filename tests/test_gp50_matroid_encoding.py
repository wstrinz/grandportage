"""Post-G3a §4.3: the rank-3 matroid encoder is deterministic, framed, and reproduces the F0 controls."""
import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("encode_matroid", ROOT / "tools/encode-matroid.py")
enc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(enc)

FANO = {"name": "F7", "elements": [str(i) for i in range(1, 8)],
        "lines": [["1", "2", "4"], ["2", "3", "5"], ["3", "4", "6"], ["4", "5", "7"], ["5", "6", "1"],
                  ["6", "7", "2"], ["7", "1", "3"]]}
NON_FANO = dict(FANO, name="F7-", lines=[l for l in FANO["lines"] if l != ["4", "5", "7"]])
# One integer point: an F_2 point of F7 and a rational point of F7- whose guards include 2.
POINT = {"x4": 1, "y4": 1, "z4": 0, "x5": 0, "y5": 1, "z5": 1, "x7": 1, "y7": 0, "z7": 1}


def value(text):
    # The text is the encoder's own output for the fixed inputs above: only names, integers, + - * ^.
    return eval(text.replace("^", "**"), {}, dict(POINT))


class MatroidEncodingTests(unittest.TestCase):
    def test_deterministic_under_input_order(self):
        shuffled = dict(FANO, lines=[list(reversed(l)) for l in reversed(FANO["lines"])])
        self.assertEqual(enc.encode(FANO), enc.encode(shuffled))

    def test_frame_and_premise(self):
        e = enc.encode(FANO)
        self.assertEqual(e["frame"], ["1", "2", "3", "6"])
        self.assertEqual(e["premise"]["name"], "ENCODING-FRAME")
        self.assertEqual(e["premise"]["status"], "OPEN")
        self.assertEqual(len(e["variables"]), 9)

    def test_fano_point_is_an_f2_point_only(self):
        e = enc.encode(FANO)
        self.assertTrue(all(value(q) % 2 == 0 for q in e["equations"]))
        self.assertTrue(all(value(g) % 2 == 1 for g in e["nonzero"]))
        self.assertNotEqual([value(q) for q in e["equations"]], [0] * len(e["equations"]))

    def test_non_fano_point_is_rational_with_guard_2(self):
        e = enc.encode(NON_FANO)
        self.assertEqual({value(q) for q in e["equations"]}, {0})
        guards = {value(g) for g in e["nonzero"]}
        self.assertNotIn(0, guards)
        self.assertIn(2, guards)

    def test_digest_binds_the_system(self):
        self.assertNotEqual(enc.encode(FANO)["digest"], enc.encode(NON_FANO)["digest"])

    def test_refuses_non_matroids(self):
        with self.assertRaises(ValueError):
            enc.encode(dict(FANO, lines=FANO["lines"] + [["1", "2", "3"]]))
        with self.assertRaises(ValueError):
            enc.encode({"name": "line", "elements": ["a", "b", "c"], "lines": [["a", "b", "c"]]})


if __name__ == "__main__":
    unittest.main()
