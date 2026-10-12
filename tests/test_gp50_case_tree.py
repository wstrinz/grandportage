"""G-6: refutation case trees (`case_tree` certificates) through the `gp` CLI, decided by `gp_ledger3`.

K₂,₃ (parts {0, 1} and {2, 3, 4}) is not a unit-distance graph: the rhombus relations of the 4-cycles
0-2-1-3 and 0-2-1-4 give p3 = p4, against the distinctness guard on {3, 4} (an L1a collision). The
controls are refused: a rhombus without a guard on a diagonal pair, a split with a missing branch, a
leaf wrong by one coefficient, and a ℂ-scope (characteristic 0) or semireal claim offered a tree.

L1b (`unit` steps): Globus–Parshall's GP5, filed with --udg, needs one derived unit edge (p0 p3, from the
rhombi 0-1-5-6 and 1-3-4-5 and the edge 46) before K₄ on {0, 1, 2, 3} collides 0 and 1. Its controls are a
missing diagonal guard, a via pair that is not an edge, a wrong sign and an off-by-one weight. Selected guards
(`guards`) on sos and ordered receipts: only the named guards enter the guard term; an index past the
guards is refused.
"""
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_case_tree", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

EDGES = [(0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4)]
PAIRS = [(i, j) for i in range(5) for j in range(i + 1, 5)]
POINTS = [[f"x{i}", f"y{i}"] for i in range(5)]


def d2(i, j):
    return f"x{i}^2 - 2*x{i}*x{j} + x{j}^2 + y{i}^2 - 2*y{i}*y{j} + y{j}^2"


def k23(drop=()):
    return {"variables": [v for p in POINTS for v in p], "equations": [d2(i, j) + " - 1" for i, j in EDGES],
            "nonzero": [d2(i, j) for i, j in PAIRS if (i, j) not in drop]}


def l1a(weight="-1"):
    return {"collision": {"rhombi": [["1", [0, 2, 1, 3]], [weight, [0, 2, 1, 4]]], "pair": [4, 3]}}


def tree(t):
    return {"certificate": {"type": "case_tree", "points": POINTS, "tree": t}}


GP5 = {"name": "GP5", "n": 7, "edges": [[0, 1], [0, 2], [0, 6], [1, 2], [1, 3], [1, 5], [2, 3], [3, 4], [4, 5],
                                        [4, 6], [5, 6]]}
GP5_POINTS = [[f"x{i + 1}", f"y{i + 1}"] for i in range(7)]


def gp5_system(drop_guard=None, drop_edge=None):
    """GP5's --udg system (tools/encode-udg.py's form) with one guard or one edge equation left out."""
    def d(i, j):
        return f"(x{i + 1} - x{j + 1})^2 + (y{i + 1} - y{j + 1})^2"
    return {"variables": [v for p in GP5_POINTS for v in p],
            "equations": [d(i, j) + " - 1" for i, j in GP5["edges"] if [i, j] != drop_edge],
            "nonzero": [d(i, j) for i in range(7) for j in range(i + 1, 7) if [i, j] != drop_guard]}


def l1b(weight="1", sign=-1, via=(4, 6)):
    k4 = {"collision": {"rhombi": [["1/2", [0, 1, 2, 3]], ["1/2", [0, 1, 3, 2]]], "pair": [0, 1]}}
    return {"certificate": {"type": "case_tree", "points": GP5_POINTS, "tree": {
        "unit": {"rhombi": [["1", [0, 1, 5, 6]], [weight, [1, 3, 4, 5]]], "pair": [0, 3], "via": list(via),
                 "sign": sign},
        "then": k4}}}


class GpCaseTree(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = Path(tempfile.mkdtemp())
        (cls.dir / "campaign.json").write_text(json.dumps({"name": "G-6 case-tree controls", "family": []}))
        cls.gp("init")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    @classmethod
    def gp(cls, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(cls.dir), *args])
        return code, out.getvalue() + err.getvalue()

    def file(self, name, body):
        path = self.dir / f"{name}.json"
        path.write_text(json.dumps(body), encoding="utf-8")
        return str(path)

    def claim(self, label, system, *scope):
        code, out = self.gp("claim", label, "--system", self.file(label, system), "--kind", "EMPTY", *scope)
        self.assertEqual(code, 0, out)

    def held(self, label, receipt):
        code, out = self.gp("submit", label, self.file(label + "-receipt", receipt))
        self.assertEqual(code, 0, out)
        self.assertIn(f"held: {label}", out)
        return out

    def refused(self, label, receipt, *needles):
        code, out = self.gp("submit", label, self.file(label + "-refused", receipt))
        self.assertNotEqual(code, 0, out)
        for n in needles:
            self.assertIn(n, out)
        return out

    def test_1_l1a_held_with_meaning(self):
        self.claim("k23", k23(), "--real")
        # (3) A leaf wrong by one coefficient.
        self.refused("k23", tree(l1a("-2")), "case-tree receipt is refused",
                     "the weighted rhombus relations do not sum to p4 - p3")
        self.held("k23", tree(l1a()))
        code, out = self.gp("explain", "k23")
        self.assertEqual(code, 0, out)
        self.assertIn("1 L1a collision leaves (2 rhombus relations)", out)
        self.assertIn("rhombus_relation", out)
        self.assertIn("no OPEN premise", out)

    def test_2_no_diagonal_guard(self):
        # (1) Injectivity is explicit: without a guard on the diagonal pair {2, 3} the rhombus 0-2-1-3 is refused.
        self.claim("k23-no23", k23(drop=[(2, 3)]), "--real")
        self.refused("k23-no23", tree(l1a()), "no distinctness guard cited for the diagonal (2,3)")
        # Citing another guard (index 1 is the guard on {0, 2}, an edge) for that diagonal is refused too.
        cited = tree({"collision": {"rhombi": [["1", [0, 2, 1, 3], [0, 1, 3, 2], [0, 1]],
                                               ["-1", [0, 2, 1, 4], [0, 1, 5, 4], [0, 7]]], "pair": [4, 3], "guard": 8}})
        cited["certificate"]["cited"] = True
        self.refused("k23-no23", cited, "no distinctness guard cited for the diagonal (2,3)")

    def test_3_splits(self):
        self.claim("k23-split", k23(), "--real")
        # (2) A split with a missing branch is refused (it does not even elaborate).
        self.refused("k23-split", tree({"split": "sign", "poly": "x0 - x1", "neg": l1a(), "zero": l1a()}),
                     "a split lacks its pos branch")
        # A split whose branches all close is held.
        self.held("k23-split", tree({"split": "sign", "poly": "x0 - x1", "neg": l1a(), "zero": l1a(), "pos": l1a()}))
        # x^2 + 1 = 0 split on x = 0 / x != 0, with ordered (ideal / SOS) leaves.
        self.claim("x2p1", {"variables": ["x"], "equations": ["x^2 + 1"]}, "--real")
        self.held("x2p1", {"certificate": {"type": "case_tree", "points": [], "tree": {
            "split": "zero", "poly": "x",
            "zero": {"ordered": {"cofactors": ["-1", "x"]}},
            "nonzero": {"ordered": {"cofactors": ["-1"], "cone": [{"squares": ["x"]}]}}}}})

    def test_5_l1b_unit_step(self):
        code, out = self.gp("claim", "gp5", "--udg", self.file("gp5-graph", GP5), "--kind", "EMPTY", "--real")
        self.assertEqual(code, 0, out)
        # The collision alone is refused: the edge 03 is only derived.
        k4 = l1b()
        k4["certificate"]["tree"] = k4["certificate"]["tree"]["then"]
        self.refused("gp5", k4, "case-tree receipt is refused", "a cited edge equation is not the unit-distance")
        # (3) A wrong sign, (4) an off-by-one weight: the relations do not sum to (p0 - p3) - s (p4 - p6).
        self.refused("gp5", l1b(sign=1), "unit (0,3): the weighted rhombus relations do not sum to (p0 - p3) - (p4 - p6)")
        self.refused("gp5", l1b(weight="2"), "unit (0,3): the weighted rhombus relations do not sum to (p0 - p3) - (p6 - p4)")
        self.refused("gp5", l1b(sign=2), "unit (0,3): the sign is 2, not 1 or -1")
        self.held("gp5", l1b())
        code, out = self.gp("explain", "gp5")
        self.assertEqual(code, 0, out)
        self.assertIn("1 L1b unit steps", out)
        self.assertIn("unitOk_real", out)
        # (1) A missing diagonal guard ({0, 5} is a diagonal of the rhombus 0-1-5-6).
        self.claim("gp5-no05", gp5_system(drop_guard=[0, 5]), "--real")
        self.refused("gp5-no05", l1b(), "rhombus (0,1,5,6): no distinctness guard cited for the diagonal (0,5)")
        # (2) The via pair is not an edge (no rhombus uses the edge 46, so only the step fails).
        self.claim("gp5-no46", gp5_system(drop_edge=[4, 6]), "--real")
        self.refused("gp5-no46", l1b(), "unit (0,3): (4,6) is not an edge of the branch")

    def test_6_selected_guards(self):
        # x^2 + y^2 = 0 with guards x^200 and y: every guard is over the degree budget, guard 1 alone is not.
        circ = {"variables": ["x", "y"], "equations": ["x^2 + y^2"], "nonzero": ["x^200", "y"]}
        self.claim("circ-sos", circ, "--real")
        sos = {"type": "sos", "cofactors": ["-1"], "squares": ["x"], "guard_power": 1}
        self.refused("circ-sos", {"certificate": sos}, "exceeds the degree or size budget")
        self.refused("circ-sos", {"certificate": dict(sos, guards=[2])}, "selected guard index is past")
        self.held("circ-sos", {"certificate": dict(sos, guards=[1])})
        # [index, exponent]: (y^2)^2 + (xy)^2 - y^2 (x^2 + y^2) = 0.
        self.claim("circ-sos2", circ, "--semireal")
        self.held("circ-sos2", {"certificate": {"type": "sos", "cofactors": ["-y^2"], "squares": ["x*y"],
                                                "guard_power": 1, "guards": [[1, 2]]}})
        self.claim("circ-ord", dict(circ, signs=[["y", ">0"]]), "--real")
        ordered = {"type": "ordered", "cofactors": ["-1"], "positive_powers": [0], "guard_power": 1,
                   "cone": [{"squares": ["x"]}]}
        self.refused("circ-ord", {"certificate": ordered}, "exceeds the degree or size budget")
        self.held("circ-ord", {"certificate": dict(ordered, guards=[1])})

    def test_4_scope_c_and_semireal_refused(self):
        # (4) A ℂ-scope (characteristic 0) claim never receives a case tree, and nothing carries one into ℝ.
        self.claim("k23-c", k23(), "--char0")
        self.refused("k23-c", tree(l1a()), "unknown certificate type", "characteristic 0")
        self.claim("k23-semireal", k23(), "--semireal")
        self.refused("k23-semireal", tree(l1a()), "a case tree is admitted only for EMPTY claims at real scope")
        lin = {"variables": ["x"], "equations": ["x - 1", "x - 2"], "nonzero": []}
        self.claim("lin-c", lin, "--char0")
        self.held("lin-c", {"certificate": {"type": "ideal", "cofactors": ["1", "-1"], "m": 0, "k": 0}})
        self.claim("lin-from-c", lin, "--real")
        self.refused("lin-from-c", {"rule": {"type": "narrow"}, "premises": ["lin-c"]},
                     "no scope order from characteristic 0 to real")


if __name__ == "__main__":
    unittest.main()
