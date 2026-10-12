"""HW61 G-4: the unit-distance graph encoder is deterministic, puts no constraint on non-edges, guards
every pair, and matches the Lean encoder (`GPProfile.UDG.Data.system`) term for term."""
import importlib.util
import itertools
import json
import os
import random
import subprocess
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("encode_udg", ROOT / "tools/encode-udg.py")
enc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(enc)

K4 = {"name": "K4", "n": 4, "edges": [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]}
C4 = {"name": "C4", "n": 4, "edges": [[0, 1], [1, 2], [2, 3], [3, 0]]}
MOSER = {"name": "moser", "n": 7, "edges": [[0, 1], [0, 2], [1, 2], [1, 3], [2, 3], [0, 4], [0, 5], [4, 5],
                                              [4, 6], [5, 6], [3, 6]]}
GADGETS = [  # artwaste data/tu-gadgets.json at ba1c76fd
    (6, [[0, 1], [0, 3], [0, 4], [1, 2], [2, 3], [2, 5], [3, 4], [4, 5]]),
    (7, [[0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 6], [2, 3], [2, 4], [2, 5], [2, 6], [5, 6]]),
    (7, [[0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 6], [2, 3], [2, 5], [2, 6], [4, 5], [5, 6]]),
    (8, [[0, 1], [0, 2], [0, 6], [1, 3], [1, 7], [2, 3], [2, 5], [2, 6], [3, 4], [4, 5], [4, 7], [5, 6]]),
    (8, [[0, 1], [0, 2], [0, 6], [1, 3], [1, 7], [2, 3], [2, 5], [3, 4], [4, 5], [4, 7], [5, 6]]),
]


def value(text, point):
    # Safe here: the text is the encoder's own output for fixed test inputs (only variable names,
    # integers and + - * ^), evaluated with no builtins, as in test_gp50_matroid_encoding.
    return eval(text.replace("^", "**"), {}, dict(point))


def point(coords):
    return {f"{c}{i + 1}": Fraction(v) for i, xy in enumerate(coords) for c, v in zip("xy", xy)}


def random_graph(rng, n, m):
    pairs = list(itertools.combinations(range(n), 2))
    return {"name": f"r{n}-{m}", "n": n, "edges": [list(p) for p in rng.sample(pairs, m)]}


def samples():
    rng = random.Random(61)
    out = [(K4, False), (K4, True), (C4, False), (MOSER, False), (MOSER, True),
           ({"name": "petersen", "n": 10, "edges": enc.graph6_decode("IheA@GUAo")[1]}, False),
           ({"name": "empty3", "n": 3, "edges": []}, True)]
    out += [({"name": f"gadget{k}", "n": n, "edges": e}, False) for k, (n, e) in enumerate(GADGETS)]
    out += [(random_graph(rng, 9, 14), False), (random_graph(rng, 12, 20), True),
            (random_graph(rng, 22, 61), False), (random_graph(rng, 22, 61), True)]
    return out


class UDGEncodingTests(unittest.TestCase):
    def test_deterministic_under_input_order(self):
        shuffled = dict(K4, edges=[list(reversed(e)) for e in reversed(K4["edges"])])
        self.assertEqual(enc.encode(K4), enc.encode(shuffled))
        self.assertNotEqual(enc.encode(K4)["digest"], enc.encode(C4)["digest"])
        self.assertNotEqual(enc.encode(K4)["digest"], enc.encode(K4, gauge=True)["digest"])

    def test_shape(self):
        e = enc.encode(MOSER)
        self.assertEqual(e["variables"][:4], ["x1", "y1", "x2", "y2"])
        self.assertEqual(len(e["variables"]), 14)
        self.assertEqual(len(e["equations"]), 11)  # one per edge, none for non-edges
        self.assertEqual(len(e["nonzero"]), 21)  # every pair, edges included
        self.assertEqual(e["premise"]["theorem"], "GPBinding.UDG.udg_frame_iff")
        self.assertIsNone(e["gauge"])
        g = enc.encode(MOSER, gauge=True)
        self.assertEqual(g["gauge"], [0, 1])
        self.assertEqual(g["equations"][:4], ["x1", "y1", "x2 - 1", "y2"])
        self.assertEqual(g["equations"][4:], e["equations"])

    def test_graph6(self):
        self.assertEqual(enc.graph6_decode("C~"), (4, [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3]]))
        n, edges = enc.graph6_decode("IheA@GUAo")
        self.assertEqual((n, len(edges)), (10, 15))
        self.assertTrue(all(sum(v in e for e in edges) == 3 for v in range(10)))
        with self.assertRaises(ValueError):
            enc.graph6_decode("C~~")

    def test_unit_square_and_extra_unit_distances(self):
        square = point([(0, 0), (1, 0), (1, 1), (0, 1)])
        e = enc.encode(C4)
        self.assertEqual({value(q, square) for q in e["equations"]}, {0})
        self.assertNotIn(0, {value(g, square) for g in e["nonzero"]})
        # The path 0-1-2-3 on the same points: its non-edge 3 0 is also at unit distance, which the
        # system allows (no non-edge constraint, M5 pitfall 4).
        p = enc.encode({"n": 4, "edges": [[0, 1], [1, 2], [2, 3]]})
        self.assertEqual({value(q, square) for q in p["equations"]}, {0})
        self.assertNotIn(0, {value(g, square) for g in p["nonzero"]})
        # A collision (vertices 0 and 2 at one point) satisfies the edges but fails a guard.
        collide = point([(0, 0), (1, 0), (0, 0), (1, 0)])
        c = enc.encode({"n": 4, "edges": [[0, 1], [1, 2], [2, 3]]})
        self.assertEqual({value(q, collide) for q in c["equations"]}, {0})
        self.assertIn(0, {value(g, collide) for g in c["nonzero"]})

    def test_refuses_non_simple_input(self):
        for bad in ({"n": 3, "edges": [[0, 0]]}, {"n": 3, "edges": [[0, 3]]}, {"n": -1, "edges": []},
                    {"n": 3, "edges": [[0, 1, 2]]}):
            with self.assertRaises(ValueError):
                enc.encode(bad)

    def test_lean_differential(self):
        """The Python encoder's polynomials equal the Lean encoder's, term for term, on sample graphs."""
        profile = ROOT / "profile"
        if not (profile / ".lake/build/lib/lean/GPProfile/UDG.olean").exists():
            self.skipTest("GPProfile.UDG not built")
        cases = samples()
        lits = ", ".join("⟨{}, [{}], {}⟩".format(g["n"], ", ".join(f"({i}, {j})" for i, j in g["edges"]),
                                                  "true" if gauge else "false") for g, gauge in cases)
        src = ("import GPProfile.UDG\nimport Lean.Data.Json\nopen GPProfile GPProfile.UDG Lean\n"
               "def termJ (t : List Nat × Rat) : Json := Json.arr #[toJson t.1, toJson t.2.num, toJson t.2.den]\n"
               "def polyJ (p : Sparse) : Json := Json.arr (p.map termJ).toArray\n"
               "def sysJ (D : Data) : Json := match D.system with\n"
               "  | none => Json.null\n"
               "  | some (v, e, g) => Json.arr #[toJson v, Json.arr (e.map polyJ).toArray, "
               "Json.arr (g.map polyJ).toArray]\n"
               f"#eval IO.println (Json.compress (Json.arr (([{lits}] : List Data).map sysJ).toArray))\n")
        path = profile / "tmp" / "UDGDifferential.lean"
        path.parent.mkdir(exist_ok=True)
        path.write_bytes(src.encode("utf-8"))
        try:
            toolchain = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains" / (
                profile / "lean-toolchain").read_text(encoding="utf-8").strip().replace("/", "--").replace(":", "---")
            lake = toolchain / "bin" / ("lake.exe" if os.name == "nt" else "lake")
            run = subprocess.run([str(lake), "env", "lean", "tmp/UDGDifferential.lean"], cwd=profile,
                                 capture_output=True, text=True, encoding="utf-8")
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        finally:
            path.unlink(missing_ok=True)
        lean = json.loads(run.stdout.strip().splitlines()[-1])
        self.assertEqual(len(lean), len(cases))
        for (g, gauge), got in zip(cases, lean):
            n, edges = enc.canonical(g)
            names, eqs, guards = enc.polys(n, edges, gauge)
            want = [names, [dict(p) for p in eqs], [dict(p) for p in guards]]
            self.assertIsNotNone(got, g["name"])
            as_dict = lambda poly: {tuple(e): Fraction(num, den) for e, num, den in poly}
            self.assertEqual(got[0], want[0], g["name"])
            self.assertEqual([as_dict(p) for p in got[1]], want[1], g["name"])
            self.assertEqual([as_dict(p) for p in got[2]], want[2], g["name"])
            # The text the CLI files is the same polynomial.
            e = enc.encode(g, gauge)
            rng = random.Random(len(edges))
            pt = {v: Fraction(rng.randint(-5, 5), rng.randint(1, 4)) for v in names}
            ev = lambda d: sum(c * eval_mono(m, names, pt) for m, c in d.items())
            self.assertEqual([value(t, pt) for t in e["equations"]], [ev(d) for d in want[1]])
            self.assertEqual([value(t, pt) for t in e["nonzero"]], [ev(d) for d in want[2]])


def eval_mono(m, names, pt):
    out = Fraction(1)
    for v, k in zip(names, m):
        out *= pt[v] ** k
    return out


if __name__ == "__main__":
    unittest.main()
