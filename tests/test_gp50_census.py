"""Phase 4 (post-G2 §4, M4 §5): census controls and traps through the census profile and the Kernel fold.

R(3,3) = 6 as two held claims: a C5 witness (EXISTS at 5) and an LRAT refutation of the CNF Lean emits
(NONE at 6). Traps: a timeout (no receipt), "none found up to n" (scope wider than the reach), a
truncated proof, and a witness that fails the predicate.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

EXE_SUFFIX = ".exe" if os.name == "nt" else ""
ELAN_HOME = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
CENSUS = ROOT / "census"
TOOLCHAIN = ELAN_HOME / "toolchains" / (CENSUS / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")
RUNNER = CENSUS / (".lake/build/bin/gp_census" + EXE_SUFFIX)
CADICAL = TOOLCHAIN / ("bin/cadical" + EXE_SUFFIX)


def triple(body):
    return {"exists": "x", "body": {"exists": "y", "body": {"exists": "z", "body": {"and": body}}}}


R33 = {"colors": 1, "predicate": {"and": [
    {"not": triple([{"adj": ["x", "y"]}, {"adj": ["y", "z"]}, {"adj": ["x", "z"]}])},
    {"not": triple([{"not": {"eq": ["x", "y"]}}, {"not": {"eq": ["y", "z"]}}, {"not": {"eq": ["x", "z"]}},
                    {"not": {"adj": ["x", "y"]}}, {"not": {"adj": ["y", "z"]}}, {"not": {"adj": ["x", "z"]}}])}]}}


class CensusControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"])
        subprocess.run([str(TOOLCHAIN / ("bin/lake" + EXE_SUFFIX)), "build", "gp_census"], cwd=CENSUS,
                       env=env, check=True, capture_output=True)
        cls.tmp = Path(tempfile.mkdtemp())
        claim = cls.tmp / "r33.json"
        claim.write_text(json.dumps(dict(R33, kind="NONE")), encoding="utf-8")
        cnf = subprocess.run([str(RUNNER), "cnf", str(claim), "6"], check=True, capture_output=True,
                             text=True).stdout
        (cls.tmp / "r33_6.cnf").write_text(cnf, encoding="utf-8", newline="\n")
        solve = subprocess.run([str(CADICAL), "--lrat=true", "--binary=false", "-q", "r33_6.cnf", "r33_6.lrat"],
                               cwd=cls.tmp, capture_output=True, text=True)
        assert solve.returncode == 20, solve.stdout  # 20: UNSATISFIABLE
        proof = (cls.tmp / "r33_6.lrat").read_text(encoding="utf-8")
        lrat = {"type": "lrat", "n": 6, "proof": proof}
        # A refutation of some other encoding: GP's CNF plus one extra unit clause.
        lines = cnf.splitlines()
        nv, nc = map(int, lines[0].split()[2:4])
        other_cnf = f"p cnf {nv} {nc + 1}\n1 0\n" + "\n".join(lines[1:]) + "\n"
        (cls.tmp / "other.cnf").write_text(other_cnf, encoding="utf-8", newline="\n")
        subprocess.run([str(CADICAL), "--lrat=true", "--binary=false", "-q", "other.cnf", "other.lrat"],
                       cwd=cls.tmp, capture_output=True)
        other = (cls.tmp / "other.lrat").read_text(encoding="utf-8")
        c5 = {"edges": [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0]]}
        claims = [
            dict(R33, kind="NONE", key=1, scope=[6], certificate=lrat),
            dict(R33, kind="NONE", key=2, scope=[6]),
            dict(R33, kind="NONE", key=3, scope=[6, 7], certificate=lrat),
            dict(R33, kind="NONE", key=4, scope=[6], certificate=dict(lrat, proof=proof[: len(proof) // 2])),
            dict(R33, kind="EXISTS", key=5, scope=[5], certificate={"type": "witness", "n": 5, "witness": c5}),
            dict(R33, kind="EXISTS", key=6, scope=[5],
                 certificate={"type": "witness", "n": 5, "witness": {"edges": [[0, 1], [1, 2], [2, 0]]}}),
            dict(R33, kind="NONE", key=7, scope=[6], certificate=dict(lrat, proof=other)),
        ]
        ledger = cls.tmp / "ledger.json"
        ledger.write_text(json.dumps({"claims": claims}), encoding="utf-8")
        out = subprocess.run([str(RUNNER), "run", str(ledger)], check=True, capture_output=True, text=True)
        cls.claims = {c["key"]: c for c in json.loads(out.stdout)["claims"]}

    def test_r33_both_halves_held(self):
        self.assertTrue(self.claims[1]["held"])
        self.assertEqual(self.claims[1]["reach"], [6])
        self.assertTrue(self.claims[5]["held"])

    def test_timeout_is_not_unsat(self):
        self.assertFalse(self.claims[2]["held"])

    def test_none_up_to_n_is_not_none_beyond(self):
        self.assertFalse(self.claims[3]["held"])
        self.assertEqual(self.claims[3]["reach"], [6])

    def test_truncated_proof_is_refused(self):
        self.assertFalse(self.claims[4]["held"])

    def test_witness_must_satisfy(self):
        self.assertFalse(self.claims[6]["held"])

    def test_refutation_of_another_encoding_refused(self):
        # GP rebuilds its own CNF; an LRAT proof for any other formula does not check against it.
        self.assertFalse(self.claims[7]["held"])

    def test_floating_point_witness_rejected(self):
        bad = dict(R33, kind="EXISTS", key=1, scope=[5],
                   certificate={"type": "witness", "n": 5, "witness": {"edges": [[0, 1.0], [1, 2]]}})
        path = self.tmp / "float.json"
        path.write_text(json.dumps({"claims": [bad]}), encoding="utf-8")
        out = subprocess.run([str(RUNNER), "run", str(path)], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0)


def dimacs(clauses, nvars):
    return f"p cnf {nvars} {len(clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)


def parse(text):
    head = next(l for l in text.splitlines() if l.startswith("p cnf"))
    clauses = [[int(t) for t in l.split()[:-1]] for l in text.splitlines() if l and l[0] not in "pc"]
    return int(head.split()[2]), clauses


class CensusCover(unittest.TestCase):
    """NONE by cube and conquer (M4 §4): R(3,3) at 6 split on the atom of the pair {0, 1}. Each leaf is
    the cube's units followed by GP's CNF; the cover refutes the negated cubes. A cover missing a cube
    is satisfiable, so it has no refutation (the non-exhaustive cover trap)."""

    @classmethod
    def setUpClass(cls):
        CensusControls.setUpClass()
        cls.tmp = Path(tempfile.mkdtemp())
        claim = cls.tmp / "r33.json"
        claim.write_text(json.dumps(dict(R33, kind="NONE")), encoding="utf-8")
        nvars, base = parse(subprocess.run([str(RUNNER), "cnf", str(claim), "6"], check=True, capture_output=True,
                                           text=True).stdout)
        x = 0 * 6 + 1 + 1  # edgeVar 6 0 1 = 1, as a 1-based DIMACS variable

        def refute(clauses, name):
            (cls.tmp / f"{name}.cnf").write_text(dimacs(clauses, nvars), encoding="utf-8", newline="\n")
            r = subprocess.run([str(CADICAL), "--lrat=true", "--binary=false", "-q", f"{name}.cnf", f"{name}.lrat"],
                               cwd=cls.tmp, capture_output=True, text=True)
            return r.returncode, (cls.tmp / f"{name}.lrat").read_text(encoding="utf-8") if r.returncode == 20 else ""

        cubes = [[x], [-x]]
        leaves = [refute([[lit] for lit in c] + base, f"leaf{i}")[1] for i, c in enumerate(cubes)]
        _, cover_proof = refute([[-lit for lit in c] for c in cubes], "cover")
        cls.short_rc, _ = refute([[-lit for lit in c] for c in cubes[:1]], "short")
        good = {"type": "cover", "n": 6, "cubes": cubes, "leaves": leaves, "cover_proof": cover_proof}
        claims = [
            dict(R33, kind="NONE", key=1, scope=[6], certificate=good),
            dict(R33, kind="NONE", key=2, scope=[6], certificate=dict(good, cubes=cubes[:1], leaves=leaves[:1])),
        ]
        (cls.tmp / "ledger.json").write_text(json.dumps({"claims": claims}), encoding="utf-8")
        out = subprocess.run([str(RUNNER), "run", str(cls.tmp / "ledger.json")], check=True, capture_output=True,
                             text=True)
        cls.claims = {c["key"]: c for c in json.loads(out.stdout)["claims"]}

    def test_cover_held(self):
        self.assertTrue(self.claims[1]["held"])

    def test_non_exhaustive_cover_refused(self):
        self.assertEqual(self.short_rc, 10)  # one cube alone does not cover: satisfiable
        self.assertFalse(self.claims[2]["held"])


class CensusCount(unittest.TestCase):
    """COUNT = 11 for graphs on 4 vertices (M4 §5): eleven witnesses, distinct canonical forms, and a
    block-and-refute EXHAUSTIVE under the full lex-leader. The listing is proposed outside GP."""

    @classmethod
    def setUpClass(cls):
        import itertools
        CensusControls.setUpClass()
        cls.tmp = Path(tempfile.mkdtemp())
        n, pairs = 4, [(a, b) for a in range(4) for b in range(4) if a < b]
        perms = list(itertools.permutations(range(n)))

        def vec(edges):
            return tuple(1 if p in edges else 0 for p in pairs)

        def relabel(edges, l):
            return {(i, j) for i, j in pairs if (min(l[i], l[j]), max(l[i], l[j])) in edges}

        reps = sorted({min(vec(relabel({p for i, p in enumerate(pairs) if bits >> i & 1}, l)) for l in perms)
                       for bits in range(2 ** len(pairs))})
        cls.classes = len(reps)
        listing = [{"edges": [list(p) for p, b in zip(pairs, r) if b]} for r in reps]
        claim = {"colors": 1, "predicate": True, "kind": "COUNT", "count": len(reps)}
        (cls.tmp / "claim.json").write_text(json.dumps(claim), encoding="utf-8")

        def certificate(lst, name):
            cert = {"type": "listed", "n": n, "list": lst, "labels": [list(l) for l in perms]}
            (cls.tmp / f"{name}.json").write_text(json.dumps(cert), encoding="utf-8")
            cnf = subprocess.run([str(RUNNER), "listcnf", str(cls.tmp / "claim.json"), str(cls.tmp / f"{name}.json")],
                                 check=True, capture_output=True, text=True).stdout
            (cls.tmp / f"{name}.cnf").write_text(cnf, encoding="utf-8", newline="\n")
            r = subprocess.run([str(CADICAL), "--lrat=true", "--binary=false", "-q", f"{name}.cnf", f"{name}.lrat"],
                               cwd=cls.tmp, capture_output=True, text=True)
            return cert, r.returncode, (cls.tmp / f"{name}.lrat").read_text(encoding="utf-8") if r.returncode == 20 else ""

        cert, cls.full_rc, proof = certificate(listing, "full")
        _, cls.missing_rc, _ = certificate(listing[:-1], "missing")
        full = dict(cert, proof=proof)
        claims = [
            dict(claim, key=1, scope=[4], certificate=full),
            dict(claim, key=2, scope=[4], kind="EXHAUSTIVE", list=listing, certificate=full),
            dict(claim, key=3, scope=[4], count=12, certificate=full),
            dict(claim, key=4, scope=[4], count=12, certificate=dict(full, list=listing + [{"edges": [[0, 2]]}])),
            dict(claim, key=5, scope=[4], count=10, certificate=dict(full, list=listing[:-1])),
            # Held modulo a visible OPEN premise (catalog completeness), the trusted-generator route.
            dict(claim, key=6, scope=[4], assuming_complete=listing, certificate={"type": "catalog", "n": 4}),
            dict(claim, key=7, scope=[4], count=12, assuming_complete=listing + [{"edges": [[0, 2]]}],
                 certificate={"type": "catalog", "n": 4}),
        ]
        (cls.tmp / "ledger.json").write_text(json.dumps({"claims": claims}), encoding="utf-8")
        out = subprocess.run([str(RUNNER), "run", str(cls.tmp / "ledger.json")], check=True, capture_output=True,
                             text=True)
        cls.claims = {c["key"]: c for c in json.loads(out.stdout)["claims"]}

    def test_count_and_exhaustive_held(self):
        self.assertEqual(self.classes, 11)
        self.assertEqual(self.full_rc, 20)
        self.assertTrue(self.claims[1]["held"])
        self.assertTrue(self.claims[2]["held"])

    def test_wrong_count_refused(self):
        self.assertFalse(self.claims[3]["held"])

    def test_duplicate_class_refused(self):
        # A twelfth entry isomorphic to a listed one: its canonical form repeats.
        self.assertFalse(self.claims[4]["held"])

    def test_catalog_premise(self):
        self.assertTrue(self.claims[6]["held"])   # COUNT 11 assuming the catalog is complete
        self.assertFalse(self.claims[7]["held"])  # a catalog with a repeated class

    def test_missing_class_has_no_certificate(self):
        self.assertEqual(self.missing_rc, 10)  # satisfiable: no refutation exists
        self.assertFalse(self.claims[5]["held"])


if __name__ == "__main__":
    unittest.main()
