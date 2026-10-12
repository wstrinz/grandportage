"""HW61 G-5: census extension covers through the census profile and the Kernel fold.

The statement is census NONE of `Extension.extPred`: every graph that is the base plus one vertex of
degree k contains some pattern. The receipt lists one hit per neighbourhood; the neighbourhoods
come from the Lean generator, so coverage is by construction.

Instance: the 5-cycle with a new vertex of degree 2. Two adjacent neighbours close a triangle; two
non-adjacent ones have a common neighbour, closing a 4-cycle. A third pattern, the induced path
(a path with its ends a required non-edge), exercises required non-edges.
Controls: a non-injective map, a missed edge, a required non-edge that is an edge, a forged list
(one neighbourhood missing, or one relabelled), a pattern list other than the claim's, a pattern
file whose hash differs from its pin, a scope wider than the reach, and a non-NONE kind.
"""
import hashlib
import importlib.util
import itertools
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

EXE = ".exe" if os.name == "nt" else ""
ELAN_HOME = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
CENSUS = ROOT / "census"
TOOLCHAIN = ELAN_HOME / "toolchains" / (CENSUS / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")
RUNNER = CENSUS / f".lake/build/bin/gp_census{EXE}"

spec = importlib.util.spec_from_file_location("gp50_extcover", ROOT / "tools/gp50_extcover.py")
ext = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ext)

C5 = "Dhc"  # graph6 of the 5-cycle 0-1-2-3-4-0
K3 = {"n": 3, "edges": [[0, 1], [1, 2], [0, 2]], "non_edges": []}
C4 = {"n": 4, "edges": [[0, 1], [1, 2], [2, 3], [3, 0]], "non_edges": []}
P3 = {"n": 3, "edges": [[0, 1], [1, 2]], "non_edges": [[0, 2]]}
PATS = [K3, C4]


def g6_check():
    n, edges = ext.g6decode(C5)
    assert n == 5 and sorted(edges) == [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)], edges


class ExtensionCover(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        g6_check()
        env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"])
        subprocess.run([str(TOOLCHAIN / f"bin/lake{EXE}"), "build", "gp_census"], cwd=CENSUS, env=env,
                       check=True, capture_output=True)
        cls.tmp = Path(tempfile.mkdtemp())
        n, edges = ext.g6decode(C5)
        cls.hits, survivors = ext.find_hits(n, edges, 2, PATS)
        assert not survivors

    def run_claims(self, claims):
        path = self.tmp / "ledger.json"
        path.write_text(json.dumps({"claims": claims}), encoding="utf-8")
        out = subprocess.run([str(RUNNER), "run", str(path)], capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        return {c["key"]: c for c in json.loads(out.stdout)["claims"]}

    def claim(self, key, hits, pats=PATS, cert_pats=None, scope=None, kind="NONE"):
        hp = self.tmp / f"h{key}.hits"
        ext.write_hits(hp, hits)
        c = ext.claim(key, C5, 2, pats, hp, {})
        if cert_pats is not None:
            c["certificate"]["patterns"] = cert_pats
        if scope is not None:
            c["scope"] = scope
        c["kind"] = kind
        return c

    def edit(self, i, p=None, mp=None, S=None):
        hits = list(self.hits)
        S0, p0, mp0 = hits[i]
        hits[i] = (S0 if S is None else S, p0 if p is None else p, mp0 if mp is None else mp)
        return hits

    def test_generator_is_complete(self):
        # The Lean generator's list is exactly the k-subsets, each once (mem_combos, nodup_combos).
        for n, k in [(5, 2), (21, 4), (21, 5)]:
            out = subprocess.run([str(RUNNER), "combos", str(n), str(k)], check=True, capture_output=True,
                                 text=True).stdout.split()
            got = [tuple(sorted(map(int, s.split(",")))) for s in out]
            self.assertEqual(len(got), len(set(got)))
            self.assertEqual(set(got), set(itertools.combinations(range(n), k)))

    def test_cover_held(self):
        out = self.run_claims([self.claim(1, self.hits)])
        self.assertTrue(out[1]["held"])
        self.assertEqual(out[1]["reach"], [6])

    def test_required_non_edge_held(self):
        n, edges = ext.g6decode(C5)
        hits, survivors = ext.find_hits(n, edges, 2, [K3, P3])
        self.assertFalse(survivors)
        out = self.run_claims([self.claim(2, hits, pats=[K3, P3])])
        self.assertTrue(out[2]["held"])

    def test_non_injective_map_refused(self):
        S, p, mp = self.hits[0]
        bad = self.edit(0, mp=[mp[0]] * len(mp))
        self.assertFalse(self.run_claims([self.claim(3, bad)])[3]["held"])

    def test_missed_edge_refused(self):
        # Send a triangle onto three vertices of the 5-cycle: one edge (0, 2) is missing.
        bad = self.edit(0, p=0, mp=[0, 1, 2])
        self.assertFalse(self.run_claims([self.claim(4, bad)])[4]["held"])

    def test_required_non_edge_violated_refused(self):
        # S = {0, 1}: the path 5-0-1 has every edge, but its ends 5, 1 are adjacent.
        n, edges = ext.g6decode(C5)
        hits, _ = ext.find_hits(n, edges, 2, [K3, P3])
        i = next(j for j, h in enumerate(hits) if h[0] == [1, 0])
        hits[i] = ([1, 0], 1, [5, 0, 1])
        self.assertFalse(self.run_claims([self.claim(5, hits, pats=[K3, P3])])[5]["held"])
        hits[i] = ([1, 0], 1, [5, 0, 4])  # 5-0-4 with 5, 4 non-adjacent: accepted
        self.assertTrue(self.run_claims([self.claim(6, hits, pats=[K3, P3])])[6]["held"])

    def test_forged_list_refused(self):
        # Coverage is by construction: a receipt missing one neighbourhood, or relabelling one, fails.
        missing = self.hits[:3] + self.hits[4:]
        relabelled = self.edit(3, S=[4, 0])
        out = self.run_claims([self.claim(7, missing), self.claim(8, relabelled)])
        self.assertFalse(out[7]["held"])
        self.assertFalse(out[8]["held"])

    def test_pattern_mismatch_refused(self):
        # The certificate's pattern list differs from the one the claim binds (one edge changed).
        other = [K3, {"n": 4, "edges": [[0, 1], [1, 2], [2, 3], [3, 1]], "non_edges": []}]
        out = self.run_claims([self.claim(9, self.hits, cert_pats=other)])
        self.assertFalse(out[9]["held"])

    def test_pattern_hash_pin_refused(self):
        pats = self.tmp / "pats.json"
        pats.write_bytes(json.dumps(PATS).encode())
        bases = self.tmp / "bases.g6"
        bases.write_text(C5 + "\n", encoding="utf-8")
        wrong = hashlib.sha256(b"not the patterns").hexdigest()
        with self.assertRaises(SystemExit):
            ext.run(bases, 2, pats, wrong, self.tmp / "pinrun")
        right = hashlib.sha256(pats.read_bytes()).hexdigest()
        s = ext.run(bases, 2, pats, right, self.tmp / "pinrun")
        self.assertEqual((s["held"], s["survivors"]), (1, 0))

    def test_scope_and_kind(self):
        out = self.run_claims([self.claim(10, self.hits, scope=[6, 7]),
                               self.claim(11, self.hits, kind="EXISTS")])
        self.assertFalse(out[10]["held"])
        self.assertEqual(out[10]["reach"], [6])
        self.assertFalse(out[11]["held"])


if __name__ == "__main__":
    unittest.main()
