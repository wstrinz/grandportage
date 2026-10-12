"""Track E: the Comparator emitter is deterministic, covers the 3P ledger, and refuses unfaithful claims.

No Lean build here: the emitted shards are checked by stock Comparator in .github/workflows/comparator.yml.
"""
import contextlib
import copy
import importlib.util
import io
import json
import re
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAMPAIGN = ROOT / "campaigns/3p-matroids"
COMMITTED = CAMPAIGN / "warrants/comparator-MANIFEST.json"
spec = importlib.util.spec_from_file_location("comparator_emit", ROOT / "tools/comparator-emit.py")
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)

COUNTS = {"map-p": 1241, "map-s": 9, "point-p": 86, "point-s": 467, "bridge": 12, "source": 10}


def emit(out):
    with contextlib.redirect_stdout(io.StringIO()):
        E.main(["--campaign", str(CAMPAIGN), "--out", str(out)])
    return {p.relative_to(out).as_posix(): p.read_bytes() for p in sorted(out.rglob("*")) if p.is_file()}


class ComparatorEmitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.files = emit(Path(cls.tmp.name) / "a")
        cls.manifest = json.loads(cls.files["MANIFEST.json"])
        cls.raw, cls.claims, cls.sup = E.load_ledger(CAMPAIGN)
        cls.enc = E.load_encoder(ROOT / "tools/encode-matroid.py")

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_emit_twice_is_byte_identical(self):
        again = emit(Path(self.tmp.name) / "b")
        self.assertEqual(sorted(again), sorted(self.files))
        for path, data in self.files.items():
            self.assertEqual(again[path], data, path)

    def test_committed_manifest_is_current(self):
        self.assertTrue(COMMITTED.read_bytes() == self.files["MANIFEST.json"],
                        "regenerate campaigns/3p-matroids/warrants/comparator-MANIFEST.json")
        self.assertEqual(self.manifest["inputs"]["realizes_def_sha256"],
                         E.sha(E.REALIZES.encode("utf-8")))

    def test_counts_per_class_and_coverage(self):
        m = self.manifest
        self.assertEqual({k: v["emitted"] for k, v in m["classes"].items() if v["emitted"]}, COUNTS)
        self.assertEqual(m["classes"]["empty"], {"emitted": 0, "refused": 0, "deferred": 62})
        self.assertEqual(m["counts"]["refused"], 0)
        self.assertEqual(m["counts"]["claims_in_ledger"], 1891)
        self.assertEqual(m["counts"]["unsupported"], 4)
        self.assertEqual(m["counts"]["emitted"], sum(COUNTS.values()))
        self.assertEqual(len(m["claims"]), sum(COUNTS.values()))
        self.assertGreaterEqual(m["counts"]["coverage_percent"], 95.0)
        self.assertEqual(m["counts"]["coverage_percent"], round(100 * 1825 / 1891, 2))
        # every gap is listed with its reason
        gaps = m["refused"] + m["deferred"]
        self.assertEqual(len(gaps) + len(m["unsupported"]) + len(m["claims"]), 1891)
        self.assertTrue(all(r["reason"] for r in gaps))
        self.assertTrue(all(r["reason"].startswith("deferred (reprioritised 2026-10-09): EMPTY")
                            for r in m["deferred"]))

    def test_shapes(self):
        realizes = E.REALIZES
        names = {}
        for s in self.manifest["shards"]:
            chal = self.files[s["challenge"]].decode("utf-8")
            sol = self.files[s["solution"]].decode("utf-8")
            cfg = json.loads(self.files[s["config"]])
            self.assertEqual(re.findall(r"(?m)^import .*$", chal), ["import Mathlib"], s["shard"])
            self.assertEqual(re.findall(r"(?m)^import .*$", sol), ["import Mathlib"], s["shard"])
            self.assertTrue(realizes in chal and realizes in sol, s["shard"])
            self.assertEqual(set(cfg), {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"})
            self.assertEqual(cfg["permitted_axioms"], ["propext", "Quot.sound", "Classical.choice"])
            self.assertEqual(chal.count("  sorry\n"), s["claims"])
            self.assertNotIn("sorry", sol)
            for n in cfg["theorem_names"]:
                self.assertIn(f"theorem {n} ", chal)
                self.assertIn(f"theorem {n} ", sol)
                names[n] = s["shard"]
        self.assertEqual(names, {c["theorem"]: c["shard"] for c in self.manifest["claims"]})

    def test_map_p_solutions_use_part_one_only(self):
        for s in self.manifest["shards"]:
            sol = self.files[s["solution"]].decode("utf-8")
            self.assertEqual(E.PART2 in sol, s["class"] != "map-p", s["shard"])

    def refuse(self, key, cls, mutate, expect):
        c2, s2 = copy.deepcopy(self.claims), copy.deepcopy(self.sup)
        mutate(c2, s2)
        with self.assertRaises(E.Refuse) as cm:
            E.build(key, E.classify(key, c2, s2), c2, s2, CAMPAIGN, self.enc)
        self.assertIn(expect, str(cm.exception))

    def test_map_p_fidelity_mutants(self):
        K = 29  # Pappus-in-chi-2
        E.build(K, "map-p", self.claims, self.sup, CAMPAIGN, self.enc)
        first = lambda s: sorted(s[K]["receipt"]["rule"]["map"])[0]
        for mutate, expect in [
            (lambda c, s: c[K].update(kind="IN_IDEAL"), "kind/target"),
            (lambda c, s: c[K].update(target="x5"), "kind/target"),
            (lambda c, s: c[K].update(scope={"characteristic": 4}), "not prime"),
            (lambda c, s: c[K].update(scope={"characteristic": 3}), "receipt certificate at characteristic 2"),
            (lambda c, s: s[K]["receipt"]["rule"]["guard_certificates"][0].update(characteristic=3), "receipt certificate"),
            (lambda c, s: s[K]["receipt"].update(premises=[12, 13]), "premises"),
            (lambda c, s: c[12].update(scope={"characteristic": 3}), "source scope"),
            (lambda c, s: c[12]["system"].update(equations=["2*a**2 + a + 1"]), "not monic"),
            (lambda c, s: c[K].update(matroid="Desargues"), "encoding digest"),
            (lambda c, s: c[K].update(matroid="NoSuchMatroid"), "not found"),
            (lambda c, s: c[K]["system"]["nonzero"].pop(), "differs from the encoder"),
            (lambda c, s: c[K]["system"]["equations"].append("x4"), "differs from the encoder"),
            (lambda c, s: s[K]["receipt"]["rule"]["map"].pop(first(s)), "map variables"),
            (lambda c, s: s[K]["receipt"]["rule"]["map"].update({first(s): "0"}), "at the map image"),
            (lambda c, s: s[K]["receipt"]["rule"]["map"].update(
                {first(s): "a + " + s[K]["receipt"]["rule"]["map"][first(s)]}), "at the map image"),
        ]:
            self.refuse(K, "map-p", mutate, expect)

    def test_map_s_fidelity_mutants(self):
        K = 15  # AG23-in-chi, outside [3]
        E.build(K, "map-s", self.claims, self.sup, CAMPAIGN, self.enc)
        first = lambda s: sorted(s[K]["receipt"]["rule"]["map"])[0]
        for mutate, expect in [
            (lambda c, s: c[K].update(scope={"outside": []}), "is not a unit outside"),
            (lambda c, s: c[K].update(scope={"outside": [4]}), "not a list of distinct primes"),
            (lambda c, s: s[K]["receipt"]["rule"]["guard_certificates"][0].update(characteristic=3), "receipt certificate"),
            (lambda c, s: c[14].update(scope={"outside": [5]}), "does not cover"),
            (lambda c, s: s[K]["receipt"]["rule"]["map"].update({first(s): "a + 7"}), "at the map image"),
        ]:
            self.refuse(K, "map-s", mutate, expect)

    def test_point_fidelity_mutants(self):
        for K in (4, 7, 8):  # F7-nonempty-2 (p = 2), F7m-real-q (char 0), F7m-nonempty (outside [2])
            E.build(K, E.classify(K, self.claims, self.sup), self.claims, self.sup, CAMPAIGN, self.enc)
        pt = lambda s, k: s[k]["receipt"]["certificate"]["point"]
        for K, mutate, expect in [
            (4, lambda c, s: pt(s, 4).update(x4="0"), "at the point"),
            (4, lambda c, s: s[4]["receipt"]["certificate"].update(characteristic=3), "receipt certificate"),
            (4, lambda c, s: c[4].update(scope={"characteristic": 3}), "receipt certificate"),
            (4, lambda c, s: pt(s, 4).pop("x4"), "point variables"),
            (8, lambda c, s: c[8].update(scope={"outside": []}), "not a unit at the point in scope"),
            (8, lambda c, s: pt(s, 8).update(y5="2"), "at the point"),
            (8, lambda c, s: s[8]["receipt"]["certificate"].update(characteristic=2), "receipt certificate"),
            (7, lambda c, s: pt(s, 7).update(x5="1"), "at the point"),
            (8, lambda c, s: c[8].update(kind="EMPTY"), "deferred (reprioritised"),
        ]:
            if expect == "deferred (reprioritised":
                c2, s2 = copy.deepcopy(self.claims), copy.deepcopy(self.sup)
                mutate(c2, s2)
                with self.assertRaises(E.Refuse) as cm:
                    E.classify(K, c2, s2)
                self.assertIn(expect, str(cm.exception))
            else:
                self.refuse(K, None, mutate, expect)

    def test_bridge_and_source_fidelity_mutants(self):
        E.build(5, "bridge", self.claims, self.sup, CAMPAIGN, self.enc)
        E.build(12, "source", self.claims, self.sup, CAMPAIGN, self.enc)
        for K, mutate, expect in [
            (5, lambda c, s: c[4].update(scope={"characteristic": 3}), "bridge premise differs"),
            (5, lambda c, s: c[4]["system"]["nonzero"].pop(), "bridge premise differs"),
            (5, lambda c, s: s[5]["receipt"]["rule"].update(map={}), "unexpected fields"),
            (5, lambda c, s: s[4]["receipt"]["certificate"]["point"].update(x4="0"), "at the point"),
            (12, lambda c, s: c[12]["system"].update(equations=["2*a**2 + a + 1"]), "not monic"),
            (12, lambda c, s: c[12]["system"].update(nonzero=["a"]), "not one equation"),
            (12, lambda c, s: s[12]["receipt"]["certificate"].update(characteristic=3), "receipt certificate"),
            (12, lambda c, s: c[12].update(scope={"characteristic": 9}), "not prime"),
            (12, lambda c, s: s[12]["receipt"]["certificate"].update(type="other"), "no emitter class"),
        ]:
            if expect == "no emitter class":
                c2, s2 = copy.deepcopy(self.claims), copy.deepcopy(self.sup)
                mutate(c2, s2)
                with self.assertRaises(E.Refuse) as cm:
                    E.classify(K, c2, s2)
                self.assertIn(expect, str(cm.exception))
            else:
                self.refuse(K, None, mutate, expect)


if __name__ == "__main__":
    unittest.main()
