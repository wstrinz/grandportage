"""DK V4 slice machinery (docs/DK-V4-DESIGN.md) on a small synthetic statement, without DK's data.

Four points and four lines, every line with 2 points and every point on 2 lines, with the point
action s1 = (0 1)(2 3), s2 = id, s3 = s1. Members fall into two classes: the 4-cycle 0-2-1-3 and two
doubled edges. With "every line is fixed by s1" (an action atom) only the doubled edges remain.

Controls: the full listing is held at its count; must-refuse traps: a missed model, a representative
whose action is not valid, a duplicate class, a non-centralising relabelling, a wrong count; and the
catalog form holds only with its premise visible in the statement.
"""
import itertools
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = ".exe" if os.name == "nt" else ""
CENSUS = ROOT / "census"
RUNNER = CENSUS / f".lake/build/bin/gp_census{EXE}"
TOOLCHAIN = Path.home() / ".elan/toolchains" / (CENSUS / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")
CADICAL = TOOLCHAIN / f"bin/cadical{EXE}"

PTS = 4
N = 8
S1 = [1, 0, 3, 2]
A0 = [S1, [0, 1, 2, 3], S1]
REG = {"and": [
    {"forall": "L", "body": {"or": [{"not": {"color": ["L", 1]}}, {"and": [
        {"atLeast": 2, "var": "p", "body": {"adj": ["p", "L"]}},
        {"not": {"atLeast": 3, "var": "p", "body": {"adj": ["p", "L"]}}}]}]}},
    {"forall": "p", "body": {"or": [{"not": {"color": ["p", 0]}}, {"and": [
        {"atLeast": 2, "var": "L", "body": {"adj": ["p", "L"]}},
        {"not": {"atLeast": 3, "var": "L", "body": {"adj": ["p", "L"]}}}]}]}}]}
FIXED = {"and": [REG, {"forall": "L", "body": {"or": [{"not": {"color": ["L", 1]}}, {"act": [0, "L", "L"]}]}}]}


def build():
    subprocess.run([str(TOOLCHAIN / f"bin/lake{EXE}"), "build", "gp_census"], cwd=CENSUS, check=True,
                   capture_output=True)


def members(pred_fixed):
    """Every labelled member, by brute force over incidences and line actions (the test's proposer)."""
    out = []
    for bits in itertools.product((0, 1), repeat=PTS * PTS):
        lines = [frozenset(p for p in range(PTS) if bits[p * PTS + L]) for L in range(PTS)]
        if any(len(l) != 2 for l in lines) or any(sum(p in l for l in lines) != 2 for p in range(PTS)):
            continue
        acts = []
        for g in (0, 1, 2):
            ok = [lp for lp in itertools.permutations(range(PTS))
                  if all(frozenset(A0[g][p] for p in lines[L]) == lines[lp[L]] for L in range(PTS))]
            acts.append(ok)
        if not all(acts):
            continue
        combos = [c for c in itertools.product(*acts)] if pred_fixed else [tuple(a[0] for a in acts)]
        for c in combos:
            if pred_fixed and not all(c[0][L] == L for L in range(PTS)):
                continue
            out.append((lines, c))
            break
    return out


def witness(lines):
    return {"edges": sorted([p, PTS + L] for L, l in enumerate(lines) for p in l), "colors": [0] * PTS + [1] * PTS}


def action(c):
    return [list(A0[g]) + [PTS + j for j in c[g]] for g in range(3)]


def iso(a, b):
    return any(sorted(frozenset(pp[p] for p in l) for l in a) == sorted(b)
               for pp in itertools.permutations(range(PTS)))


def sorted_cols(lines):
    cols = [tuple(int(p in l) for p in range(PTS)) for l in lines]
    return all(cols[i] <= cols[i + 1] for i in range(PTS - 1))


SWAPS = [[*range(PTS), *[PTS + j for j in (lambda a: (a.__setitem__(i, i + 1), a.__setitem__(i + 1, i), a)[2])(list(range(PTS)))]]
         for i in range(PTS - 1)]
CENTRAL = [[1, 0, 3, 2, *range(PTS, N)], [2, 3, 0, 1, *range(PTS, N)]]   # commute with s1


def stmt(pred, count, catalog=None):
    s = {"colors": 2, "predicate": pred, "kind": "V4_COUNT", "points": PTS, "action": A0, "count": count}
    if catalog is not None:
        s["assuming_complete"] = catalog
    return s


class CensusV4(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        build()
        cls.tmp = Path(tempfile.mkdtemp())

    def listing(self, pred_fixed, labels, drop_model=False):
        ms = [(l, c) for l, c in members(pred_fixed) if sorted_cols(l)]
        reps = []
        for l, c in ms:
            if not any(iso(l, r[0]) for r in reps):
                reps.append((l, c))
        models = [m for m in ms]
        if drop_model:
            models = models[1:]
        return models, reps

    def run_claims(self, claims):
        path = self.tmp / "ledger.json"
        path.write_text(json.dumps({"claims": claims}), encoding="utf-8")
        out = subprocess.run([str(RUNNER), "run", str(path)], capture_output=True, text=True, check=True)
        return {c["key"]: c for c in json.loads(out.stdout)["claims"]}

    def listed(self, pred, count, models, reps, labels, name):
        claim = stmt(pred, count)
        cert = {"type": "v4listed", "n": N, "models": [witness(l) for l, _ in models],
                "reps": [{"witness": witness(l), "action": action(c)} for l, c in reps], "labels": labels}
        (self.tmp / f"{name}-claim.json").write_text(json.dumps(claim), encoding="utf-8")
        (self.tmp / f"{name}-cert.json").write_text(json.dumps(cert), encoding="utf-8")
        cnf = subprocess.run([str(RUNNER), "v4listcnf", str(self.tmp / f"{name}-claim.json"),
                              str(self.tmp / f"{name}-cert.json")], capture_output=True, text=True, check=True).stdout
        (self.tmp / f"{name}.cnf").write_text(cnf, encoding="utf-8", newline="\n")
        r = subprocess.run([str(CADICAL), "--lrat=true", "--binary=false", "-q", f"{name}.cnf", f"{name}.lrat"],
                           cwd=self.tmp, capture_output=True, text=True)
        cert["proof"] = (self.tmp / f"{name}.lrat").read_text(encoding="utf-8") if r.returncode == 20 else ""
        return r.returncode, dict(claim, key=1, scope=[N], certificate=cert)

    def test_listing_held(self):
        models, reps = self.listing(False, SWAPS + CENTRAL)
        self.assertEqual(len(reps), 2)
        rc, claim = self.listed(REG, 2, models, reps, SWAPS + CENTRAL, "reg")
        self.assertEqual(rc, 20)
        self.assertTrue(self.run_claims([claim])[1]["held"])

    def test_action_atom(self):
        models, reps = self.listing(True, SWAPS)
        self.assertEqual(len(reps), 1)
        rc, claim = self.listed(FIXED, 1, models, reps, SWAPS, "fixed")
        self.assertEqual(rc, 20)
        self.assertTrue(self.run_claims([claim])[1]["held"])

    def test_missed_model_is_not_refutable(self):
        models, reps = self.listing(False, SWAPS)
        rc, claim = self.listed(REG, 2, models[1:], reps, SWAPS, "missed")
        self.assertEqual(rc, 10)
        self.assertFalse(self.run_claims([claim])[1]["held"])

    def test_traps(self):
        models, reps = self.listing(False, SWAPS)
        rc, good = self.listed(REG, 2, models, reps, SWAPS, "traps")
        self.assertEqual(rc, 20)
        cert = good["certificate"]
        bad_action = json.loads(json.dumps(good))
        bad_action["certificate"]["reps"][0]["action"][0][PTS] = PTS + 3    # not an automorphism
        dup = json.loads(json.dumps(good))
        dup["count"] = 3
        dup["certificate"]["reps"].append(cert["reps"][0])
        wrong_count = dict(good, count=3)
        noncentral = json.loads(json.dumps(good))
        noncentral["certificate"]["labels"] = SWAPS + [[1, 2, 0, 3, *range(PTS, N)]]
        got = self.run_claims([dict(c, key=k) for k, c in enumerate([good, bad_action, dup, wrong_count, noncentral], 1)])
        self.assertEqual([got[k]["held"] for k in range(1, 6)], [True, False, False, False, False])

    def test_catalog_premise(self):
        _, reps = self.listing(False, SWAPS)
        cat = [witness(l) for l, _ in reps]
        claim = dict(stmt(REG, 2, catalog=cat), key=1, scope=[N],
                     certificate={"type": "v4catalog", "n": N,
                                  "reps": [{"witness": witness(l), "action": action(c)} for l, c in reps]})
        short = dict(stmt(REG, 1, catalog=cat[:1]), key=2, scope=[N],
                     certificate={"type": "v4catalog", "n": N,
                                  "reps": [{"witness": witness(l), "action": action(c)} for l, c in reps[:1]]})
        got = self.run_claims([claim, short])
        # Both hold: each is "COUNT = m IF the catalog is complete". The short catalog's premise is
        # false, which is exactly why the premise stays visible and OPEN in the statement.
        self.assertTrue(got[1]["held"])
        self.assertTrue(got[2]["held"])


if __name__ == "__main__":
    unittest.main()
