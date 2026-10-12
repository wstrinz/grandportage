"""F2 search driver (untrusted, campaign-op; GP replays everything).

For each catalog matroid: a Q point whose guard values have few prime factors, then at each of
those primes a point over F_p or over F_p[a]/(m).  Results go to search/f2-plan.json.

usage: python f2.py [names...]   (default: every catalog entry not isomorphic to an F1 matroid)
"""
import importlib.util
import json
import math
import os
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent
ROOT = CAMPAIGN.parents[1]
sys.path.insert(0, str(HERE))
from realize import F, check, clear_denoms_Q, bad_primes, cross, det3, to_frame, coords_of  # noqa: E402

spec = importlib.util.spec_from_file_location("encoder", ROOT / "tools/encode-matroid.py")
encoder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(encoder)

# irreducible moduli, low degree first; (1,) is the prime field
IRR = {2: [(1,), (1, 1, 1), (1, 1, 0, 1), (1, 1, 0, 0, 1)], 3: [(1,), (1, 0, 1), (1, 2, 0, 1)],
       5: [(1,), (3, 0, 1)], 7: [(1,), (1, 0, 1)], 11: [(1,), (1, 0, 1)], 13: [(1,), (2, 0, 1)]}
PLAN = HERE / os.environ.get("F2_PLAN", "f2-plan.json")


def mat_of(name):
    return json.loads((CAMPAIGN / "matroids" / f"{name}.json").read_text(encoding="utf-8"))


def place(K, mat, R=3, retries=60):
    """Place points one at a time in a random order, retrying a point that breaks a condition.

    A point on two lines through placed points is their meet; on one line, a random point of it;
    otherwise random.  After each placement every triple through the new point is checked:
    det = 0 on a line, det != 0 otherwise.  A forced point that fails restarts the attempt."""
    els = list(mat["elements"])
    random.shuffle(els)
    lines = [frozenset(L) for L in mat["lines"]]
    on_line = lambda t: any(t <= L for L in lines)
    pos = {}
    for e in els:
        cons = [L for L in lines if e in L and len([x for x in L if x in pos]) >= 2]
        for _ in range(retries):
            if len(cons) >= 2:
                ls = [cross(K, *[pos[x] for x in sorted(L) if x in pos][:2]) for L in cons[:2]]
                v = cross(K, ls[0], ls[1])
            elif cons:
                a, b = [x for x in sorted(cons[0]) if x in pos][:2]
                s, t = K.rand(R), K.rand(R)
                v = [K.add(K.mul(s, pa), K.mul(t, pb)) for pa, pb in zip(pos[a], pos[b])]
            else:
                v = [K.rand(R) for _ in range(3)]
            ok = not all(K.iszero(x) for x in v)
            placed = list(pos)
            for i in range(len(placed)):
                if not ok:
                    break
                for j in range(i + 1, len(placed)):
                    a, b = placed[i], placed[j]
                    z = K.iszero(det3(K, pos[a], pos[b], v))
                    if z != on_line(frozenset((a, b, e))):
                        ok = False
                        break
            if ok:
                pos[e] = v
                break
            if len(cons) >= 2:
                return None
        else:
            return None
    return pos


def attempt(K, mat, enc, R=3):
    pos = place(K, mat, R)
    if pos is None:
        return None
    fr = to_frame(K, pos, enc["frame"])
    if fr is None:
        return None
    co = coords_of(enc, fr)
    eqs, gs = check(K, enc, co)
    if all(K.iszero(x) for x in eqs) and not any(K.iszero(x) for x in gs):
        return co
    return None


def qpoint(mat, enc, rounds=400):
    K = F(0)
    best = None
    for t in range(rounds):
        co = attempt(K, mat, enc, R=1 + t % 4)
        if co is None:
            continue
        co = clear_denoms_Q(enc, co)
        eqs, gs = check(K, enc, co)
        assert all(K.iszero(x) for x in eqs) and not any(K.iszero(x) for x in gs)
        bp = bad_primes(gs)
        sc = (math.prod(bp), max([abs(x[0].numerator) for x in co.values()] or [0]))
        if best is None or sc < best[0]:
            best = (sc, co, bp)
            if not bp:
                break
    if best is None:
        return None
    return {"point": {v: str(x[0]) for v, x in best[1].items()}, "bad_primes": sorted(best[2])}


def fpoint(mat, enc, p, tries=1500):
    for m in IRR.get(p, [(1,)]):
        K = F(p, m)
        for _ in range(tries):
            co = attempt(K, mat, enc)
            if co:
                return {"p": p, "m": list(m), "point": {v: K.tostr(x) for v, x in co.items()}}
    return None


def main():
    cat = json.loads((CAMPAIGN / "catalog/catalog.json").read_text(encoding="utf-8"))
    names = sys.argv[1:] or [e["name"] for e in cat["entries"] if "isomorphic_to" not in e]
    plan = json.loads(PLAN.read_text(encoding="utf-8")) if PLAN.exists() else {}
    for name in names:
        random.seed(name)
        mat = mat_of(name)
        enc = encoder.encode(mat)
        q = qpoint(mat, enc)
        entry = {"digest": enc["digest"], "q": q, "fp": {}}
        for p in (q["bad_primes"] if q else []):
            entry["fp"][str(p)] = fpoint(mat, enc, p)
        plan[name] = entry
        fp = {p: (None if v is None else len(v["m"]) - 1 or 1) for p, v in entry["fp"].items()}
        print(name, "Q:", "none" if q is None else q["bad_primes"], "F_p degrees:", fp, flush=True)
        PLAN.write_bytes((json.dumps(plan, indent=1) + "\n").encode("utf-8"))


if __name__ == "__main__":
    main()
