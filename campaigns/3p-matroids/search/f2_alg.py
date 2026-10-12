"""Entries with no Q point: decide Q-emptiness (Singular), else search a point over a quadratic
number field Q[a]/(m) and record the char-0 map route (untrusted; GP replays everything).

usage: python f2_alg.py [names...]   (default: plan entries with q = null and no "empty"/"alg")
Writes entry["alg"] = {"m", "point", "bad_primes"} and field points at those primes, or hands
the entry to f2_empty.py when the system is empty over Q.
"""
import json
import re
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from f2 import encoder, mat_of, fpoint, attempt, PLAN  # noqa: E402
from realize import F  # noqa: E402
from sat import sat_is_one  # noqa: E402

# monic moduli over Q, low degree first: w, i, sqrt(-2), sqrt(2), golden ratio, sqrt(3), sqrt(-7) root
QFIELDS = [(1, 1, 1), (1, 0, 1), (2, 0, 1), (-2, 0, 1), (-1, -1, 1), (-3, 0, 1), (2, -1, 1), (-5, 0, 1)]
a = sp.Symbol("a")


def alg_point(mat, enc, tries=3000):
    for m in QFIELDS:
        K = F(0, m)
        for _ in range(tries):
            co = attempt(K, mat, enc, R=2)
            if co:
                return m, {v: K.tostr(x) for v, x in co.items()}
    return None, None


def route_primes(enc, m, point):
    """Primes in the denominators of the map route's certificates (what the reach will exclude)."""
    sys.path.insert(0, str(HERE))
    from f2_build import map_receipt  # noqa: E402
    path, _ = map_receipt("probe", enc, {"p": 0, "m": list(m), "point": point}, write_file=False)
    text = json.dumps(path)
    dens = {int(d) for d in re.findall(r"/(\d+)", text)}
    return sorted({p for d in dens for p in sp.factorint(d)})


def main():
    plan = json.loads(PLAN.read_text(encoding="utf-8"))
    names = sys.argv[1:] or [n for n, e in plan.items() if e["q"] is None and "empty" not in e and "alg" not in e]
    for name in names:
        mat = mat_of(name)
        enc = encoder.encode(mat)
        if sat_is_one(enc, list(range(len(enc["nonzero"]))), 0):
            print(name, "EMPTY over Q: run f2_empty.py", flush=True)
            continue
        m, point = alg_point(mat, enc)
        entry = plan[name]
        if m is None:
            print(name, "NONEMPTY over Qbar but no quadratic point found: manual", flush=True)
            entry["alg"] = None
        else:
            S = route_primes(enc, m, point)
            entry["alg"] = {"m": list(m), "point": point, "bad_primes": S}
            for p in S:
                entry["fp"][str(p)] = fpoint(mat, enc, p)
            print(name, "point over Q[a]/", m, "route excludes", S,
                  {p: (v and len(v["m"]) - 1 or v) for p, v in entry["fp"].items()}, flush=True)
        PLAN.write_bytes((json.dumps(plan, indent=1) + "\n").encode("utf-8"))


if __name__ == "__main__":
    main()
