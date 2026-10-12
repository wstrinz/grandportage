"""For plan entries with no Q point: a Q emptiness certificate (Singular, untrusted), then at each
denominator prime a field point, or else a mod-p emptiness certificate.  Updates f2-plan.json.

usage: python f2_empty.py [names...]   (default: plan entries with q = null and no "empty")
"""
import json
import re
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from f2 import encoder, mat_of, fpoint, PLAN  # noqa: E402
from sat import minimize, cert  # noqa: E402


def empty_cert(enc, char):
    S = minimize(enc, char)
    k, cof = cert(enc, S, char)
    dens = {int(d) for c in cof for d in re.findall(r"/(\d+)", c)}
    primes = sorted({p for d in dens for p in sp.factorint(d)})
    return {"char": char, "guards": S, "k": k, "cofactors": cof, "denominator_primes": primes}


def main():
    plan = json.loads(PLAN.read_text(encoding="utf-8"))
    names = sys.argv[1:] or [n for n, e in plan.items() if e["q"] is None and "empty" not in e and "alg" not in e]
    # entries with a Q point but no field point at some bad prime: try EMPTY mod p there
    for name, entry in plan.items():
        if entry["q"] is None:
            continue
        for ps in [ps for ps, fp in entry["fp"].items() if fp is None]:
            enc = encoder.encode(mat_of(name))
            entry.setdefault("empty", []).append(empty_cert(enc, int(ps)))
            entry["fp"].pop(ps)
            print(name, "EMPTY mod", ps, "guards", entry["empty"][-1]["guards"], flush=True)
            PLAN.write_bytes((json.dumps(plan, indent=1) + "\n").encode("utf-8"))
    for name in names:
        mat = mat_of(name)
        enc = encoder.encode(mat)
        e0 = empty_cert(enc, 0)
        entry = plan[name]
        entry["empty"] = [e0]
        for p in e0["denominator_primes"]:
            fp = fpoint(mat, enc, p)
            entry["fp"][str(p)] = fp
            if fp is None:
                entry["fp"].pop(str(p))
                entry["empty"].append(empty_cert(enc, p))
        print(name, "EMPTY outside", e0["denominator_primes"], "guards", e0["guards"],
              "| at those primes:", {p: ("point" if str(p) in entry["fp"] else "EMPTY mod p") for p in e0["denominator_primes"]},
              flush=True)
        PLAN.write_bytes((json.dumps(plan, indent=1) + "\n").encode("utf-8"))


if __name__ == "__main__":
    main()
