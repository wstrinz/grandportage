"""Build the 3-step map route of GP-CLI.md for a point over F_p[a]/(m)."""
import json, sys
import sympy as sp
from qpoints_lib import enc_of, GP
a = sp.Symbol("a")
D = GP + "campaigns/3p-matroids/"

def mpoly(m): return sum(c * a**i for i, c in enumerate(m))

def build(job, guard_style="bezout"):
    fp = json.load(open("fpoints.json"))[job]
    name, p, m = job.split(":")[0], fp["p"], fp["m"]
    enc = enc_of(name); M = mpoly(m)
    tag = (f"F{p}^{len(m)-1}" if len(m) > 2 else f"F{p}") if p else "Qw"
    src = {"variables": ["a"], "equations": [str(sp.expand(M))], "nonzero": []}
    srcfile = D + f"systems/{tag}.json"
    json.dump(src, open(srcfile, "w", newline="\n"), indent=1)
    dom = dict(modulus=p) if p else dict(domain="QQ")
    raw = {v: sp.Poly(sp.sympify(s.replace("^", "**")), a, **dom) for v, s in fp["point"].items()}
    if not p:  # clear denominators point by point (homogeneous coordinates)
        import math
        for e in {v[1:] for v in raw}:
            L = math.lcm(*[int(sp.fraction(c)[1]) for v in raw if v[1:] == e for c in raw[v].all_coeffs()])
            for v in raw:
                if v[1:] == e: raw[v] = raw[v] * L
    mp = {v: str(P.as_expr()) for v, P in raw.items()}
    syms = sp.symbols(enc["variables"]); sub = {s: sp.sympify(mp[str(s)]) for s in syms}
    MP = sp.Poly(M, a, **dom)
    def comp(s): return sp.Poly(sp.sympify(s, locals={str(x): x for x in syms}).subs(sub), a, **dom)
    eqc = []
    for e in enc["equations"]:
        q, r = comp(e).div(MP); assert r.is_zero, (e, r)
        eqc.append({"type": "ideal", "cofactors": [str(q.as_expr())], "m": 1, "k": 0, **({"characteristic": p} if p else {})})
    gc = []
    for g in enc["nonzero"]:
        G = comp(g).rem(MP); assert not G.is_zero
        s = G.invert(MP) if MP.degree() > 0 else G
        t = (sp.Poly(1, a, **dom) - s * comp(g)).div(MP)[0]
        gc.append({"type": "ideal", "cofactors": [str(t.as_expr()), str(s.as_expr())], "m": 0, "k": 0, **({"characteristic": p} if p else {})})
    R = D + "receipts/"
    json.dump({"certificate": {"type": "proper_coefficient", "monomial": "a", **({"characteristic": p} if p else {})}},
              open(R + f"{tag}-proper.json", "w", newline="\n"), indent=1)
    json.dump({"rule": {"type": "map", "map": mp, "eq_certificates": eqc, "guard_certificates": gc},
               "premises": [f"src-{tag}"]}, open(R + f"{name}-map-{tag}.json", "w", newline="\n"), indent=1)
    import re
    dens = sorted({int(d) for c in gc + eqc for q in c["cofactors"] for d in re.findall(r"/(\d+)", q)})
    print("denominators", dens, [sp.factorint(d) for d in dens])
    print(job, "->", srcfile, f"{name}-map-{tag}.json", "eqs", len(eqc), "guards", len(gc))

if __name__ == "__main__":
    for j in sys.argv[1:]: build(j)
