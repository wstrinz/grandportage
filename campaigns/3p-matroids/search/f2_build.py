"""Turn search/f2-plan.json into receipts (receipts/f2/) and a gp command list (untrusted).

Per matroid M with a Q point of bad primes S:
  M-q      NONEMPTY --outside S         point over Q (integer coordinates)
  M-p<p>   NONEMPTY --char p            point over F_p                   (p in S)
  M-x<p>   NOT_IN_IDEAL 1 --char p      map from src-<tag> over F_p[a]/(m) (p in S)
Extra rows (EMPTY certificates, char-0 maps) come from search/f2-extra.json when present.

usage: python f2_build.py [names...] > commands.txt
"""
import json
import math
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent
sys.path.insert(0, str(HERE))
from f2 import encoder, mat_of  # noqa: E402

RDIR = CAMPAIGN / "receipts" / "f2"
a = sp.Symbol("a")
# source systems already held (F1) or added in F2: tag -> (claim label, modulus, characteristic)
SRC = {"F2^2": "src-F2^2", "F2^4": "src-F2^4", "F3^2": "src-F3^2", "F5^2": "src-F5^2", "Qw": "src-Qw"}


def tag_of(p, m):
    if p == 0:
        return "Qw" if tuple(m) == (1, 1, 1) else "Q" + "_".join(map(str, m))
    return f"F{p}^{len(m) - 1}"


def dom(p):
    return {"modulus": p} if p else {"domain": "QQ"}


def charkey(p):
    return {"characteristic": p} if p else {}


def write(name, obj):
    RDIR.mkdir(parents=True, exist_ok=True)
    (RDIR / name).write_bytes((json.dumps(obj, indent=1) + "\n").encode("utf-8"))
    return f"receipts/f2/{name}"


def parse_el(s, p):
    return sp.Poly(sp.sympify(s.replace("^", "**"), locals={"a": a}), a, **dom(p))


def src_rows(tag, p, m):
    """Claim and hold NOT_IN_IDEAL(1) at p on {m(a) = 0} by proper_coefficient, once per tag."""
    M = sum(c * a ** i for i, c in enumerate(m))
    sysfile = CAMPAIGN / "systems" / f"{tag}.json"
    if not sysfile.exists():
        sysfile.write_bytes((json.dumps({"variables": ["a"], "equations": [str(sp.expand(M))], "nonzero": []},
                                        indent=1) + "\n").encode("utf-8"))
    k = len(m) - 1  # the leading coefficient is 1: a unit in every characteristic
    mono = next(f"a^{i}" if i > 1 else "a" for i in range(1, len(m)) if m[i] % p) if p else f"a^{k}"
    r = write(f"{tag}-proper.json", {"certificate": {"type": "proper_coefficient", "monomial": mono, **charkey(p)}})
    scope = f"--char {p}" if p else '--outside ""'
    return [f"claim src-{tag} --system systems/{tag}.json --kind NOT_IN_IDEAL --target 1 {scope}",
            f"submit src-{tag} {r}"]


def map_receipt(name, enc, fp, write_file=True):
    p, m = fp["p"], fp["m"]
    tag = tag_of(p, m)
    MP = sp.Poly(sum(c * a ** i for i, c in enumerate(m)), a, **dom(p))
    mp = {v: parse_el(s, p) for v, s in fp["point"].items()}
    if not p:  # clear denominators point by point (homogeneous coordinates)
        for e in {v[1:] for v in mp}:
            L = math.lcm(*[int(sp.fraction(c)[1]) for v in mp if v[1:] == e for c in mp[v].all_coeffs()])
            for v in mp:
                if v[1:] == e:
                    mp[v] = mp[v] * L
    syms = sp.symbols(enc["variables"])
    loc = {str(x): x for x in syms}
    sub = {x: mp[str(x)].as_expr() for x in syms}

    def comp(s):
        return sp.Poly(sp.expand(sp.sympify(s, locals=loc).subs(sub)), a, **dom(p))

    eqc, gc = [], []
    for e in enc["equations"]:
        q, r = comp(e).div(MP)
        assert r.is_zero, (name, e)
        eqc.append({"type": "ideal", "cofactors": [str(q.as_expr())], "m": 1, "k": 0, **charkey(p)})
    for g in enc["nonzero"]:
        G = comp(g).rem(MP)
        assert not G.is_zero, (name, g)
        s = G.invert(MP)
        t = (sp.Poly(1, a, **dom(p)) - s * comp(g)).div(MP)[0]
        gc.append({"type": "ideal", "cofactors": [str(t.as_expr()), str(s.as_expr())], "m": 0, "k": 0,
                   **charkey(p)})
    rule = {"type": "map", "map": {v: str(P.as_expr()) for v, P in mp.items()},
            "eq_certificates": eqc, "guard_certificates": gc}
    receipt = {"rule": rule, "premises": [f"src-{tag}"]}
    if not write_file:
        return receipt, tag
    return write(f"{name}-map-{tag}.json", receipt), tag


def rows_for(name, entry, held_src):
    enc = encoder.encode(mat_of(name))
    assert enc["digest"] == entry["digest"], name
    out = []
    q = entry.get("q")
    if q:
        S = ",".join(map(str, q["bad_primes"]))
        r = write(f"{name}-point-q.json", {"certificate": {"type": "point", "point": q["point"]}})
        out += [f'claim {name}-q --matroid {name} --kind NONEMPTY --outside "{S}"', f"submit {name}-q {r}"]
    alg = entry.get("alg")
    if alg:
        r, tag = map_receipt(name, enc, {"p": 0, "m": alg["m"], "point": alg["point"]})
        if tag not in held_src:
            out += src_rows(tag, 0, alg["m"])
            held_src.add(tag)
        S = ",".join(map(str, alg["bad_primes"]))
        out += [f'claim {name}-a --matroid {name} --kind NOT_IN_IDEAL --target 1 --outside "{S}"',
                f"submit {name}-a {r}"]
    for e in entry.get("empty", []):
        cert = {"type": "ideal", "cofactors": e["cofactors"], "m": 0, "k": e["k"], "guards": e["guards"]}
        if e["char"]:
            p = e["char"]
            r = write(f"{name}-empty-mod{p}.json", {"certificate": dict(cert, characteristic=p)})
            out += [f"claim {name}-e{p} --matroid {name} --kind EMPTY --char {p}", f"submit {name}-e{p} {r}"]
        else:
            S = ",".join(map(str, e["denominator_primes"]))
            r = write(f"{name}-empty-q.json", {"certificate": cert})
            out += [f'claim {name}-e --matroid {name} --kind EMPTY --outside "{S}"', f"submit {name}-e {r}"]
    for ps, fp in entry.get("fp", {}).items():
        p = int(ps)
        if fp is None:
            out.append(f"# OPEN {name} at {p}: no point found")
            continue
        if len(fp["m"]) == 1:
            pt = {v: str(int(parse_el(s, p).as_expr()) % p if s != "0" else 0) for v, s in fp["point"].items()}
            r = write(f"{name}-point-f{p}.json", {"certificate": {"type": "point", "point": pt, "characteristic": p}})
            out += [f"claim {name}-p{p} --matroid {name} --kind NONEMPTY --char {p}", f"submit {name}-p{p} {r}"]
        else:
            r, tag = map_receipt(name, enc, fp)
            if tag not in held_src:
                out += src_rows(tag, p, fp["m"])
                held_src.add(tag)
            out += [f"claim {name}-x{p} --matroid {name} --kind NOT_IN_IDEAL --target 1 --char {p}",
                    f"submit {name}-x{p} {r}"]
    return out


def main():
    plan = json.loads((HERE / "f2-plan.json").read_text(encoding="utf-8"))
    names = sys.argv[1:] or list(plan)
    ledger = (CAMPAIGN / "ledger.jsonl").read_text(encoding="utf-8").splitlines()
    filed = {json.loads(l).get("label", "") for l in ledger if l.strip()}
    held_src = set(SRC) | {lab[4:] for lab in filed if lab.startswith("src-")}
    for n in names:
        print("\n".join(rows_for(n, plan[n], held_src)))


if __name__ == "__main__":
    main()
