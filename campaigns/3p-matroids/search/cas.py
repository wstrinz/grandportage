"""Untrusted search helpers for the 3P campaign (campaign-op; GP replays everything).

lift(enc, target, char=0) -> cofactors q_i with sum q_i*eq_i == target (Singular `lift`),
checked locally with sympy (mod char when char > 0).
"""
import json, subprocess, sys, re
import sympy as sp

SING = ["wsl", "-d", "Ubuntu", "--", "Singular", "-q", "--no-warn"]


def singular(script: str) -> str:
    r = subprocess.run(SING, input=script, capture_output=True, text=True, timeout=600)
    if r.returncode != 0 or "error" in r.stdout.lower():
        raise RuntimeError(r.stdout + r.stderr)
    return r.stdout


def ring_decl(vars_, char):
    return f"ring R = {char}, ({','.join(vars_)}), dp;\n"


def lift(enc, target, char=0, eqs=None):
    vars_ = enc["variables"]
    eqs = enc["equations"] if eqs is None else eqs
    s = ring_decl(vars_, char)
    s += "ideal I = " + ", ".join(f"({e})" for e in eqs) + ";\n"
    s += f"poly f = {target};\n"
    s += "matrix L = lift(I, f);\n"
    s += "int i; for (i = 1; i <= nrows(L); i++) { print(L[i,1]); print(\"@@\"); }\nquit;\n"
    out = singular(s)
    parts = [p.strip() for p in out.split("@@")][: len(eqs)]
    cof = [p.replace("\n", "") for p in parts]
    check(vars_, eqs, cof, target, char)
    return cof


def check(vars_, eqs, cof, target, char=0):
    syms = sp.symbols(vars_)
    loc = dict(zip(vars_, syms))
    tot = sum(sp.sympify(q, locals=loc) * sp.sympify(e, locals=loc) for q, e in zip(cof, eqs))
    diff = sp.expand(tot - sp.sympify(target, locals=loc))
    if char:
        diff = sp.Poly(diff, *syms).trunc(char) if diff != 0 else 0
        ok = diff == 0 or sp.Poly(diff, *syms).is_zero
    else:
        ok = diff == 0
    if not ok:
        raise AssertionError(f"identity fails: residual {diff}")
    return True


def in_radical_cert(enc, guards, char=0, max_k=6):
    """Find k and cofactors with sum q_i eq_i = (prod guards)^k."""
    g = "*".join(f"({enc['nonzero'][i]})" for i in guards)
    for k in range(1, max_k + 1):
        try:
            return k, lift(enc, f"({g})^{k}", char)
        except RuntimeError:
            continue
    raise RuntimeError("no k found")


if __name__ == "__main__":
    enc = json.load(open(sys.argv[1]))
    print(json.dumps(lift(enc, sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 0)))
