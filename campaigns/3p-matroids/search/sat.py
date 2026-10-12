"""Find a small guard subset S with 1 in sat(I, prod S) (Singular), then k and cofactors."""
import json, sys
from cas import singular, lift
from qpoints_lib import enc_of

def sat_is_one(enc, S, char):
    s = f"LIB \"elim.lib\";\nring R = {char}, ({','.join(enc['variables'])}), dp;\noption(redSB);\n"
    s += "ideal I = " + ", ".join(f"({e})" for e in enc["equations"]) + ";\n"
    s += "ideal J = std(I);\n"
    for i in S:  # one guard at a time: far cheaper than saturating by the product
        s += f"if (J[1] != 1) {{ J = sat(J, {enc['nonzero'][i]})[1]; }}\n"
    s += "print(J);\nquit;\n"
    out = singular(s).strip()
    return out.replace("_[1]=", "").strip() == "1"

def minimize(enc, char=0):
    S = list(range(len(enc["nonzero"])))
    assert sat_is_one(enc, S, char), "not empty"
    # greedy removal, trying higher-degree guards first
    for i in sorted(S, key=lambda i: -len(enc["nonzero"][i])):
        T = [j for j in S if j != i]
        if sat_is_one(enc, T, char): S = T
    return S

def cert(enc, S, char=0, kmax=8):
    g = "*".join(f"({enc['nonzero'][i]})" for i in S)
    for k in range(1, kmax + 1):
        try:
            return k, lift(enc, f"({g})^{k}", char)
        except RuntimeError:
            pass
    raise RuntimeError("k too small")

if __name__ == "__main__":
    name, char = sys.argv[1], int(sys.argv[2])
    enc = enc_of(name)
    S = minimize(enc, char); print(name, "char", char, "guards", S, [enc["nonzero"][i] for i in S])
    k, cof = cert(enc, S, char)
    import re
    dens = set()
    for c in cof:
        for d in re.findall(r"/(\d+)", c): dens.add(int(d))
    print("k", k, "denominators", sorted(dens), "cofactor chars", sum(len(c) for c in cof))
    json.dump({"guards": S, "k": k, "cofactors": cof, "char": char}, open(f"empty-{name}-{char}.json", "w"))
