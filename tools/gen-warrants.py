"""Generate theorem warrants (A4) for held 3a claims, from the runner's exact canonical inputs.

usage: python tools/gen-warrants.py <candidates.json> [--out binding/GPBinding/Warrants/Generated.lean]
Candidates come from `gp_corpus_run <root> <manifest> --candidates`. Supported shape: C1 emptiness
over Q (m = 0) with integer statement coefficients; cofactor denominators are cleared by their
lcm D, and D != 0 in every field of the scope follows from an explicit prime factorization.
Other claims stay receipt-only (A4: "otherwise mint a receipt").
"""
from fractions import Fraction
import json
from math import lcm
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
SIMP = ("valueE_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, "
        "List.length_nil, Fin.prod_univ_succ, Fin.prod_univ_zero, List.getD_cons_zero, List.getD_cons_succ, "
        "List.getD_nil, Fin.val_zero, Fin.val_succ, pow_zero, pow_one, mul_one, add_zero, Rat.cast_ofNat, "
        "Rat.cast_one, Rat.cast_neg, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_zero")

TERM = re.compile(r"\(\[([0-9, ]*)\], \((-?\d+)(?:/(\d+))? : Rat\)\)")


def terms(lit):
    """Parse a sparse literal `[([e..], (n/d : Rat)), ...]`."""
    out = []
    for es, n, d in TERM.findall(lit):
        exps = [int(e) for e in es.split(",") if e.strip()]
        out.append((exps, Fraction(int(n), int(d) if d else 1)))
    return out


def var(i):
    return "x " + "(Fin.succ " * i + "0" + ")" * i


def expr(poly, scale=1):
    parts = []
    for exps, c in poly:
        c = c * scale
        assert c.denominator == 1, "scaled coefficient is not integral"
        factors = [f"{var(i)} ^ {e}" for i, e in enumerate(exps) if e]
        parts.append("(" + " * ".join([f"({c.numerator} : K.carrier)"] + factors) + ")")
    return " + ".join(parts) if parts else "0"


def mem(i):
    return "(" + "List.mem_cons_of_mem _ (" * i + "List.mem_cons_self" + ")" * i + ")"


def factor(n):
    fs, d = [], 2
    while d * d <= n:
        while n % d == 0:
            fs.append(d)
            n //= d
        d += 1
    if n > 1:
        fs.append(n)
    return fs


def theorem(c):
    name = "w_" + re.sub(r"[^A-Za-z0-9]", "_", c["case"]) + f"_{c['key']}"
    eqs = [terms(e) for e in c["eqs"]]
    guards = [terms(g) for g in c["guards"]]
    qs = [terms(q) for q in c["cert"]["cofactors"]]
    k = c["cert"]["k"]
    D = lcm(*[t[1].denominator for q in qs for t in q]) if any(qs) else 1
    lines = [f"theorem {name} :", f"    Warranted {c['stmt']}", f"      {c['scope']} := by",
             "  intro K hK x hx"]
    hyps = []
    for i in range(len(eqs)):
        lines.append(f"  have e{i} := hx.1 _ {mem(i)}")
        hyps.append(f"e{i}")
    for j in range(len(guards)):
        lines.append(f"  have g{j} := hx.2 _ {mem(j)}")
        hyps.append(f"g{j}")
    if hyps:
        lines.append(f"  simp only [{SIMP}] at {' '.join(hyps)}")
    combo = " + ".join(f"({expr(q, D)}) * e{i}" for i, q in enumerate(qs) if q) or "0"
    if D != 1:
        fs = factor(D)
        lines.append(f"  have hD : (({D} : ℕ) : K.carrier) ≠ 0 :=")
        lines.append(f"    natCast_ne_zero_of_factors hK {fs} (by norm_num) (by decide) (by decide)")
    else:
        lines.append("  have hD : ((1 : ℕ) : K.carrier) ≠ 0 := by simp")
    if k == 0 or not guards:
        lines += ["  apply hD", "  simp only [Nat.cast_ofNat, Nat.cast_one]", f"  linear_combination {combo}"]
    else:
        prod = " ".join(f"(mul_ne_zero g{j}" for j in range(len(guards) - 1)) + f" g{len(guards) - 1}" + ")" * (len(guards) - 1)
        lines += [f"  refine mul_ne_zero hD (pow_ne_zero {k} ({prod.strip()})) ?_", "  simp only [Nat.cast_ofNat, Nat.cast_one]",
                  f"  linear_combination {combo}"]
    return name, "\n".join(lines)


def eligible(c):
    cert = c["cert"]
    if c["kind"] != "EMPTY" or cert.get("type") != "ideal" or cert.get("field") != "GPProfile.Field.rat":
        return False
    if cert["m"] != 0:
        return False
    polys = [terms(p) for p in c["eqs"] + c["guards"]]
    return all(t[1].denominator == 1 for p in polys for t in p)


def main():
    src = Path(sys.argv[1])
    out = Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else \
        ROOT / "binding/GPBinding/Warrants/Generated.lean"
    cands = [c for c in json.loads(src.read_text(encoding="utf-8")) if eligible(c)]
    seen, blocks, entries = set(), [], []
    for c in cands:
        name, block = theorem(c)
        # One warrant per (statement, scope): a case filed under two labels mints one theorem.
        if name in seen or (c["stmt"], c["scope"]) in seen:
            continue
        seen.add(name)
        seen.add((c["stmt"], c["scope"]))
        blocks.append(block)
        entries.append(f'  ⟨"{name}", {c["stmt"]}, {c["scope"]}, {name}⟩')
    header = ("import GPBinding.Binder.Registry\nimport Mathlib.Tactic.LinearCombination\n"
              "import Mathlib.Tactic.NormNum.Prime\n\n"
              "/-! Generated by tools/gen-warrants.py; do not edit. Theorem warrants (A4) for held 3a claims. -/\n\n"
              "namespace GPBinding.Warrants\nopen GPProfile GPBinding.Binder MvPolynomial\n\n")
    body = "\n\n".join(blocks)
    registry = "\n\n/-- Every generated warrant, for the binder. -/\ndef registry : List Bound := [\n" + \
        ",\n".join(entries) + "]\n\nend GPBinding.Warrants\n"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(header + body + registry, encoding="utf-8")
    print(json.dumps({"candidates": len(json.loads(src.read_text(encoding="utf-8"))), "warrants": len(blocks)}))


if __name__ == "__main__":
    main()
