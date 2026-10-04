"""Generate the §3.6a shadow-slice Lean files from the reach-slice inputs (glue only).

usage: python tools/gen-shadow-claims.py
Each claim is restated as a Mathlib theorem whose scope is a `ringChar` hypothesis, proved by
`linear_combination` with denominators cleared, or by `decide` over `ZMod p`.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "binding/GPBinding/Shadow"
GENERATED = ("A08b", "A08c", "X125", "X15", "A04A05", "FanoC1", "FanoF2")
HEADER = "import GPBinding.Shadow.Common\n\nnamespace GPBinding.Shadow\nopen GPBinding.Shadow\n\n"


def lean(text):
    return text.replace("^", " ^ ")


def write(name, body):
    (OUT / f"{name}.lean").write_text(HEADER + body + "\nend GPBinding.Shadow\n", encoding="utf-8")


def fano():
    c1 = json.loads((ROOT / "corpus/must/GP-X413.json").read_text())["inputs"]
    w = json.loads((ROOT / "corpus/must/GP-X415.json").read_text())["inputs"]
    vs = c1["variables"]
    hyps = " → ".join(f"{lean(g)} = 0" for g in c1["generators"])
    names = [f"h{i}" for i in range(len(c1["generators"]))]
    # Twice the C1 cofactors: integer coefficients, so `linear_combination` proves 2 = 0.
    import sympy as sp
    syms = sp.symbols(" ".join(vs))
    local = dict(zip(vs, syms))
    doubled = [str(sp.expand(2 * sp.sympify(q.replace("^", "**"), locals=local))).replace("**", "^")
               for q in c1["cofactors"]]
    combo = " + ".join(f"({lean(q)}) * {h}" for q, h in zip(doubled, names))
    write("FanoC1", f"""/-- GP-FANO-C1: the Fano incidence system is empty in every field of characteristic ≠ 2.
Guards are dropped: emptiness without them is the stronger statement. -/
theorem fano_c1 (K : Type*) [Field K] (hK : ringChar K ≠ 2) ({' '.join(vs)} : K) :
    {hyps} → False := by
  intro {' '.join(names)}
  have hz : ((2 : ℕ) : K) = 0 := by push_cast; linear_combination {combo}
  exact cast_prime_ne_zero Nat.prime_two hK hz
""")
    point = " ".join(w["point"][v] for v in vs)
    eqs = " ∧ ".join(f"{lean(g)} = 0" for g in w["generators"])
    guards = " ∧ ".join(f"{lean(g)} ≠ 0" for g in w["guards"])
    write("FanoF2", f"""/-- GP-FANO-F2: the F_2 witness satisfies every incidence and no guard vanishes. -/
theorem fano_f2 : ∃ {' '.join(vs)} : ZMod 2, ({eqs}) ∧ ({guards}) :=
  ⟨{', '.join(w['point'][v] for v in vs)}, by decide⟩
""")


def fixed():
    write("A08b", """/-- GP-A08b: `2x` and `1 - 2x` have no common zero in any field. -/
theorem a08b (K : Type*) [Field K] (x : K) : 2 * x = 0 → 1 - 2 * x = 0 → False := by
  intro h1 h2
  have h : (1 : K) = 0 := by linear_combination h1 + h2
  exact one_ne_zero h
""")
    write("A08c", """/-- GP-A08c: `2x - 1` has a zero in every field of characteristic ≠ 2. -/
theorem a08c (K : Type*) [Field K] (hK : ringChar K ≠ 2) : ∃ x : K, 2 * x - 1 = 0 := by
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast cast_prime_ne_zero Nat.prime_two hK
  exact ⟨2⁻¹, by rw [mul_inv_cancel₀ h2, sub_self]⟩
""")
    write("X125", """/-- GP-X125: the unit certificate holds in every field of characteristic outside {2, 23}. -/
theorem x125 (K : Type*) [Field K] (h2 : ringChar K ≠ 2) (h23 : ringChar K ≠ 23) (x y : K) :
    y ^ 2 - x ^ 3 + x - 1 = 0 → 3 * x ^ 2 - 1 = 0 → 2 * y = 0 → False := by
  intro e1 e2 e3
  have h46 : ((2 : ℕ) : K) * ((23 : ℕ) : K) = 0 := by
    push_cast
    linear_combination (-(36 * x + 54)) * e1 + (8 - 12 * x ^ 2 - 18 * x) * e2 + ((18 * x + 27) * y) * e3
  exact mul_ne_zero (cast_prime_ne_zero Nat.prime_two h2)
    (cast_prime_ne_zero (by norm_num) h23) h46

/-- GP-X126 refusal: in characteristic 23 the system has the point (13, 0). -/
theorem x126_refusal : ∃ x y : ZMod 23, y ^ 2 - x ^ 3 + x - 1 = 0 ∧ 3 * x ^ 2 - 1 = 0 ∧ 2 * y = 0 :=
  ⟨13, 0, by decide⟩
""")
    write("X15", """/-- GP-X15: in characteristic 2, `y^2 + 1 = 0·(x+1) + (y+1)·(y+1)` (the ideal-membership
identity), the cross term `2y` vanishing. -/
theorem x15 (K : Type*) [CommRing K] [CharP K 2] (x y : K) :
    y ^ 2 + 1 = 0 * (x + 1) + (y + 1) * (y + 1) := by
  rw [zero_mul, zero_add, ← sq, add_pow_char, one_pow]
""")
    write("A04A05", """/-- GP-A04, positive side at p = 3: outside characteristic 3, `3x = 0` forces `x = 0`. -/
theorem a04_reach (K : Type*) [Field K] (hK : ringChar K ≠ 3) (x : K) : 3 * x = 0 → x = 0 := by
  intro h
  have h3 : ((3 : ℕ) : K) ≠ 0 := cast_prime_ne_zero Nat.prime_three hK
  push_cast at h3
  exact (mul_eq_zero.mp h).resolve_left h3

/-- GP-A04 refusal at p = 3: in characteristic 3, `3x = 0` does not force `x = 0`. -/
theorem a04_refusal : ∃ x : ZMod 3, 3 * x = 0 ∧ x ≠ 0 := ⟨1, by decide⟩

/-- GP-A05 refusal: Lean elaborates `3/8` in characteristic 2 as `3 * 8⁻¹ = 3 * 0⁻¹`, the junk
value 0, so the "reduced" identity silently becomes `d2 = h2`; it typechecks, not refuses. -/
theorem a05_junk : (3 : ZMod 2) * (8 : ZMod 2)⁻¹ = 0 := by
  have h8 : (8 : ZMod 2) = 0 := by decide
  rw [h8, ZMod.inv_zero, mul_zero]
""")


if __name__ == "__main__":
    import sys
    if len(sys.argv) == 3 and sys.argv[1] == "--out":
        OUT = Path(sys.argv[2])
    OUT.mkdir(parents=True, exist_ok=True)
    fixed()
    fano()
    print(sorted(p.name for p in OUT.glob("*.lean")))
