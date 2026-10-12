import GPBinding.Binder.Explicit
import GPBinding.Matroid.Det
import GPProfile.Matroid

/-!
The Lean encoder's polynomials evaluate to determinants (ENCODING-FRAME). Each determinant is
built from constants and variables with Hex arithmetic; through `toMvPolynomial` it is the same
expression over the subring of rationals that are good in `K`, so at a point `x` its explicit
value is the determinant of the encoder's columns evaluated at `x`.
-/

noncomputable section

namespace GPBinding.Matroid
open GPProfile GPProfile.Matroid GPBinding.Binder GPBinding.Admission MvPolynomial HexMvPolyMathlib

variable {K : Type*} [Field K]

def entryK (n : ℕ) (x : Fin n → K) : Entry → K
  | .const k => (k : K)
  | .var i => if h : i < n then x ⟨i, h⟩ else 0

/-- An encoder column evaluated at a point. -/
def colK (n : ℕ) (x : Fin n → K) (e : Entry × Entry × Entry) : Fin 3 → K :=
  ![entryK n x e.1, entryK n x e.2.1, entryK n x e.2.2]

/-- The entry as a polynomial over the good rationals. -/
def entryG (n : ℕ) : Entry → MvPolynomial (Fin n) (Good K)
  | .const k => MvPolynomial.C (k : Good K)
  | .var i => if h : i < n then MvPolynomial.X ⟨i, h⟩ else 0

theorem toMv_entry (n : ℕ) (e : Entry) :
    toMvPolynomial (entryP n e) = MvPolynomial.map (Good K).subtype (entryG (K := K) n e) := by
  cases e with
  | const k => simp [entryP, entryG]
  | var i =>
    simp only [entryP, entryG]
    split <;> simp

def det3G (n : ℕ) (u v w : Entry × Entry × Entry) : MvPolynomial (Fin n) (Good K) :=
  let (a, b, c) := (entryG (K := K) n u.1, entryG (K := K) n u.2.1, entryG (K := K) n u.2.2)
  let (d, e, f) := (entryG (K := K) n v.1, entryG (K := K) n v.2.1, entryG (K := K) n v.2.2)
  let (g, h, i) := (entryG (K := K) n w.1, entryG (K := K) n w.2.1, entryG (K := K) n w.2.2)
  a * (e * i - h * f) - d * (b * i - h * c) + g * (b * f - e * c)

theorem toMv_det3P (n : ℕ) (u v w : Entry × Entry × Entry) :
    toMvPolynomial (det3P n u v w) = MvPolynomial.map (Good K).subtype (det3G (K := K) n u v w) := by
  simp only [det3P, det3G, toMvPolynomial_add, toMvPolynomial_sub, toMvPolynomial_mul, toMv_entry (K := K),
    map_add, map_sub, map_mul]

theorem eval_entryG (n : ℕ) (x : Fin n → K) (e : Entry) :
    eval₂ (castGood K) x (entryG (K := K) n e) = entryK n x e := by
  cases e with
  | const k =>
    simp only [entryG, entryK, eval₂_C]
    exact map_intCast (castGood K) k
  | var i =>
    simp only [entryG, entryK]
    split <;> simp

theorem eval_det3P (n : ℕ) (x : Fin n → K) (u v w : Entry × Entry × Entry) :
    eval x (toK (K := K) (toMvPolynomial (det3P n u v w))) = det3 (colK n x u) (colK n x v) (colK n x w) := by
  rw [toMv_det3P (K := K), toK_map, eval_map]
  simp only [det3G, eval₂_add, eval₂_sub, eval₂_mul, eval_entryG, det3, colK, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem arityOk_ofHex {n : ℕ} (d : GPProfile.P n Rat) : arityOk n (ofHex d) = true := by
  simp [arityOk, ofHex]

/-- A determinant's sparse form, evaluated explicitly, is the determinant of the columns. -/
theorem valueE_det {n : ℕ} (d : GPProfile.P n Rat) (hrt : toHexQ n (ofHex d) = some d)
    (hint : (ofHex d).all (fun t => t.2.den == 1) = true) (x : Fin n → K) :
    valueE K n (ofHex d) x = eval x (toK (K := K) (toMvPolynomial d)) := by
  have hg : ∀ c ∈ (ofHex d).coeffs, c ∈ Good K := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    have := List.all_eq_true.mp hint t ht
    simp only [beq_iff_eq] at this
    show ((t.2.den : ℕ) : K) ≠ 0
    rw [this]; simp
  unfold valueE
  rw [← toK_meaning (arityOk_ofHex d) hg, meaning_of hrt]

end GPBinding.Matroid
