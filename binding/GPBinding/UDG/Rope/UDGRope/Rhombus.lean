import UDGRope.Basic
import Mathlib.Data.Complex.Basic

/-!
**P1, the rhombus lemma.** In an injective unit-distance embedding into the plane, every 4-cycle
`a-b-c-d` has `p a - p b + p c - p d = 0` (artwaste `check/PROOFS.md`, "Two geometric facts").

The proof is algebra in coordinates and holds over every field with `2 ≠ 0` for the quadratic form
`x² + y²` (`rhombus_field`). With `w = c - a`, `e = b - d`, `z = b + d - a - c`: the four unit
equations give `⟨e, w⟩ = ⟨z, w⟩ = ⟨z, e⟩ = 0`, so `z · det(w, e) = 0`. If the determinant vanishes,
Lagrange's identity forces `w` or `e` to be isotropic, and each case collapses `a = c` or `b = d`.

Controls:
- `rhombus_needs_injective`: without injectivity the conclusion fails (`a` and `c` collide).
- Over `ℂ²` with the bilinear form, the lemma still **holds** for injective maps
  (`rhombus_complex`), contrary to the packet's expected control (HW61 §3, P1). What fails over `ℂ`
  is the frame's reading of injectivity as the guard `Δx² + Δy² ≠ 0`
  (`complex_isotropic_pair`: distinct points with zero squared distance).
-/

namespace UDGRope

section Field
variable {K : Type*} [Field K]

/-- The rhombus lemma in coordinates, over any field with `2 ≠ 0`. -/
theorem rhombus_field (h2 : (2 : K) ≠ 0) {a0 a1 b0 b1 c0 c1 d0 d1 : K}
    (hab : (a0 - b0) ^ 2 + (a1 - b1) ^ 2 = 1) (hbc : (b0 - c0) ^ 2 + (b1 - c1) ^ 2 = 1)
    (hcd : (c0 - d0) ^ 2 + (c1 - d1) ^ 2 = 1) (hda : (d0 - a0) ^ 2 + (d1 - a1) ^ 2 = 1)
    (hac : ¬ (a0 = c0 ∧ a1 = c1)) (hbd : ¬ (b0 = d0 ∧ b1 = d1)) :
    a0 - b0 + c0 - d0 = 0 ∧ a1 - b1 + c1 - d1 = 0 := by
  -- w = c - a, e = b - d, z = b + d - a - c, u = b - a
  have hew : (b0 - d0) * (c0 - a0) + (b1 - d1) * (c1 - a1) = 0 := by
    have : 2 * ((b0 - d0) * (c0 - a0) + (b1 - d1) * (c1 - a1)) = 0 := by
      linear_combination hab - hbc - hda + hcd
    simpa [h2] using this
  have hzw : (b0 + d0 - a0 - c0) * (c0 - a0) + (b1 + d1 - a1 - c1) * (c1 - a1) = 0 := by
    have : 2 * ((b0 + d0 - a0 - c0) * (c0 - a0) + (b1 + d1 - a1 - c1) * (c1 - a1)) = 0 := by
      linear_combination hab - hbc + hda - hcd
    simpa [h2] using this
  have hze : (b0 + d0 - a0 - c0) * (b0 - d0) + (b1 + d1 - a1 - c1) * (b1 - d1) = 0 := by
    linear_combination hab - hda - hew
  have hz0 : (b0 + d0 - a0 - c0) * ((c0 - a0) * (b1 - d1) - (c1 - a1) * (b0 - d0)) = 0 := by
    linear_combination (b1 - d1) * hzw - (c1 - a1) * hze
  have hz1 : (b1 + d1 - a1 - c1) * ((c0 - a0) * (b1 - d1) - (c1 - a1) * (b0 - d0)) = 0 := by
    linear_combination (c0 - a0) * hze - (b0 - d0) * hzw
  have sq0 : ∀ t : K, 2 * t ^ 2 = 0 → t = 0 := fun t ht => by
    have : t ^ 2 = 0 := by simpa [h2] using ht
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  -- `w` is not isotropic: else `u ⊥ w` and `u ∥ w` force `w = 0`
  have hQw : (c0 - a0) ^ 2 + (c1 - a1) ^ 2 ≠ 0 := by
    intro hw
    have huw : (b0 - a0) * (c0 - a0) + (b1 - a1) * (c1 - a1) = 0 := by
      have : 2 * ((b0 - a0) * (c0 - a0) + (b1 - a1) * (c1 - a1)) = 0 := by
        linear_combination hab - hbc + hw
      simpa [h2] using this
    have hD' : ((c0 - a0) * (b1 - a1) - (c1 - a1) * (b0 - a0)) ^ 2 = 0 := by
      linear_combination ((b0 - a0) ^ 2 + (b1 - a1) ^ 2) * hw -
        ((b0 - a0) * (c0 - a0) + (b1 - a1) * (c1 - a1)) * huw
    have hD'0 := pow_eq_zero_iff two_ne_zero |>.mp hD'
    have hsq : (c0 - a0) ^ 2 = (c1 - a1) ^ 2 := by
      linear_combination ((c0 - a0) * (b0 - a0) - (c1 - a1) * (b1 - a1)) * huw +
        ((c0 - a0) * (b1 - a1) + (c1 - a1) * (b0 - a0)) * hD'0 - ((c0 - a0) ^ 2 - (c1 - a1) ^ 2) * hab
    have h0 := sq0 (c0 - a0) (by linear_combination hw + hsq)
    have h1 : c1 - a1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by rw [← hsq, h0]; ring)
    exact hac ⟨by linear_combination -h0, by linear_combination -h1⟩
  by_cases hD0 : ((c0 - a0) * (b1 - d1) - (c1 - a1) * (b0 - d0)) = 0
  · -- then `e` is isotropic, and `e ⊥ w`, `e ∥ w` force `e = 0`
    exfalso
    have hQe : (b0 - d0) ^ 2 + (b1 - d1) ^ 2 = 0 := by
      have : ((c0 - a0) ^ 2 + (c1 - a1) ^ 2) * ((b0 - d0) ^ 2 + (b1 - d1) ^ 2) = 0 := by
        linear_combination ((b0 - d0) * (c0 - a0) + (b1 - d1) * (c1 - a1)) * hew + ((c0 - a0) * (b1 - d1) - (c1 - a1) * (b0 - d0)) * hD0
      exact (mul_eq_zero.mp this).resolve_left hQw
    have hsq : ((c0 - a0) ^ 2 + (c1 - a1) ^ 2) * ((b0 - d0) ^ 2 - (b1 - d1) ^ 2) = 0 := by
      linear_combination ((b0 - d0) * (c0 - a0) - (b1 - d1) * (c1 - a1)) * hew -
        ((b0 - d0) * (c1 - a1) + (b1 - d1) * (c0 - a0)) * hD0
    have hsq' := (mul_eq_zero.mp hsq).resolve_left hQw
    have h0 := sq0 (b0 - d0) (by linear_combination hQe + hsq')
    have h1 : b1 - d1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hQe - (b0 - d0) * h0)
    exact hbd ⟨by linear_combination h0, by linear_combination h1⟩
  · have e0 := (mul_eq_zero.mp hz0).resolve_right hD0
    have e1 := (mul_eq_zero.mp hz1).resolve_right hD0
    exact ⟨by linear_combination -e0, by linear_combination -e1⟩

end Field

/-- **P1 (rhombus lemma).** In an injective unit-distance embedding into the Euclidean plane,
every 4-cycle `a-b-c-d` (closed, with `a ≠ c` and `b ≠ d`) has `p a - p b + p c - p d = 0`. -/
theorem rhombus {V : Type*} {G : SimpleGraph V} (f : G.UnitDistEmbedding ℝ²) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) :
    f.p a - f.p b + f.p c - f.p d = 0 := by
  have u1 := (dist_eq_one_iff _ _).mp (f.unit_dist hab)
  have u2 := (dist_eq_one_iff _ _).mp (f.unit_dist hbc)
  have u3 := (dist_eq_one_iff _ _).mp (f.unit_dist hcd)
  have u4 := (dist_eq_one_iff _ _).mp (f.unit_dist hda)
  have nac : ¬ (f.p a 0 = f.p c 0 ∧ f.p a 1 = f.p c 1) := fun h =>
    hac (f.p.injective (PiLp.ext fun i => by fin_cases i; exacts [h.1, h.2]))
  have nbd : ¬ (f.p b 0 = f.p d 0 ∧ f.p b 1 = f.p d 1) := fun h =>
    hbd (f.p.injective (PiLp.ext fun i => by fin_cases i; exacts [h.1, h.2]))
  obtain ⟨h0, h1⟩ := rhombus_field two_ne_zero u1 u2 u3 u4 nac nbd
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- Control: without injectivity the rhombus lemma fails (`a = c`, `b ≠ d`). -/
theorem rhombus_needs_injective :
    ∃ p : Fin 4 → ℝ², dist (p 0) (p 1) = 1 ∧ dist (p 1) (p 2) = 1 ∧ dist (p 2) (p 3) = 1 ∧
      dist (p 3) (p 0) = 1 ∧ p 0 - p 1 + p 2 - p 3 ≠ 0 := by
  refine ⟨![pt 0 0, pt 1 0, pt 0 0, pt 0 1], ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_eq_one_iff]; simp
  · rw [dist_eq_one_iff]; simp
  · rw [dist_eq_one_iff]; simp
  · rw [dist_eq_one_iff]; simp
  · intro h
    have := congrArg (fun v : ℝ² => v 0) h
    simp at this

/-- Over `ℂ²` with the bilinear form the rhombus lemma still holds for injective maps: the packet's
expected failing control does not fail. -/
theorem rhombus_complex (p : Fin 4 → Fin 2 → ℂ) (hp : Function.Injective p)
    (h : ∀ i : Fin 4, (p i 0 - p (i + 1) 0) ^ 2 + (p i 1 - p (i + 1) 1) ^ 2 = 1) :
    p 0 - p 1 + p 2 - p 3 = 0 := by
  have ne : ∀ i j : Fin 4, i ≠ j → ¬ (p i 0 = p j 0 ∧ p i 1 = p j 1) := fun i j hij h' =>
    hij (hp (funext fun k => by fin_cases k; exacts [h'.1, h'.2]))
  obtain ⟨h0, h1⟩ := rhombus_field two_ne_zero (h 0) (h 1) (h 2) (h 3) (ne 0 2 (by decide))
    (ne 1 3 (by decide))
  funext k
  fin_cases k
  · simpa using h0
  · simpa using h1

/-- What does fail over `ℂ`: distinct points at squared distance 0, so the guard
`Δx² + Δy² ≠ 0` is stronger than injectivity there (M5 pitfall 3). -/
theorem complex_isotropic_pair :
    ∃ p q : Fin 2 → ℂ, p ≠ q ∧ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 0 := by
  refine ⟨![1, Complex.I], 0, fun h => by simpa using congrFun h 0, ?_⟩
  simp

end UDGRope
