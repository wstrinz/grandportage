/-
# Unilateral finite-tail recurrence semantics

This file isolates the semantic fact behind the corrected JC adjoint-recurrence
receipt. A bounded constant-coefficient forward-shift operator acts only on the
declared unilateral domain. If a sequence is zero from `cutoff` onward but is
nonzero at `cutoff - 1`, its annihilators are exactly those whose coefficients
below `cutoff - start` vanish.

For the live instance, `start = 6` and `cutoff = 14`, so the annihilator ideal
is `(S^8)`. This statement does not establish the native sequence premises;
the bounded evidence checker must do that independently.

Like the rest of the GP semantic shadow, this file is deliberately Mathlib-free.
-/

namespace GrandPortage

universe u v

variable {K : Type u} {M : Type v}

/-- Apply coefficients `0 .. width-1` as forward shifts at depth `d`. -/
def applyForwardShift [Zero M] [Add M] [SMul K M]
    (coefficients : Nat → K) (sequence : Nat → M) (d : Nat) : Nat → M
  | 0 => 0
  | width + 1 =>
      applyForwardShift coefficients sequence d width +
        coefficients width • sequence (d + width)

/-- The bounded operator vanishes at every point of the unilateral domain. -/
def AnnihilatesFrom [Zero M] [Add M] [SMul K M]
    (coefficients : Nat → K) (width : Nat)
    (sequence : Nat → M) (start : Nat) : Prop :=
  ∀ d, start ≤ d → applyForwardShift coefficients sequence d width = 0

/-- The sequence is identically zero at and after the declared cutoff. -/
def ZeroFrom [Zero M] (sequence : Nat → M) (cutoff : Nat) : Prop :=
  ∀ n, cutoff ≤ n → sequence n = 0

theorem applyForwardShift_eq_zero_of_terms
    [Zero M] [Add M] [SMul K M]
    (zero_add : ∀ x : M, 0 + x = x)
    (coefficients : Nat → K) (sequence : Nat → M) (d width : Nat)
    (terms_zero : ∀ i, i < width → coefficients i • sequence (d + i) = 0) :
    applyForwardShift coefficients sequence d width = 0 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [applyForwardShift, ih]
      · exact zero_add _ |>.trans (terms_zero width (by omega))
      · intro i i_lt
        exact terms_zero i (by omega)

theorem applyForwardShift_eq_single_of_lowest
    [Zero K] [Zero M] [Add M] [SMul K M]
    (zero_add : ∀ x : M, 0 + x = x)
    (add_zero : ∀ x : M, x + 0 = x)
    (zero_smul : ∀ x : M, (0 : K) • x = 0)
    (smul_zero : ∀ x : K, x • (0 : M) = 0)
    (coefficients : Nat → K) (sequence : Nat → M)
    (d width i : Nat)
    (i_lt_width : i < width)
    (lowest : ∀ j, j < i → coefficients j = 0)
    (higher_zero : ∀ j, i < j → j < width → sequence (d + j) = 0) :
    applyForwardShift coefficients sequence d width =
      coefficients i • sequence (d + i) := by
  induction width generalizing i with
  | zero => omega
  | succ width ih =>
      rw [applyForwardShift]
      by_cases width_eq : width = i
      · subst width
        have prefix_zero := applyForwardShift_eq_zero_of_terms zero_add
          coefficients sequence d i (fun j j_lt => by
            rw [lowest j j_lt, zero_smul])
        rw [prefix_zero, zero_add]
      · have i_lt_previous : i < width := by omega
        rw [ih i i_lt_previous
          (fun j (j_lt : j < i) => lowest j j_lt)
          (fun j (i_lt_j : i < j) j_lt =>
            higher_zero j i_lt_j (by omega))]
        rw [higher_zero width i_lt_previous (by omega), smul_zero, add_zero]

/--
No annihilator can have a nonzero lowest coefficient before the cutoff gap.
This is the backward-induction step that the native JC receipt previously
described only in prose.
-/
theorem no_low_shift_annihilator
    [Zero K] [Zero M] [Add M] [SMul K M]
    (zero_add : ∀ x : M, 0 + x = x)
    (add_zero : ∀ x : M, x + 0 = x)
    (zero_smul : ∀ x : M, (0 : K) • x = 0)
    (smul_zero : ∀ x : K, x • (0 : M) = 0)
    (nonzero_smul : ∀ {a : K} {x : M}, a ≠ 0 → x ≠ 0 → a • x ≠ 0)
    (coefficients : Nat → K) (width : Nat) (sequence : Nat → M)
    (start cutoff i : Nat)
    (start_lt_cutoff : start < cutoff)
    (gap_lt_width : cutoff - start ≤ width)
    (i_lt_gap : i < cutoff - start)
    (coefficient_nonzero : coefficients i ≠ 0)
    (lowest : ∀ j, j < i → coefficients j = 0)
    (tail : ZeroFrom sequence cutoff)
    (last_nonzero : sequence (cutoff - 1) ≠ 0) :
    ¬ AnnihilatesFrom coefficients width sequence start := by
  intro annihilates
  have i_lt_width : i < width := by omega
  have start_le_probe : start ≤ cutoff - 1 - i := by omega
  have evaluated := annihilates (cutoff - 1 - i) start_le_probe
  rw [applyForwardShift_eq_single_of_lowest zero_add add_zero zero_smul
      smul_zero coefficients sequence (cutoff - 1 - i) width i i_lt_width
      lowest] at evaluated
  · have probe_eq : cutoff - 1 - i + i = cutoff - 1 := by omega
    rw [probe_eq] at evaluated
    exact (nonzero_smul coefficient_nonzero last_nonzero) evaluated
  · intro j i_lt_j j_lt_width
    apply tail
    omega

/-- Every coefficient below the cutoff gap of an annihilator must vanish. -/
theorem annihilator_coefficients_below_gap_zero
    [Zero K] [Zero M] [Add M] [SMul K M]
    (zero_add : ∀ x : M, 0 + x = x)
    (add_zero : ∀ x : M, x + 0 = x)
    (zero_smul : ∀ x : M, (0 : K) • x = 0)
    (smul_zero : ∀ x : K, x • (0 : M) = 0)
    (nonzero_smul : ∀ {a : K} {x : M}, a ≠ 0 → x ≠ 0 → a • x ≠ 0)
    (coefficients : Nat → K) (width : Nat) (sequence : Nat → M)
    (start cutoff : Nat)
    (start_lt_cutoff : start < cutoff)
    (gap_lt_width : cutoff - start ≤ width)
    (tail : ZeroFrom sequence cutoff)
    (last_nonzero : sequence (cutoff - 1) ≠ 0)
    (annihilates : AnnihilatesFrom coefficients width sequence start) :
    ∀ i, i < cutoff - start → coefficients i = 0 := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro i_lt_gap
      by_cases coefficient_zero : coefficients i = 0
      · exact coefficient_zero
      · exact False.elim ((no_low_shift_annihilator zero_add add_zero zero_smul
          smul_zero nonzero_smul coefficients width sequence start cutoff i
          start_lt_cutoff gap_lt_width i_lt_gap coefficient_zero
          (fun j j_lt => ih j j_lt (by omega)) tail last_nonzero) annihilates)

/-- Coefficients supported at or beyond the cutoff gap always annihilate. -/
theorem high_shift_coefficients_annihilate
    [Zero K] [Zero M] [Add M] [SMul K M]
    (zero_add : ∀ x : M, 0 + x = x)
    (zero_smul : ∀ x : M, (0 : K) • x = 0)
    (smul_zero : ∀ x : K, x • (0 : M) = 0)
    (coefficients : Nat → K) (width : Nat) (sequence : Nat → M)
    (start cutoff : Nat)
    (start_le_cutoff : start ≤ cutoff)
    (tail : ZeroFrom sequence cutoff)
    (high_support : ∀ i, i < cutoff - start → coefficients i = 0) :
    AnnihilatesFrom coefficients width sequence start := by
  intro d start_le_d
  apply applyForwardShift_eq_zero_of_terms zero_add
  intro i i_lt_width
  by_cases i_lt_gap : i < cutoff - start
  · rw [high_support i i_lt_gap, zero_smul]
  · rw [tail (d + i) (by omega), smul_zero]

/--
Characterization of the unilateral constant-coefficient annihilator ideal.
At the coefficient level, this says exactly that the operator is divisible by
`S^(cutoff-start)`.
-/
theorem annihilatesFrom_iff_coefficients_below_gap_zero
    [Zero K] [Zero M] [Add M] [SMul K M]
    (zero_add : ∀ x : M, 0 + x = x)
    (add_zero : ∀ x : M, x + 0 = x)
    (zero_smul : ∀ x : M, (0 : K) • x = 0)
    (smul_zero : ∀ x : K, x • (0 : M) = 0)
    (nonzero_smul : ∀ {a : K} {x : M}, a ≠ 0 → x ≠ 0 → a • x ≠ 0)
    (coefficients : Nat → K) (width : Nat) (sequence : Nat → M)
    (start cutoff : Nat)
    (start_lt_cutoff : start < cutoff)
    (gap_lt_width : cutoff - start ≤ width)
    (tail : ZeroFrom sequence cutoff)
    (last_nonzero : sequence (cutoff - 1) ≠ 0) :
    AnnihilatesFrom coefficients width sequence start ↔
      ∀ i, i < cutoff - start → coefficients i = 0 := by
  constructor
  · exact annihilator_coefficients_below_gap_zero zero_add add_zero zero_smul
      smul_zero nonzero_smul coefficients width sequence start cutoff
      start_lt_cutoff gap_lt_width tail last_nonzero
  · exact high_shift_coefficients_annihilate zero_add zero_smul smul_zero
      coefficients width sequence start cutoff
      (Nat.le_of_lt start_lt_cutoff) tail

/-- The live arithmetic boundary is an eight-step cutoff gap. -/
theorem jcAdjoint_cutoff_gap : 14 - 6 = 8 := by decide

end GrandPortage
