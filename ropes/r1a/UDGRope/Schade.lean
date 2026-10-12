import UDGRope.Basic

/-!
**Schade averaging.** `u(n) ≤ ⌊n · u(n−1) / (n−2)⌋` for `n ≥ 3`, with `u` formal-conjectures'
`maxUnitDistances` (copied in `UDGRope.Defs`).

Deleting a point `r` of an `n`-point set keeps exactly the unit pairs avoiding `r`. A unit pair
`{x, y}` (with `x ≠ y`) avoids `n − 2` of the `n` points, so summing over `r` counts every unit
pair `n − 2` times: `(n − 2) · unitDistNum P = Σ_r unitDistNum (P.erase r) ≤ n · u(n − 1)`.
`schade_bound` states this with any bound `m` for `(n−1)`-point sets; `schade` is the `sSup` form.
-/

namespace UDGRope
open scoped Finset

/-- The unit pairs of `P`, in the `Sym2.lift` form of `unitDistNum_eq`. -/
noncomputable def unitPairs (P : Finset ℝ²) : Finset (Sym2 ℝ²) :=
  {p ∈ P.sym2 | Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩ p = 1}

theorem card_unitPairs (P : Finset ℝ²) : #(unitPairs P) = unitDistNum P := (unitDistNum_eq P).symm

theorem unitDistNum_erase (P : Finset ℝ²) (r : ℝ²) :
    unitDistNum (P.erase r) = #{p ∈ unitPairs P | r ∉ p} := by
  rw [unitDistNum_eq, unitPairs, Finset.filter_filter]
  congr 1
  ext p
  induction p using Sym2.ind with
  | h x y =>
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_erase, Sym2.mem_iff,
      Sym2.lift_mk, not_or]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
      exact ⟨⟨h2, h4⟩, h5, Ne.symm h1, Ne.symm h3⟩
    · rintro ⟨⟨h2, h4⟩, h5, h1, h3⟩
      exact ⟨⟨⟨Ne.symm h1, h2⟩, ⟨Ne.symm h3, h4⟩⟩, h5⟩

/-- A unit pair avoids exactly `n − 2` points of the set. -/
theorem card_avoid {P : Finset ℝ²} {p : Sym2 ℝ²} (hp : p ∈ unitPairs P) :
    #{r ∈ P | r ∉ p} = #P - 2 := by
  classical
  induction p using Sym2.ind with
  | h x y =>
    simp only [unitPairs, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.lift_mk] at hp
    obtain ⟨⟨hx, hy⟩, hd⟩ := hp
    have hxy : x ≠ y := by rintro rfl; simp at hd
    have : ({r ∈ P | r ∉ s(x, y)} : Finset ℝ²) = P \ {x, y} := by
      ext r; simp [Sym2.mem_iff]
    rw [this, Finset.card_sdiff_of_subset (by simp [Finset.insert_subset_iff, hx, hy]),
      Finset.card_pair hxy]

/-- Every unit pair is missed by exactly two deletions: `Σ_r unitDistNum (P.erase r) =
(#P − 2) · unitDistNum P`. -/
theorem sum_unitDistNum_erase (P : Finset ℝ²) :
    ∑ r ∈ P, unitDistNum (P.erase r) = (#P - 2) * unitDistNum P := by
  classical
  simp_rw [unitDistNum_erase, Finset.card_filter]
  rw [Finset.sum_comm, ← card_unitPairs, mul_comm, Finset.card_eq_sum_ones (unitPairs P), Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [one_mul, ← card_avoid hp, Finset.card_filter]

/-- **Schade averaging**, bound form: if every `(n−1)`-point set has at most `m` unit pairs, every
`n`-point set (`n ≥ 3`) has at most `⌊n·m/(n−2)⌋`. -/
theorem schade_bound {n m : ℕ} (hn : 3 ≤ n)
    (hm : ∀ Q : Finset ℝ², #Q = n - 1 → unitDistNum Q ≤ m) (P : Finset ℝ²) (hP : #P = n) :
    unitDistNum P ≤ n * m / (n - 2) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hsum := sum_unitDistNum_erase P
  have hle : ∑ r ∈ P, unitDistNum (P.erase r) ≤ ∑ _r ∈ P, m :=
    Finset.sum_le_sum fun r hr => hm _ (by rw [Finset.card_erase_of_mem hr, hP])
  rw [Finset.sum_const, smul_eq_mul, hP] at hle
  rw [hsum, hP] at hle
  linarith [Nat.mul_comm (n - 2) (unitDistNum P)]

theorem unitDistNum_le (Q : Finset ℝ²) : unitDistNum Q ≤ (#Q + 1).choose 2 := by
  rw [unitDistNum, ← Finset.card_sym2]
  exact Finset.card_filter_le _ _

theorem unitDistanceCounts_bddAbove (n : ℕ) : BddAbove (unitDistanceCounts n) := by
  refine ⟨(n + 1).choose 2, ?_⟩
  rintro _ ⟨Q, rfl, rfl⟩
  exact unitDistNum_le Q

/-- Every `n`-point set has at most `u(n)` unit pairs (for `u(N) ≤ M` hypotheses as in P4). -/
theorem unitDistNum_le_maxUnitDistances {n : ℕ} (P : Finset ℝ²) (hP : #P = n) :
    unitDistNum P ≤ maxUnitDistances n :=
  le_csSup (unitDistanceCounts_bddAbove n) ⟨P, hP, rfl⟩

/-- **Schade averaging** (P8's first step): `u(n) ≤ ⌊n · u(n−1) / (n−2)⌋` for `n ≥ 3`, with `u` the
formal-conjectures `maxUnitDistances`. -/
theorem schade (n : ℕ) (hn : 3 ≤ n) :
    maxUnitDistances n ≤ n * maxUnitDistances (n - 1) / (n - 2) := by
  apply csSup_le'
  rintro _ ⟨P, hP, rfl⟩
  exact schade_bound hn (fun Q hQ => unitDistNum_le_maxUnitDistances Q hQ) P hP

end UDGRope
