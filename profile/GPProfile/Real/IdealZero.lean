import GPProfile.Algebra

/-!
The zero test of `A + Σ cᵢ·eᵢ` without building the products (ud22 performance, DECISIONS 2026-10-10).

An ordered or SOS replay ends by testing `A + Σ cᵢ·eᵢ = 0` in `ℚ[x]`, where the cofactors `cᵢ` are
large and the equations `eᵢ` small. Hex builds each product as a tree map and then merges them.
`idealZero` instead adds every term of `A` and every product of terms `(m₁, a)·(m₂, b)` into one hash
map keyed by exponent arrays, and accepts when every accumulated coefficient is zero. It is exact
arithmetic over ℚ, only regrouped: `idealZero_eq` proves it equals `A + (zipWith (· * ·) C E).sum == 0`,
coefficient by coefficient (Hex's `coeff_ofTerms`, `coeff_terms`, `coeff_add`).
-/

namespace GPProfile
open Hex

/-- Accumulated coefficients, keyed by exponent arrays. -/
abbrev Acc := Std.HashMap (Array Nat) Rat

/-- Add `x` to the coefficient at `k`. -/
def addT (acc : Acc) (k : Array Nat) (x : Rat) : Acc := acc.insert k (acc.getD k 0 + x)

/-- Add every term of a list. -/
def addTerms {n : Nat} (acc : Acc) (ts : List (Mono n × Rat)) : Acc :=
  ts.foldl (fun acc t => addT acc t.1.toArray t.2) acc

/-- Add every term of `c · e`, product by product of their terms. -/
def addProd {n : Nat} (acc : Acc) (c e : P n Rat) : Acc :=
  let et := e.termsList
  c.termsList.foldl (fun acc t => et.foldl (fun acc u => addT acc (Mono.mul t.1 u.1).toArray (t.2 * u.2)) acc) acc

/-- Whether `A + Σ cᵢ·eᵢ` is zero (`idealZero_eq`). -/
def idealZero {n : Nat} (A : P n Rat) (C E : List (P n Rat)) : Bool :=
  let acc := (C.zip E).foldl (fun acc ce => addProd acc ce.1 ce.2) (addTerms ∅ A.termsList)
  acc.toList.all fun kv => kv.2 == 0

/-! ## Correctness -/

attribute [local simp] Rat.add_zero Rat.zero_add

/-- The coefficient a term list gives a monomial (the right side of Hex's `coeff_ofTerms`). -/
def tsum {n : Nat} (ts : List (Mono n × Rat)) (m : Mono n) : Rat :=
  (ts.filter fun t => t.1 = m).foldl (fun acc t => acc + t.2) 0

theorem foldl_add_init {n : Nat} (l : List (Mono n × Rat)) (x : Rat) :
    l.foldl (fun acc t => acc + t.2) x = x + l.foldl (fun acc t => acc + t.2) 0 := by
  induction l generalizing x with
  | nil => simp
  | cons t l ih =>
    simp only [List.foldl_cons]
    rw [ih (x + t.2), ih (0 + t.2)]
    simp only [Rat.zero_add, Rat.add_assoc]

theorem tsum_nil {n : Nat} (m : Mono n) : tsum ([] : List (Mono n × Rat)) m = 0 := rfl

theorem tsum_cons {n : Nat} (t : Mono n × Rat) (ts : List (Mono n × Rat)) (m : Mono n) :
    tsum (t :: ts) m = (if t.1 = m then t.2 else 0) + tsum ts m := by
  unfold tsum
  by_cases h : t.1 = m
  · simp only [List.filter_cons, h, decide_true, ite_true, List.foldl_cons]
    rw [foldl_add_init, Rat.zero_add]
  · simp [h]

theorem tsum_append {n : Nat} (l₁ l₂ : List (Mono n × Rat)) (m : Mono n) :
    tsum (l₁ ++ l₂) m = tsum l₁ m + tsum l₂ m := by
  induction l₁ with
  | nil => simp [tsum_nil]
  | cons t l ih => rw [List.cons_append, tsum_cons, tsum_cons, ih, Rat.add_assoc]

theorem addT_getD (acc : Acc) (k j : Array Nat) (x : Rat) :
    (addT acc k x).getD j 0 = if k = j then acc.getD j 0 + x else acc.getD j 0 := by
  unfold addT
  rw [Std.HashMap.getD_insert]
  by_cases h : k = j
  · subst h; simp
  · simp [h]

theorem addTerms_getD {n : Nat} (acc : Acc) (ts : List (Mono n × Rat)) (m : Mono n) :
    (addTerms acc ts).getD m.toArray 0 = acc.getD m.toArray 0 + tsum ts m := by
  induction ts generalizing acc with
  | nil => simp [addTerms, tsum_nil]
  | cons t ts ih =>
    simp only [addTerms, List.foldl_cons] at ih ⊢
    rw [ih, addT_getD, tsum_cons]
    by_cases h : t.1 = m
    · subst h; simp [Rat.add_assoc]
    · have h' : t.1.toArray ≠ m.toArray := fun e => h (Vector.toArray_inj.mp e)
      simp [h, h']

/-- The term list of a product, pair by pair (the list Hex's `mul` folds). -/
def prodTerms {n : Nat} (c e : P n Rat) : List (Mono n × Rat) :=
  c.termsList.flatMap fun t => e.termsList.map fun u => (Mono.mul t.1 u.1, t.2 * u.2)

theorem addProd_eq {n : Nat} (acc : Acc) (c e : P n Rat) : addProd acc c e = addTerms acc (prodTerms c e) := by
  simp only [addProd, addTerms, prodTerms, List.foldl_flatMap, List.foldl_map]

theorem mul_ofTerms {n : Nat} (c e : P n Rat) : c * e = MvPoly.ofTerms (prodTerms c e) := by
  show MvPoly.mul c e = _
  unfold MvPoly.mul MvPoly.ofTerms MvPoly.foldTerms prodTerms MvPoly.termsList
  simp only [Std.ExtTreeMap.foldl_eq_foldl_toList, List.foldl_map, List.foldl_flatMap]

theorem coeff_mul_tsum {n : Nat} (c e : P n Rat) (m : Mono n) :
    MvPoly.coeff m (c * e) = tsum (prodTerms c e) m := by
  rw [mul_ofTerms, MvPoly.coeff_ofTerms]
  rfl

theorem coeff_tsum {n : Nat} (A : P n Rat) (m : Mono n) : MvPoly.coeff m A = tsum A.termsList m :=
  (MvPoly.coeff_terms m A).symm

/-- The accumulated coefficient of every monomial is the coefficient of `A + Σ cᵢ·eᵢ`. -/
theorem acc_getD {n : Nat} (A : P n Rat) (C E : List (P n Rat)) (m : Mono n) :
    ((C.zip E).foldl (fun acc ce => addProd acc ce.1 ce.2) (addTerms ∅ A.termsList)).getD m.toArray 0 =
      MvPoly.coeff m (A + (List.zipWith (· * ·) C E).sum) := by
  suffices h : ∀ (acc : Acc) (B : P n Rat), acc.getD m.toArray 0 = MvPoly.coeff m B →
      ((C.zip E).foldl (fun acc ce => addProd acc ce.1 ce.2) acc).getD m.toArray 0 =
        MvPoly.coeff m (B + (List.zipWith (· * ·) C E).sum) by
    apply h
    rw [addTerms_getD, coeff_tsum]
    simp
  induction C generalizing E with
  | nil => intro acc B h; simpa [MvPoly.coeff_add] using h
  | cons c C ih =>
    intro acc B h
    cases E with
    | nil => simpa [MvPoly.coeff_add] using h
    | cons e E =>
      simp only [List.zip_cons_cons, List.foldl_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [ih E (addProd acc c e) (B + c * e)]
      · rw [← MvPoly.add_assoc]
      · rw [addProd_eq, addTerms_getD, h, MvPoly.coeff_add, coeff_mul_tsum]

/-- Every key of an accumulator built from `Mono n` terms has `n` entries. -/
def KeysSized (n : Nat) (acc : Acc) : Prop := ∀ k ∈ acc, k.size = n

theorem addT_sized {n : Nat} {acc : Acc} {k : Array Nat} (x : Rat) (h : KeysSized n acc) (hk : k.size = n) :
    KeysSized n (addT acc k x) := by
  intro j hj
  unfold addT at hj
  rcases Std.HashMap.mem_insert.mp hj with e | e
  · have := LawfulBEq.eq_of_beq e; subst this; exact hk
  · exact h j e

theorem addTerms_sized {n : Nat} (acc : Acc) (ts : List (Mono n × Rat)) (h : KeysSized n acc) :
    KeysSized n (addTerms acc ts) := by
  induction ts generalizing acc with
  | nil => exact h
  | cons t ts ih =>
    simp only [addTerms, List.foldl_cons] at ih ⊢
    exact ih _ (addT_sized _ h t.1.size_toArray)

theorem acc_sized {n : Nat} (A : P n Rat) (C E : List (P n Rat)) :
    KeysSized n ((C.zip E).foldl (fun acc ce => addProd acc ce.1 ce.2) (addTerms ∅ A.termsList)) := by
  suffices h : ∀ (acc : Acc), KeysSized n acc →
      KeysSized n ((C.zip E).foldl (fun acc ce => addProd acc ce.1 ce.2) acc) by
    apply h
    apply addTerms_sized
    intro k hk
    simp at hk
  induction C generalizing E with
  | nil => intro acc h; exact h
  | cons c C ih =>
    intro acc h
    cases E with
    | nil => exact h
    | cons e E =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      exact ih E _ (by rw [addProd_eq]; exact addTerms_sized _ _ h)

/-- A map with sized keys is all zero exactly when its `getD` vanishes at every `Mono n`. -/
theorem all_zero_iff {n : Nat} (acc : Acc) (hs : KeysSized n acc) :
    (acc.toList.all fun kv => kv.2 == 0) = true ↔ ∀ m : Mono n, acc.getD m.toArray 0 = 0 := by
  constructor
  · intro h m
    rw [Std.HashMap.getD_eq_getD_getElem?]
    cases hv : acc[m.toArray]? with
    | none => rfl
    | some v =>
      have hmem : (m.toArray, v) ∈ acc.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hv
      have := List.all_eq_true.mp h _ hmem
      simpa using this
  · intro h
    apply List.all_eq_true.mpr
    intro kv hkv
    have hv := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkv
    have hk : kv.1 ∈ acc := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [hv])
    have hsz := hs kv.1 hk
    have := h ⟨kv.1, hsz⟩
    rw [Std.HashMap.getD_eq_getD_getElem?] at this
    rw [hv] at this
    simpa using this

theorem idealZero_eq {n : Nat} (A : P n Rat) (C E : List (P n Rat)) :
    idealZero A C E = (A + (List.zipWith (· * ·) C E).sum == 0) := by
  unfold idealZero
  apply Bool.eq_iff_iff.mpr
  rw [all_zero_iff _ (acc_sized A C E)]
  simp only [acc_getD, beq_iff_eq]
  constructor
  · intro h
    apply MvPoly.ext
    intro m
    rw [h m, MvPoly.coeff_zero]
  · intro h m
    rw [h, MvPoly.coeff_zero]

end GPProfile
