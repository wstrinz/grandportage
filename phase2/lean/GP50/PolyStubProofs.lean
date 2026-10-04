import GP50.PolyStub
namespace GP50.PolyStub

theorem degreeFold_ge_initial (polynomial : Polynomial) (initial : Nat) :
    initial ≤ polynomial.foldl (fun bound term => max bound term.1) initial := by
  induction polynomial generalizing initial with
  | nil => simp
  | cons term rest ih =>
    exact Nat.le_trans (Nat.le_max_left _ _) (ih (max initial term.1))

theorem term_le_degreeFold (polynomial : Polynomial) (term : Nat × Rat)
    (present : term ∈ polynomial) (initial : Nat) :
    term.1 ≤ polynomial.foldl (fun bound term => max bound term.1) initial := by
  induction polynomial generalizing initial with
  | nil => simp at present
  | cons head rest ih =>
    simp only [List.mem_cons] at present
    rcases present with rfl | tail
    · exact Nat.le_trans (Nat.le_max_right _ _) (degreeFold_ge_initial rest (max initial term.1))
    · exact ih tail (max initial head.1)

theorem term_le_degreeBound (polynomial : Polynomial) (term : Nat × Rat)
    (present : term ∈ polynomial) : term.1 ≤ degreeBound polynomial :=
  term_le_degreeFold polynomial term present 0

theorem coefficientFold_of_missing (polynomial : Polynomial) (exponent : Nat)
    (missing : ∀ term ∈ polynomial, term.1 ≠ exponent) (initial : Rat) :
    polynomial.foldl
      (fun sum term => if term.1 == exponent then sum + term.2 else sum) initial = initial := by
  induction polynomial generalizing initial with
  | nil => rfl
  | cons head rest ih =>
    have different := missing head (by simp)
    have tail := ih (fun term present => missing term (by simp [present])) initial
    simpa [different] using tail

theorem coefficient_zero_above_bound (polynomial : Polynomial) (exponent : Nat)
    (above : degreeBound polynomial < exponent) : coefficient polynomial exponent = 0 := by
  apply coefficientFold_of_missing
  intro term present equalExponent
  have bound := term_le_degreeBound polynomial term present
  omega

theorem equal_sound (left right : Polynomial) (success : equal left right = true) :
    ∀ exponent, coefficient left exponent = coefficient right exponent := by
  intro exponent
  by_cases inside : exponent < max (degreeBound left) (degreeBound right) + 1
  · have all := List.all_eq_true.mp success
    exact eq_of_beq (all exponent (List.mem_range.mpr inside))
  · have leftBound := Nat.le_max_left (degreeBound left) (degreeBound right)
    have rightBound := Nat.le_max_right (degreeBound left) (degreeBound right)
    rw [coefficient_zero_above_bound left exponent (by omega),
      coefficient_zero_above_bound right exponent (by omega)]

theorem coefficientFold_offset (polynomial : Polynomial) (exponent : Nat) (initial : Rat) :
    polynomial.foldl (fun sum term => if term.1 == exponent then sum + term.2 else sum) initial =
      initial + coefficient polynomial exponent := by
  induction polynomial generalizing initial with
  | nil => simp [coefficient, Rat.add_zero]
  | cons head rest ih =>
    cases same : head.1 == exponent with
    | false =>
      simpa only [coefficient, List.foldl_cons, same, Bool.false_eq_true, if_false] using ih initial
    | true =>
      simp only [coefficient, List.foldl_cons, same, if_true, Rat.zero_add]
      rw [ih, ih]
      exact Rat.add_assoc _ _ _

theorem coefficient_append (left right : Polynomial) (exponent : Nat) :
    coefficient (left ++ right) exponent = coefficient left exponent + coefficient right exponent := by
  simp only [coefficient, List.foldl_append]
  exact coefficientFold_offset right exponent (coefficient left exponent)

theorem coefficient_flatMap {α : Type} (values : List α) (polynomial : α → Polynomial)
    (exponent : Nat) :
    coefficient (values.flatMap polynomial) exponent =
      (values.map fun value => coefficient (polynomial value) exponent).sum := by
  induction values with
  | nil => simp [coefficient]
  | cons head rest ih =>
    simp [coefficient_append, ih, List.sum_cons]

-- Exact formal univariate polynomial-span identity of the implemented term list.
-- No statement about geometric points, emptiness, binding, or multivariate reach.
theorem replay_sound (generators cofactors : List Polynomial) (target : Polynomial)
    (success : replay generators cofactors target = true) :
    generators.length = cofactors.length ∧
      ∀ exponent, coefficient
        ((generators.zip cofactors).flatMap fun (generator,cofactor) =>
          multiply generator cofactor) exponent = coefficient target exponent := by
  have parts : generators.length = cofactors.length ∧
      equal ((generators.zip cofactors).flatMap fun (generator,cofactor) =>
        multiply generator cofactor) target = true := by
    simpa only [replay, Bool.and_eq_true, beq_iff_eq] using success
  exact ⟨parts.1, equal_sound _ target parts.2⟩

theorem replay_coefficient_sum (generators cofactors : List Polynomial) (target : Polynomial)
    (success : replay generators cofactors target = true) :
    generators.length = cofactors.length ∧
      ∀ exponent, ((generators.zip cofactors).map fun (generator,cofactor) =>
        coefficient (multiply generator cofactor) exponent).sum = coefficient target exponent := by
  have identity := replay_sound generators cofactors target success
  refine ⟨identity.1, ?_⟩
  intro exponent
  rw [← coefficient_flatMap]
  exact identity.2 exponent

#print axioms coefficient_zero_above_bound
#print axioms equal_sound
#print axioms replay_sound
#print axioms replay_coefficient_sum
end GP50.PolyStub

