/-
An integer-expression slice of rational_sos_cofactor_v1.
Expressions and derivations are explicit. No certificate equality is assumed.
The Python parser, rational denominators, and receipt binding are separate.
-/
import GrandPortage.Atlas

namespace GrandPortage.CertificateInterpreter

universe u

inductive Expr where
  | zero | one | var (index : Nat)
  | add (left right : Expr) | mul (left right : Expr) | neg (value : Expr)
  deriving Repr, DecidableEq

structure Operations (Value : Type u) where
  zero : Value
  one : Value
  add : Value → Value → Value
  mul : Value → Value → Value
  neg : Value → Value

variable {Value : Type u} {o : Operations Value}

def eval (o : Operations Value) (point : Nat → Value) : Expr → Value
  | .zero => o.zero
  | .one => o.one
  | .var i => point i
  | .add a b => o.add (eval o point a) (eval o point b)
  | .mul a b => o.mul (eval o point a) (eval o point b)
  | .neg a => o.neg (eval o point a)

/-- Ordinary algebraic laws used by this small derivation language.
This is not an assumption that the supplied certificate evaluates correctly. -/
structure Laws (o : Operations Value) : Prop where
  add_assoc : ∀ a b c, o.add (o.add a b) c = o.add a (o.add b c)
  add_zero : ∀ a, o.add a o.zero = a
  zero_add : ∀ a, o.add o.zero a = a
  add_neg : ∀ a, o.add a (o.neg a) = o.zero
  neg_add : ∀ a b, o.neg (o.add a b) = o.add (o.neg a) (o.neg b)
  neg_one_mul : ∀ a, o.mul (o.neg o.one) a = o.neg a
  mul_zero : ∀ a, o.mul a o.zero = o.zero

inductive Derivation : Expr → Expr → Prop where
  | refl (a) : Derivation a a
  | symm : Derivation a b → Derivation b a
  | trans : Derivation a b → Derivation b c → Derivation a c
  | add : Derivation a b → Derivation c d → Derivation (.add a c) (.add b d)
  | mul : Derivation a b → Derivation c d → Derivation (.mul a c) (.mul b d)
  | neg : Derivation a b → Derivation (.neg a) (.neg b)
  | assoc (a b c) : Derivation (.add (.add a b) c) (.add a (.add b c))
  | addZero (a) : Derivation (.add a .zero) a
  | zeroAdd (a) : Derivation (.add .zero a) a
  | cancel (a) : Derivation (.add a (.neg a)) .zero
  | negAdd (a b) : Derivation (.neg (.add a b)) (.add (.neg a) (.neg b))
  | negOneMul (a) : Derivation (.mul (.neg .one) a) (.neg a)

theorem derivation_sound (laws : Laws o) (point : Nat → Value)
    (proof : Derivation a b) : eval o point a = eval o point b := by
  induction proof with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | neg _ ih => exact congrArg o.neg ih
  | assoc => exact laws.add_assoc _ _ _
  | addZero => exact laws.add_zero _
  | zeroAdd => exact laws.zero_add _
  | cancel => exact laws.add_neg _
  | negAdd => exact laws.neg_add _ _
  | negOneMul => exact laws.neg_one_mul _

def sumExpr : List Expr → Expr
  | [] => .zero
  | a :: rest => .add a (sumExpr rest)

/-- A cofactor is paired with exactly the generator it multiplies. -/
structure Certificate where
  squares : List Expr
  terms : List (Expr × Expr)

def Certificate.rhs (c : Certificate) : Expr :=
  .add (sumExpr (c.squares.map fun s => .mul s s))
       (sumExpr (c.terms.map fun (h, f) => .mul h f))

def Certificate.Holds (c : Certificate) (o : Operations Value)
    (point : Nat → Value) : Prop :=
  ∀ term ∈ c.terms, eval o point term.2 = o.zero

structure Ordering (o : Operations Value) where
  nonnegative : Value → Prop
  zero_nonnegative : nonnegative o.zero
  add_nonnegative : ∀ a b, nonnegative a → nonnegative b → nonnegative (o.add a b)
  square_nonnegative : ∀ a, nonnegative (o.mul a a)
  negative_one_not_nonnegative : ¬ nonnegative (o.neg o.one)

def arithmetic (laws : Laws o) (order : Ordering o) : Atlas.OrderedArithmetic Value := {
  zero := o.zero, negativeOne := o.neg o.one, add := o.add, mul := o.mul
  nonnegative := order.nonnegative
  zero_nonnegative := order.zero_nonnegative
  add_nonnegative := order.add_nonnegative
  square_nonnegative := order.square_nonnegative
  negativeOne_not_nonnegative := order.negative_one_not_nonnegative
  add_zero := laws.add_zero, mul_zero := laws.mul_zero
}

theorem eval_sum (laws : Laws o) (order : Ordering o) (point : Nat → Value)
    (xs : List Expr) : eval o point (sumExpr xs) =
      Atlas.sumValues (arithmetic laws order) (xs.map (eval o point)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simpa [sumExpr, eval, Atlas.sumValues, arithmetic] using
        congrArg (o.add (eval o point a)) ih

/-- From a syntactic derivation, through evaluation and generator vanishing,
to contradiction. There is no evaluated-certificate-equality premise. -/
theorem certificate_empty (laws : Laws o) (order : Ordering o)
    (c : Certificate) (proof : Derivation c.rhs (.neg .one))
    (point : Nat → Value) (holds : c.Holds o point) : False := by
  have replayed := (derivation_sound laws point proof).symm
  have zeroTerms : ∀ x ∈ (c.terms.map fun (h, f) =>
      o.mul (eval o point h) (eval o point f)), x = o.zero := by
    intro x hx
    obtain ⟨⟨h, f⟩, hmem, rfl⟩ := List.mem_map.mp hx
    change o.mul (eval o point h) (eval o point f) = o.zero
    have hf : eval o point f = o.zero := holds (h, f) hmem
    rw [hf, laws.mul_zero]
  apply Atlas.orderedSOS_contradiction (arithmetic laws order)
    (c.squares.map (eval o point))
    (c.terms.map fun (h, f) => o.mul (eval o point h) (eval o point f)) zeroTerms
  simpa [Certificate.rhs, eval, eval_sum laws order, List.map_map,
    Function.comp_def, arithmetic] using replayed

def sample : Certificate := {
  squares := [.var 0]
  terms := [(.neg .one, .add (.mul (.var 0) (.var 0)) .one)]
}

theorem sample_derivation : Derivation sample.rhs (.neg .one) := by
  let a : Expr := .mul (.var 0) (.var 0)
  change Derivation (.add (.add a .zero)
    (.add (.mul (.neg .one) (.add a .one)) .zero)) (.neg .one)
  apply Derivation.trans (Derivation.add (Derivation.addZero a)
    (Derivation.addZero _))
  apply Derivation.trans (Derivation.add (Derivation.refl a)
    (Derivation.negOneMul _))
  apply Derivation.trans (Derivation.add (Derivation.refl a)
    (Derivation.negAdd a .one))
  apply Derivation.trans (Derivation.symm (Derivation.assoc a (.neg a) (.neg .one)))
  apply Derivation.trans (Derivation.add (Derivation.cancel a) (Derivation.refl _))
  exact Derivation.zeroAdd _

theorem sample_empty (laws : Laws o) (order : Ordering o) (point : Nat → Value) :
    ¬ sample.Holds o point :=
  certificate_empty laws order sample sample_derivation point

/-- A concrete ordered interpretation discharges every interface law, so the
generic theorem is not relying on an uninhabited collection of premises. -/
def integers : Operations Int := {
  zero := 0, one := 1, add := Int.add, mul := Int.mul, neg := Int.neg
}

theorem integer_laws : Laws integers := {
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_neg := Int.add_right_neg
  neg_add := fun _ _ => Int.neg_add
  neg_one_mul := Int.neg_one_mul
  mul_zero := Int.mul_zero
}

def integer_order : Ordering integers := {
  nonnegative := fun x => 0 ≤ x
  zero_nonnegative := by decide
  add_nonnegative := fun _ _ ha hb => Int.add_nonneg ha hb
  square_nonnegative := by
    intro a
    change 0 ≤ a * a
    by_cases h : 0 ≤ a
    · exact Int.mul_nonneg h h
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  negative_one_not_nonnegative := by decide
}

theorem integer_no_root (x : Int) : x * x + 1 ≠ 0 := by
  intro hx
  apply sample_empty integer_laws integer_order (fun _ => x)
  intro term h
  simp only [sample, List.mem_cons, List.not_mem_nil, or_false] at h
  subst term
  exact hx

/-- Explicit Gaussian-integer arithmetic: the pair (0,1) is an unordered
solution. This does not assume or formalize a general complex field library. -/
def gaussian : Operations (Int × Int) := {
  zero := (0, 0), one := (1, 0)
  add := fun a b => (a.1 + b.1, a.2 + b.2)
  neg := fun a => (-a.1, -a.2)
  mul := fun a b => (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
}

def imaginaryPoint : Nat → Int × Int := fun _ => (0, 1)

theorem unordered_solution_and_replay :
    sample.Holds gaussian imaginaryPoint ∧
    eval gaussian imaginaryPoint sample.rhs = eval gaussian imaginaryPoint (.neg .one) := by
  constructor
  · intro term h
    simp only [sample, List.mem_cons, List.not_mem_nil, or_false] at h
    subst term
    decide
  · decide

theorem gaussian_has_no_ordering : ¬ Nonempty (Ordering gaussian) := by
  rintro ⟨order⟩
  have h := order.square_nonnegative (0, 1)
  exact order.negative_one_not_nonnegative h

end GrandPortage.CertificateInterpreter
