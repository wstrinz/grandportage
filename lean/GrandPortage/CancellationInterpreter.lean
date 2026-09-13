import GrandPortage.UnitInterpreter

namespace GrandPortage.CertificateInterpreter
universe u
variable {A : Type u} {o : Operations A}

def NoZeroDivisors (o : Operations A) : Prop :=
  ∀ a b, o.mul a b = o.zero → a = o.zero ∨ b = o.zero

def DomainProfile (o : Operations A) : Prop := o.one ≠ o.zero ∧ NoZeroDivisors o

theorem cancellation (laws : Laws o) (domain : NoZeroDivisors o)
    (point : Nat → A) (c g f : Expr) (proof : Derivation (.mul c g) f)
    (equation : eval o point f = o.zero) (coefficient : eval o point c ≠ o.zero) :
    eval o point g = o.zero := by
  have product := (derivation_sound laws point proof).trans equation
  exact (domain _ _ product).resolve_left coefficient

theorem cancellation_contradiction (laws : Laws o) (domain : NoZeroDivisors o)
    (point : Nat → A) (c g f : Expr) (proof : Derivation (.mul c g) f)
    (equation : eval o point f = o.zero) (coefficient : eval o point c ≠ o.zero)
    (nonzero : eval o point g ≠ o.zero) : False :=
  nonzero (cancellation laws domain point c g f proof equation coefficient)

def cancelCoefficient : Expr := .add .one .one
def cancelGenerator : Expr := .var 0
def cancelEquation : Expr := .mul cancelCoefficient cancelGenerator

theorem cancel_derivation : Derivation (.mul cancelCoefficient cancelGenerator)
    cancelEquation := .refl _

theorem integer_domain : DomainProfile integers :=
  ⟨by decide, fun _ _ h => Int.mul_eq_zero.mp h⟩

theorem integer_cancel (x : Int) (h : 2*x = 0) : x = 0 :=
  cancellation integer_laws integer_domain.2 (fun _ => x)
    cancelCoefficient cancelGenerator cancelEquation cancel_derivation h (by change (2 : Int) ≠ 0; decide)

def modFour : Operations (Fin 4) := {
  zero := 0, one := 1, add := (· + ·), mul := (· * ·), neg := (- ·)
}

theorem modFour_laws : Laws modFour := by constructor <;> decide

theorem cancellation_deletion_countermodel :
    modFour.one ≠ modFour.zero ∧
    eval modFour (fun _ => 2) cancelCoefficient ≠ modFour.zero ∧
    eval modFour (fun _ => 2) cancelEquation = modFour.zero ∧
    eval modFour (fun _ => 2) cancelGenerator ≠ modFour.zero := by decide

def modTwo : Operations (Fin 2) := {
  zero := 0, one := 1, add := (· + ·), mul := (· * ·), neg := (- ·)
}

theorem modTwo_laws : Laws modTwo := by constructor <;> decide
theorem modTwo_domain : DomainProfile modTwo := by
  constructor
  · decide
  · unfold NoZeroDivisors; decide

theorem modTwo_not_ordered : ¬ Nonempty (Ordering modTwo) := by
  rintro ⟨order⟩
  exact order.negative_one_not_nonnegative (order.square_nonnegative 1)

theorem ordered_nontrivial (laws : Laws o) (order : Ordering o) : o.one ≠ o.zero := by
  intro h
  have negZero : o.neg o.zero = o.zero :=
    (laws.zero_add (o.neg o.zero)).symm.trans (laws.add_neg o.zero)
  apply order.negative_one_not_nonnegative
  rw [h, negZero]
  exact order.zero_nonnegative

/-- Componentwise product, with a cone that observes just the first component.
The SOS Ordering interface is weaker than a linearly ordered domain. -/
def productIntegers : Operations (Int × Int) := {
  zero := (0,0), one := (1,1)
  add := fun a b => (a.1+b.1,a.2+b.2)
  mul := fun a b => (a.1*b.1,a.2*b.2)
  neg := fun a => (-a.1,-a.2)
}

theorem product_laws : Laws productIntegers := {
  add_assoc := by intros; simp [productIntegers, Int.add_assoc]
  add_zero := by intro a; cases a; simp [productIntegers]
  zero_add := by intro a; cases a; simp [productIntegers]
  add_neg := by intros; simp [productIntegers, Int.add_right_neg]
  neg_add := by intros; simp [productIntegers, Int.neg_add]
  neg_one_mul := by intros; simp [productIntegers]
  mul_zero := by intros; simp [productIntegers]
  one_mul := by intro a; cases a; simp [productIntegers]
}

def product_order : Ordering productIntegers := {
  nonnegative := fun a => integer_order.nonnegative a.1
  zero_nonnegative := integer_order.zero_nonnegative
  add_nonnegative := fun a b => integer_order.add_nonnegative a.1 b.1
  square_nonnegative := fun a => integer_order.square_nonnegative a.1
  negative_one_not_nonnegative := integer_order.negative_one_not_nonnegative
}

theorem product_not_domain : ¬ NoZeroDivisors productIntegers := by
  intro domain
  have bad := domain (1,0) (0,1) (by decide)
  cases bad with
  | inl h => cases h
  | inr h => cases h

/-- A retained ordered-interpreter countermodel in the full Laws class. -/
theorem modTwo_sos_countermodel :
    sample.Holds modTwo (fun _ => 1) ∧
    eval modTwo (fun _ => 1) sample.rhs = eval modTwo (fun _ => 1) (.neg .one) := by
  constructor
  · intro term member
    simp only [sample, List.mem_cons, List.not_mem_nil, or_false] at member
    subst term
    decide
  · decide
theorem zeroAlgebra_no_zero_divisors : NoZeroDivisors zeroAlgebra := by
  intro a b h
  exact Or.inl (Subsingleton.elim _ _)

theorem zeroAlgebra_not_nontrivial : ¬ zeroAlgebra.one ≠ zeroAlgebra.zero := by decide

theorem modFour_not_no_zero_divisors : ¬ NoZeroDivisors modFour := by
  intro h
  have bad := h 2 2 (by decide)
  rcases bad with h | h <;> cases h

end GrandPortage.CertificateInterpreter
