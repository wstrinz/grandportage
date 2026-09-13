import GrandPortage.ExpressionTransport

namespace GrandPortage.CertificateInterpreter

universe u
variable {Value : Type u} {o : Operations Value}

def unitRhs (terms : List (Expr × Expr)) : Expr :=
  sumExpr (terms.map fun (h, f) => .mul h f)

def equationsHold (terms : List (Expr × Expr)) (o : Operations Value)
    (point : Nat → Value) : Prop :=
  ∀ term ∈ terms, eval o point term.2 = o.zero

theorem unit_terms_zero (laws : Laws o) (terms : List (Expr × Expr))
    (point : Nat → Value) (holds : equationsHold terms o point) :
    eval o point (unitRhs terms) = o.zero := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
    have head := holds term (by simp)
    have tail : equationsHold rest o point := by
      intro t member
      exact holds t (by simp [member])
    simp only [unitRhs, List.map_cons, sumExpr, eval]
    rw [head, laws.mul_zero]
    change o.add o.zero (eval o point (unitRhs rest)) = o.zero
    rw [ih tail, laws.zero_add]

/-- Unit-ideal contradiction needs nontriviality, not an ordering or char zero.
Rational coefficients would impose separate denominator requirements. -/
theorem unit_certificate_empty (laws : Laws o) (nontrivial : o.one ≠ o.zero)
    (terms : List (Expr × Expr)) (proof : Derivation (unitRhs terms) .one)
    (point : Nat → Value) : ¬ equationsHold terms o point := by
  intro holds
  have replayed := derivation_sound laws point proof
  change eval o point (unitRhs terms) = o.one at replayed
  exact nontrivial (replayed.symm.trans (unit_terms_zero laws terms point holds))

def unitSample : List (Expr × Expr) :=
  [(.one, .var 0), (.one, .add (.neg (.var 0)) .one)]

theorem unit_sample_derivation : Derivation (unitRhs unitSample) .one := by
  change Derivation (.add (.mul .one (.var 0))
    (.add (.mul .one (.add (.neg (.var 0)) .one)) .zero)) .one
  apply Derivation.trans (Derivation.add (Derivation.oneMul _)
    (Derivation.trans (Derivation.addZero _) (Derivation.oneMul _)))
  apply Derivation.trans (Derivation.symm (Derivation.assoc _ _ _))
  apply Derivation.trans (Derivation.add (Derivation.cancel _) (Derivation.refl _))
  exact Derivation.zeroAdd _

theorem unit_integer_empty (point : Nat → Int) :
    ¬ equationsHold unitSample integers point :=
  unit_certificate_empty integer_laws (by decide) unitSample unit_sample_derivation point

/-- Deleting nontriviality admits the zero algebra, in the same Laws model class. -/
def zeroAlgebra : Operations Unit := {
  zero := (), one := (), add := fun _ _ => (),
  mul := fun _ _ => (), neg := fun _ => ()
}

theorem zeroAlgebra_laws : Laws zeroAlgebra := {
  add_assoc := by intros; rfl
  add_zero := by intro a; cases a; rfl
  zero_add := by intro a; cases a; rfl
  add_neg := by intros; rfl
  neg_add := by intros; rfl
  neg_one_mul := by intros; rfl
  mul_zero := by intros; rfl
  one_mul := by intro a; cases a; rfl
}

theorem nontriviality_deletion_countermodel :
    equationsHold unitSample zeroAlgebra (fun _ => ()) := by
  intro term member
  exact Subsingleton.elim _ _

end GrandPortage.CertificateInterpreter
