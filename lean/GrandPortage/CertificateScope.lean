/-
# Runtime certificate scope as a stability theorem

The Python kernel derives EMPTY scope from certificate kind. Scheme scope is
licensed only when validity survives every declared coefficient extension;
otherwise the author must name one exact field. This file models that actual
atom-under-scheme poset and supplies a theorem or countermodel for every
builtin runtime certificate kind.

This remains a non-authoritative semantic shadow. Python/Lean drift tests
compare names and derived rows; this file does not read or bless a graph.
-/

namespace GrandPortage

universe u v

inductive CertificateScope (FieldId : Type u) where
  | fieldRelative (field : FieldId)
  | scheme
  deriving DecidableEq

/-- Exact field scopes are incomparable atoms below field-independent scope. -/
def CertificateScope.le {FieldId : Type u} [DecidableEq FieldId] :
    CertificateScope FieldId -> CertificateScope FieldId -> Prop
  | .fieldRelative source, .fieldRelative target => source = target
  | .fieldRelative _, .scheme => True
  | .scheme, .scheme => True
  | .scheme, .fieldRelative _ => False

def StableUnder {Context : Type u} {Certificate : Type v}
    (extension : Context -> Context -> Prop)
    (valid : Context -> Certificate -> Prop) : Prop :=
  forall source target, extension source target ->
    forall certificate, valid source certificate -> valid target certificate

/-- Admission requires a theorem or a refuting instance, never a Boolean. -/
inductive StabilityDecision
    {Context : Type u} {Certificate : Type v}
    (extension : Context -> Context -> Prop)
    (valid : Context -> Certificate -> Prop) where
  | stable (proof : StableUnder extension valid)
  | unstable (counterexample : Not (StableUnder extension valid))

def derivedCertificateScope
    {FieldId : Type u} {Context : Type v} {Certificate : Type _}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (field : FieldId)
    (decision : StabilityDecision extension valid) : CertificateScope FieldId :=
  match decision with
  | .stable _ => .scheme
  | .unstable _ => .fieldRelative field

/-- For an unstable kind, only the exact declared field is admissible. -/
def ScopeAdmissible
    {FieldId : Type u} [DecidableEq FieldId]
    {Context : Type v} {Certificate : Type _}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (field : FieldId)
    (_decision : StabilityDecision extension valid) :
    CertificateScope FieldId -> Prop
  | .fieldRelative requested => requested = field
  | .scheme => StableUnder extension valid

theorem derivedCertificateScope_admissible
    {FieldId : Type u} [DecidableEq FieldId]
    {Context : Type v} {Certificate : Type _}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (field : FieldId)
    (decision : StabilityDecision extension valid) :
    ScopeAdmissible field decision (derivedCertificateScope field decision) := by
  cases decision with
  | stable proof => exact proof
  | unstable _ => rfl

/-- The runtime-derived scope is maximal among scopes justified at this field. -/
theorem derivedCertificateScope_maximal
    {FieldId : Type u} [DecidableEq FieldId]
    {Context : Type v} {Certificate : Type _}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (field : FieldId)
    (decision : StabilityDecision extension valid)
    (requested : CertificateScope FieldId)
    (admissible : ScopeAdmissible field decision requested) :
    CertificateScope.le requested
      (derivedCertificateScope field decision) := by
  cases decision with
  | stable _ =>
      cases requested <;> trivial
  | unstable counterexample =>
      cases requested with
      | fieldRelative requested => exact admissible
      | scheme => exact False.elim (counterexample admissible)

/-! ## Algebraic premises carried by stable certificate shapes -/

/-- Mathlib-free interface for the facts coefficient extension must preserve. -/
structure AlgebraicContext where
  unitIdeal : Prop
  localizedUnitIdeal : Prop
  nonzeroResultant : Prop

structure AlgebraicExtension (source target : AlgebraicContext) : Prop where
  unitIdeal : source.unitIdeal -> target.unitIdeal
  localizedUnitIdeal : source.localizedUnitIdeal -> target.localizedUnitIdeal
  nonzeroResultant : source.nonzeroResultant -> target.nonzeroResultant

def UnitIdealValid (context : AlgebraicContext) (_certificate : Unit) : Prop :=
  context.unitIdeal

def LocalizedUnitIdealValid
    (context : AlgebraicContext) (_certificate : Unit) : Prop :=
  context.localizedUnitIdeal

def NonzeroResultantValid
    (context : AlgebraicContext) (_certificate : Unit) : Prop :=
  context.nonzeroResultant

theorem unitIdeal_stable :
    StableUnder AlgebraicExtension UnitIdealValid := by
  intro source target extension _certificate valid
  exact extension.unitIdeal valid

theorem localizedUnitIdeal_stable :
    StableUnder AlgebraicExtension LocalizedUnitIdealValid := by
  intro source target extension _certificate valid
  exact extension.localizedUnitIdeal valid

theorem nonzeroResultant_stable :
    StableUnder AlgebraicExtension NonzeroResultantValid := by
  intro source target extension _certificate valid
  exact extension.nonzeroResultant valid

/-- Valuation collisions and degree counts are integer statements. -/
def IntegerStatementValid (_context : Unit) (_certificate : Unit) : Prop := True

theorem integerStatement_stable :
    StableUnder (fun (_source _target : Unit) => True) IntegerStatementValid := by
  intro _source _target _extension _certificate _valid
  trivial

/-! ## Retained countermodels for field-relative/refusal shapes -/

def FieldExtends : Bool -> Bool -> Prop
  | false, false => True
  | false, true => True
  | true, true => True
  | true, false => False

/-- `false` is the base field; `true` adjoins the missing witness/root. -/
def NonsquareClassValid : Bool -> Unit -> Prop
  | false, _ => True
  | true, _ => False

def NoRationalPointSearchValid : Bool -> Unit -> Prop
  | false, _ => True
  | true, _ => False

/-- A citation recorded only at its stated field carries no extension proof. -/
def CitedProofValid : Bool -> Unit -> Prop
  | false, _ => True
  | true, _ => False

theorem fragileFieldEvidence_not_stable
    (valid : Bool -> Unit -> Prop)
    (baseValid : valid false ())
    (extendedInvalid : Not (valid true ())) :
    Not (StableUnder FieldExtends valid) := by
  intro stable
  exact extendedInvalid (stable false true True.intro () baseValid)

theorem nonsquareClass_not_stable :
    Not (StableUnder FieldExtends NonsquareClassValid) :=
  fragileFieldEvidence_not_stable NonsquareClassValid True.intro
    (by simp [NonsquareClassValid])

theorem noRationalPointSearch_not_stable :
    Not (StableUnder FieldExtends NoRationalPointSearchValid) :=
  fragileFieldEvidence_not_stable NoRationalPointSearchValid True.intro
    (by simp [NoRationalPointSearchValid])

theorem citedProof_not_stable :
    Not (StableUnder FieldExtends CitedProofValid) :=
  fragileFieldEvidence_not_stable CitedProofValid True.intro
    (by simp [CitedProofValid])

/-! ## One named decision for every Python builtin certificate kind -/

def unitIdealDecision : StabilityDecision AlgebraicExtension UnitIdealValid :=
  .stable unitIdeal_stable

def localizedUnitIdealDecision :
    StabilityDecision AlgebraicExtension LocalizedUnitIdealValid :=
  .stable localizedUnitIdeal_stable

def nonzeroResultantDecision :
    StabilityDecision AlgebraicExtension NonzeroResultantValid :=
  .stable nonzeroResultant_stable

def exactValuationCollisionDecision :
    StabilityDecision (fun (_source _target : Unit) => True)
      IntegerStatementValid :=
  .stable integerStatement_stable

def degreeCountDecision :
    StabilityDecision (fun (_source _target : Unit) => True)
      IntegerStatementValid :=
  .stable integerStatement_stable

def nonsquareClassDecision :
    StabilityDecision FieldExtends NonsquareClassValid :=
  .unstable nonsquareClass_not_stable

def noRationalPointSearchDecision :
    StabilityDecision FieldExtends NoRationalPointSearchValid :=
  .unstable noRationalPointSearch_not_stable

def citedProofDecision : StabilityDecision FieldExtends CitedProofValid :=
  .unstable citedProof_not_stable

theorem unitIdeal_scope (field : String) :
    derivedCertificateScope field unitIdealDecision = .scheme := rfl

theorem localizedUnitIdeal_scope (field : String) :
    derivedCertificateScope field localizedUnitIdealDecision = .scheme := rfl

theorem nonzeroResultant_scope (field : String) :
    derivedCertificateScope field nonzeroResultantDecision = .scheme := rfl

theorem exactValuationCollision_scope (field : String) :
    derivedCertificateScope field exactValuationCollisionDecision = .scheme := rfl

theorem degreeCount_scope (field : String) :
    derivedCertificateScope field degreeCountDecision = .scheme := rfl

theorem nonsquareClass_scope (field : String) :
    derivedCertificateScope field nonsquareClassDecision =
      .fieldRelative field := rfl

theorem noRationalPointSearch_scope (field : String) :
    derivedCertificateScope field noRationalPointSearchDecision =
      .fieldRelative field := rfl

theorem citedProof_scope (field : String) :
    derivedCertificateScope field citedProofDecision =
      .fieldRelative field := rfl

end GrandPortage
