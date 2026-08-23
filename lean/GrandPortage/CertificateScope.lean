/-
# Certificate scope as a stability theorem

The runtime says scope is derived from certificate kind. This file turns the
two-level version of that rule into an admission interface: a certificate kind
must carry either a proof that its validity survives every declared extension,
or a counterexample showing that it does not. The derived scope is then the
maximal class justified by that decision.

This remains a non-authoritative semantic shadow. It neither reads the Python
registry nor blesses a runtime declaration.
-/

namespace GrandPortage

universe u v

inductive CertificateScope where
  | fieldRelative
  | scheme
  deriving DecidableEq

def CertificateScope.le : CertificateScope -> CertificateScope -> Prop
  | .fieldRelative, _ => True
  | .scheme, .scheme => True
  | .scheme, .fieldRelative => False

def StableUnder {Context : Type u} {Certificate : Type v}
    (extension : Context -> Context -> Prop)
    (valid : Context -> Certificate -> Prop) : Prop :=
  forall source target, extension source target ->
    forall certificate, valid source certificate -> valid target certificate

theorem stableUnder_sameContext
    {Context : Type u} {Certificate : Type v}
    (valid : Context -> Certificate -> Prop) :
    StableUnder (fun source target => source = target) valid := by
  intro source target equal certificate sourceValid
  cases equal
  exact sourceValid

/-- Admission requires a theorem or a refuting instance, never a Boolean. -/
inductive StabilityDecision
    {Context : Type u} {Certificate : Type v}
    (extension : Context -> Context -> Prop)
    (valid : Context -> Certificate -> Prop) where
  | stable (proof : StableUnder extension valid)
  | unstable (counterexample : Not (StableUnder extension valid))

def derivedCertificateScope
    {Context : Type u} {Certificate : Type v}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (decision : StabilityDecision extension valid) : CertificateScope :=
  match decision with
  | .stable _ => .scheme
  | .unstable _ => .fieldRelative

def ScopeAdmissible
    {Context : Type u} {Certificate : Type v}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (_decision : StabilityDecision extension valid) : CertificateScope -> Prop
  | .fieldRelative => True
  | .scheme => StableUnder extension valid

theorem derivedCertificateScope_admissible
    {Context : Type u} {Certificate : Type v}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (decision : StabilityDecision extension valid) :
    ScopeAdmissible decision (derivedCertificateScope decision) := by
  cases decision with
  | stable proof => exact proof
  | unstable _ => trivial

/-- The derived scope is maximal in the two-level lattice. -/
theorem derivedCertificateScope_maximal
    {Context : Type u} {Certificate : Type v}
    {extension : Context -> Context -> Prop}
    {valid : Context -> Certificate -> Prop}
    (decision : StabilityDecision extension valid)
    (requested : CertificateScope)
    (admissible : ScopeAdmissible decision requested) :
    CertificateScope.le requested (derivedCertificateScope decision) := by
  cases decision with
  | stable _ =>
      cases requested <;> trivial
  | unstable counterexample =>
      cases requested with
      | fieldRelative => trivial
      | scheme => exact False.elim (counterexample admissible)

/-! ## Positive and negative certificate shapes -/

/-- Exact identities are functorial under every map. -/
theorem exactIdentity_stable_under_map
    {R : Type u} {S : Type v} (map : R -> S) {left right : R} :
    left = right -> map left = map right :=
  congrArg map

def NoWitness {Point : Type u} (predicate : Point -> Prop) : Prop :=
  forall point, Not (predicate point)

/-- Negative existential evidence can be destroyed by adding a witness. -/
theorem noWitness_not_stable_under_carrier_extension :
    let basePredicate : Empty -> Prop := fun point => point.elim
    let extendedPredicate : Unit -> Prop := fun _ => True
    NoWitness basePredicate /\
      Not (NoWitness extendedPredicate) := by
  dsimp
  constructor
  · intro point
    exact point.elim
  · intro noWitness
    exact noWitness () True.intro

/-! ## Executable two-row registry model -/

def ExampleExtends : Bool -> Bool -> Prop
  | false, false => True
  | false, true => True
  | true, true => True
  | true, false => False

def StableExample (_context : Bool) (_certificate : Unit) : Prop := True

def FragileExample : Bool -> Unit -> Prop
  | false, _ => True
  | true, _ => False

theorem stableExample_survives :
    StableUnder ExampleExtends StableExample := by
  intro _source _target _extends _certificate _valid
  trivial

theorem fragileExample_fails_extension :
    Not (StableUnder ExampleExtends FragileExample) := by
  intro stable
  exact stable false true True.intro () True.intro

def stableExampleDecision :
    StabilityDecision ExampleExtends StableExample :=
  .stable stableExample_survives

def fragileExampleDecision :
    StabilityDecision ExampleExtends FragileExample :=
  .unstable fragileExample_fails_extension

theorem stableExample_has_scheme_scope :
    derivedCertificateScope stableExampleDecision = .scheme := rfl

theorem fragileExample_is_fieldRelative :
    derivedCertificateScope fragileExampleDecision = .fieldRelative := rfl

end GrandPortage
