/- Read-only specification. No parser, replay, or freshness theorem is assumed proved. -/
import GrandPortage.CancellationInterpreter

namespace GrandPortage.IR
open CertificateInterpreter

inductive ClaimKind where
  | empty | nonempty | predicate | identity
  deriving DecidableEq, Repr
inductive Direction where
  | along | against
  deriving DecidableEq, Repr
inductive PointUniverse where
  | base | algebraicClosure | realClosure
  deriving DecidableEq, Repr

/-- Predicate references name externally interpreted syntax; they are not proofs. -/
inductive Statement : ClaimKind → Type where
  | empty : Statement .empty
  | nonempty : Statement .nonempty
  | predicate (syntaxReference : String) : Statement .predicate
  | identity (lhs rhs : Expr) : Statement .identity

structure Context (Selection : Type) where
  model : String
  about : Atlas.About
  coefficientDomain : String
  pointUniverse : PointUniverse
  selected : Option Selection
  ringVariables : List String
  equations : List Expr
  guards : List Expr

/-- Vocabulary is model-indexed and abstract: no unproved global lattice. -/
structure Claim (Vocabulary : String → Type) (Selection : Type) where
  context : Context Selection
  kind : ClaimKind
  statement : Statement kind
  vocabulary : Vocabulary context.model

abbrev Relation := String → String → Prop
structure RelationClass where
  name : String
  admits : Relation → Prop

def leftTotal (r : Relation) : Prop := ∀ a, ∃ b, r a b
def rightTotal (r : Relation) : Prop := ∀ b, ∃ a, r a b
/-- These are relation-class instances, not a replacement runtime table.
Strings stand for encoded states; state encoding is an interpretation premise. -/
def equivalenceClass : RelationClass := ⟨"EQUIVALENCE", fun r => leftTotal r ∧ rightTotal r⟩
def necessaryClass : RelationClass := ⟨"NECESSARY_CONDITION", leftTotal⟩
def restrictionClass : RelationClass := ⟨"RESTRICTION", leftTotal⟩
def baseExtensionClass (fieldMap : Relation → Prop) : RelationClass :=
  ⟨"BASE_EXTENSION", fun r => leftTotal r ∧ fieldMap r⟩
def imageClosureClass (geometric : Relation → Prop) : RelationClass :=
  ⟨"IMAGE_CLOSURE", geometric⟩
def specializationClass (integralPresentation : Relation → Prop) : RelationClass :=
  ⟨"SPECIALIZATION", integralPresentation⟩

structure ExecutionIdentity where
  artifact : String
  semanticInput : String
  program : String
  binaryIdentity : String
  completionIdentity : String
  deriving DecidableEq
structure Binding where
  endpoints : List String
  payloadIdentity : String
  graphState : String
  executions : List ExecutionIdentity
  deriving DecidableEq

structure Evidence (Requirement : Type) where
  artifact : String
  interpreter : String
  discharges : Requirement → Prop
  /-- Absence of a discharge is not automatically refutation. -/
  countermodels : List (Requirement × String)
  receipt : String
  binding : Binding

structure Step (Requirement : Type) where
  source : String
  target : String
  relationClass : RelationClass
  relation : Relation
  direction : Direction
  /-- Incomparable sufficient requirement sets remain distinct alternatives. -/
  profile : ClaimKind → Direction → (Requirement → Prop) → Prop
  available : Requirement → Prop
  binding : Binding

abbrev Subset {A : Type} (p q : A → Prop) := ∀ a, p a → q a

def Covered {R : Type} (s : Step R) (kind : ClaimKind) : Prop :=
  ∃ needs, s.profile kind s.direction needs ∧ Subset needs s.available

/-- Diagnostic loss = no admitted transport under current discharge, not
irrecoverable semantic information destruction. Available evidence is in Step. -/
def lost {R : Type} (s : Step R) (v : ClaimKind → Prop) : ClaimKind → Prop :=
  fun kind => v kind ∧ ¬ Covered s kind

theorem covered_not_lost {R : Type} (s : Step R) (v : ClaimKind → Prop)
    (kind : ClaimKind) (covered : Covered s kind) : ¬ lost s v kind :=
  fun h => h.2 covered

/-- The atlas polarity applies to arbitrary conditional profiles, once the
available-premise interpretation is fixed. -/
theorem profile_polarity {R : Type} (steps : Step R → Prop) (kinds : ClaimKind → Prop) :
    PredicateLe kinds (Atlas.commonClaims Covered steps) ↔
    PredicateLe steps (Atlas.commonOperations Covered kinds) :=
  Atlas.preservation_polarity Covered steps kinds

variable {Vocabulary : String → Type} {Selection Requirement : Type}

/-- Nonlocal nodes keep fresh binding for every premise and for the whole step. -/
def NonlocalReady
    (expresses : Claim Vocabulary Selection → Prop)
    (receiptValid : Evidence Requirement → Prop) (current : Binding → Prop)
    (bindsClaim : Binding → Claim Vocabulary Selection → Prop)
    (bindsStep : Binding → Step Requirement → List (Claim Vocabulary Selection) → Claim Vocabulary Selection → Prop)
    (c : Claim Vocabulary Selection) (ps : List (Claim Vocabulary Selection))
    (s : Step Requirement) (e : Evidence Requirement) : Prop :=
  expresses c ∧ Covered s c.kind ∧ receiptValid e ∧ current e.binding ∧
  current s.binding ∧ bindsStep e.binding s ps c ∧ bindsStep s.binding s ps c ∧
  (∀ p ∈ ps, ∃ b, current b ∧ bindsClaim b p) ∧
  s.relationClass.admits s.relation ∧ c.context.model = s.target ∧
  (∃ needs, s.profile c.kind s.direction needs ∧ Subset needs e.discharges ∧ Subset e.discharges s.available)

/-- Each proof-tree constructor retains evidence and the exact current binding.
Binding predicates are external obligations, never discharged by a matching tag. -/
inductive Licence
    (expresses : (Claim Vocabulary Selection) → Prop)
    (receiptValid : Evidence Requirement → Prop)
    (current : Binding → Prop)
    (bindsClaim : Binding → (Claim Vocabulary Selection) → Prop)
    (bindsStep : Binding → Step Requirement → List (Claim Vocabulary Selection) → (Claim Vocabulary Selection) → Prop) : (Claim Vocabulary Selection) → Prop where
  | leaf (c : (Claim Vocabulary Selection)) (e : Evidence Requirement)
      (typed : expresses c) (checked : receiptValid e)
      (fresh : current e.binding) (bound : bindsClaim e.binding c) :
      Licence expresses receiptValid current bindsClaim bindsStep c
  | step (c : (Claim Vocabulary Selection)) (premises : List (Claim Vocabulary Selection)) (s : Step Requirement) (e : Evidence Requirement)
      (children : ∀ p ∈ premises, Licence expresses receiptValid current bindsClaim bindsStep p)
      (nonempty : premises ≠ [])
      (sources : ∀ p ∈ premises, p.context.model = s.source)
      (target : c.context.model = s.target)
      (related : s.relationClass.admits s.relation)
      (typed : expresses c)
      (needs : Requirement → Prop) (profile : s.profile c.kind s.direction needs)
      (discharged : Subset needs e.discharges) (available : Subset e.discharges s.available)
      (checked : receiptValid e) (freshEvidence : current e.binding)
      (freshStep : current s.binding)
      (boundEvidence : bindsStep e.binding s premises c)
      (boundStep : bindsStep s.binding s premises c) :
      Licence expresses receiptValid current bindsClaim bindsStep c

  | partition (c cover : Claim Vocabulary Selection) (ps : List (Claim Vocabulary Selection))
      (s : Step Requirement) (e : Evidence Requirement)
      (kind : c.kind = .empty ∨ c.kind = .predicate)
      (children : ∀ p ∈ ps, Licence expresses receiptValid current bindsClaim bindsStep p)
      (coverageLicence : Licence expresses receiptValid current bindsClaim bindsStep cover)
      (covers : Claim Vocabulary Selection → List (Claim Vocabulary Selection) → Claim Vocabulary Selection → Prop)
      (coverage : covers cover ps c)
      (ready : NonlocalReady expresses receiptValid current bindsClaim bindsStep c ps s e) :
      Licence expresses receiptValid current bindsClaim bindsStep c
  | family (c familyClaim : Claim Vocabulary Selection) (s : Step Requirement) (e : Evidence Requirement)
      (familyLicence : Licence expresses receiptValid current bindsClaim bindsStep familyClaim)
      (members proved : String → Prop) (member : String)
      (allProved : ∀ i, members i → proved i) (listed : members member)
      (ready : NonlocalReady expresses receiptValid current bindsClaim bindsStep c [familyClaim] s e) :
      Licence expresses receiptValid current bindsClaim bindsStep c

/-- Each nonlocal constructor explicitly requires the same admission intersection. -/
theorem partition_admission
    (expresses : Claim Vocabulary Selection → Prop) (receiptValid : Evidence Requirement → Prop)
    (current : Binding → Prop) (bindsClaim : Binding → Claim Vocabulary Selection → Prop)
    (bindsStep : Binding → Step Requirement → List (Claim Vocabulary Selection) → Claim Vocabulary Selection → Prop)
    (c : Claim Vocabulary Selection) (ps : List (Claim Vocabulary Selection))
    (s : Step Requirement) (e : Evidence Requirement)
    (ready : NonlocalReady expresses receiptValid current bindsClaim bindsStep c ps s e) :
    expresses c ∧ Covered s c.kind := ⟨ready.1, ready.2.1⟩

theorem family_admission
    (expresses : Claim Vocabulary Selection → Prop) (receiptValid : Evidence Requirement → Prop)
    (current : Binding → Prop) (bindsClaim : Binding → Claim Vocabulary Selection → Prop)
    (bindsStep : Binding → Step Requirement → List (Claim Vocabulary Selection) → Claim Vocabulary Selection → Prop)
    (c familyClaim : Claim Vocabulary Selection) (s : Step Requirement) (e : Evidence Requirement)
    (ready : NonlocalReady expresses receiptValid current bindsClaim bindsStep c [familyClaim] s e) :
    expresses c ∧ Covered s c.kind := ⟨ready.1, ready.2.1⟩

/-- Actual exhaustive-partition EMPTY semantics; coverage is a supplied proof. -/
theorem partition_empty {X Index : Type} (parent : X → Prop) (branch : Index → X → Prop)
    (coverage : ∀ x, parent x → ∃ i, branch i x)
    (empty : ∀ i x, ¬ branch i x) : ∀ x, ¬ parent x := by
  intro x hx
  obtain ⟨i, hi⟩ := coverage x hx
  exact empty i x hi

/-- Predicate elimination uses the same coverage premise with pointwise truth. -/
theorem partition_predicate {X Index : Type} (parent : X → Prop) (branch : Index → X → Prop)
    (predicate : X → Prop) (coverage : ∀ x, parent x → ∃ i, branch i x)
    (holds : ∀ i x, branch i x → predicate x) : ∀ x, parent x → predicate x := by
  intro x hx
  obtain ⟨i, hi⟩ := coverage x hx
  exact holds i x hi

theorem family_reindex {Index Other : Type} (f : Other → Index) (members proved : Index → Prop)
    (allProved : ∀ i, members i → proved i) : ∀ j, members (f j) → proved (f j) :=
  Atlas.reindex_forall f (fun i => members i → proved i) allProved

/-- If coverage is dropped, an empty reported branch says nothing about another branch. -/
theorem missing_partition_branch_countermodel :
    (∀ x : Bool, x = false → ¬ (x = true)) ∧ (∃ x : Bool, x = true) := by
  constructor
  · intro x h; cases h; decide
  · exact ⟨true, rfl⟩

/-- The intersection theorem is stated at a step constructor, where the step
is known. A leaf licence need not name any transport step. -/
theorem licence_step_admission (s : Step Requirement) (c : (Claim Vocabulary Selection))
    (expresses : (Claim Vocabulary Selection) → Prop) (typed : expresses c) (needs : Requirement → Prop)
    (profile : s.profile c.kind s.direction needs) (e : Evidence Requirement)
    (discharged : Subset needs e.discharges) (available : Subset e.discharges s.available) :
    expresses c ∧ Covered s c.kind ∧ ¬ lost s (fun _ => expresses c) c.kind := by
  have covered : Covered s c.kind :=
    ⟨needs, profile, fun r hr => available r (discharged r hr)⟩
  exact ⟨typed, covered, covered_not_lost s _ _ covered⟩

/-- Spec-level soundness by induction. Leaf interpretation/replay and each
step's mathematical preservation/binding theorem are hypotheses. In particular,
this is not a theorem that the current Python parser or binder is correct. -/
theorem sound (interpret expresses : (Claim Vocabulary Selection) → Prop)
    (receiptValid : Evidence Requirement → Prop) (current : Binding → Prop)
    (bindsClaim : Binding → (Claim Vocabulary Selection) → Prop)
    (bindsStep : Binding → Step Requirement → List (Claim Vocabulary Selection) → (Claim Vocabulary Selection) → Prop)
    (leafSound : ∀ c e, expresses c → receiptValid e → current e.binding →
      bindsClaim e.binding c → interpret c)
    (stepSound : ∀ c premises (s : Step Requirement) (e : Evidence Requirement),
      (∀ p ∈ premises, interpret p) → premises ≠ [] →
      (∀ p ∈ premises, p.context.model = s.source) → c.context.model = s.target →
      s.relationClass.admits s.relation → expresses c → Covered s c.kind → receiptValid e → current e.binding →
      current s.binding → bindsStep e.binding s premises c →
      bindsStep s.binding s premises c → interpret c)
    (partitionSound : ∀ c cover ps (s : Step Requirement) (e : Evidence Requirement)
      (covers : Claim Vocabulary Selection → List (Claim Vocabulary Selection) → Claim Vocabulary Selection → Prop),
      (c.kind = .empty ∨ c.kind = .predicate) → (∀ p ∈ ps, interpret p) → interpret cover →
      covers cover ps c → NonlocalReady expresses receiptValid current bindsClaim bindsStep c ps s e → interpret c)
    (familySound : ∀ c familyClaim (s : Step Requirement) (e : Evidence Requirement)
      (members proved : String → Prop) member,
      interpret familyClaim → members member → proved member →
      NonlocalReady expresses receiptValid current bindsClaim bindsStep c [familyClaim] s e → interpret c)
    (c : (Claim Vocabulary Selection)) (licence : Licence expresses receiptValid current bindsClaim bindsStep c) :
    interpret c := by
  induction licence with
  | leaf c e typed checked fresh bound => exact leafSound c e typed checked fresh bound
  | step c ps s e children nonempty sources target related typed needs profile discharged available
      checked freshEvidence freshStep boundEvidence boundStep ih =>
    exact stepSound c ps s e ih nonempty sources target related typed
      ⟨needs, profile, fun r hr => available r (discharged r hr)⟩
      checked freshEvidence freshStep boundEvidence boundStep

  | partition c cover ps s e kind children coverageLicence covers coverage ready ih coverIH =>
    exact partitionSound c cover ps s e covers kind ih coverIH coverage ready
  | family c fc s e familyLicence members proved member allProved listed ready ih =>
    exact familySound c fc s e members proved member ih listed
      (Atlas.family_member members proved allProved member listed) ready

end GrandPortage.IR
