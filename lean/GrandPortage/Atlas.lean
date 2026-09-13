/-
# Preservation atlas: logical laws and epoch-12 reach

Non-authoritative. See docs/ATLAS-MAPPING-V0.md for sources and proof boundaries.
These are independently stated semantic laws, not imports of Isabelle or Trocq.
Parsed field tags are abstract here; Python owns primality and syntax validation.
-/
import GrandPortage.RelationalTransport
import GrandPortage.CertificateScope

namespace GrandPortage.Atlas

universe u v w

/-! ## Isabelle-style bounded relatedness

HOL types are inhabited, but GP solution sets need not be. Quantification is
therefore restricted to explicit model predicates. Uniqueness is unnecessary
for these laws; equality transfer is a separate problem.
-/

def RelatesImplies {α : Type u} {β : Type v}
    (R : PointRelation α β) (src : Model α) (dst : Model β)
    (P : α → Prop) (Q : β → Prop) : Prop :=
  ∀ x y, src x → dst y → R x y → P x → Q y

/-- Bounded version of the forward implication in Transfer.thy's
right_total_alt_def2; model predicates keep empty solution sets expressible. -/
theorem rightTotal_all_transfer {α : Type u} {β : Type v}
    {R : PointRelation α β} {src : Model α} {dst : Model β}
    {P : α → Prop} {Q : β → Prop}
    (total : RelationSurjectiveOn R src dst)
    (related : RelatesImplies R src dst P Q)
    (holds : Everywhere src P) : Everywhere dst Q := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := total y hy
  exact related x y hx hy hxy (holds x hx)

theorem leftTotal_exists_transfer {α : Type u} {β : Type v}
    {R : PointRelation α β} {src : Model α} {dst : Model β}
    {P : α → Prop} {Q : β → Prop}
    (total : RelationTotalOn R src dst)
    (related : RelatesImplies R src dst P Q)
    (holds : ∃ x, src x ∧ P x) : ∃ y, dst y ∧ Q y := by
  obtain ⟨x, hx, hp⟩ := holds
  obtain ⟨y, hy, hxy⟩ := total x hx
  exact ⟨y, hy, related x y hx hy hxy hp⟩

theorem necessary_empty_is_transfer {α : Type u} {src dst : Model α}
    (inclusion : Refines src dst) (empty : IsEmpty dst) : IsEmpty src :=
  relationTotal_isEmpty_against
    ((refines_iff_identityRelation_total src dst).mp inclusion) empty

/-! ## Witness custody is data, not just a Prop-level existential -/

structure PointWitness {α : Type u} (M : Model α) where
  point : α
  belongs : M point

def mapWitness {α : Type u} {β : Type v} {src : Model α} {dst : Model β}
    (f : α → β) (maps : ∀ x, src x → dst (f x))
    (witness : PointWitness src) : PointWitness dst :=
  ⟨f witness.point, maps witness.point witness.belongs⟩

theorem mapWitness_comp {α : Type u} {β : Type v} {γ : Type w}
    {src : Model α} {mid : Model β} {dst : Model γ}
    (f : α → β) (g : β → γ)
    (hf : ∀ x, src x → mid (f x)) (hg : ∀ y, mid y → dst (g y))
    (p : PointWitness src) :
    mapWitness g hg (mapWitness f hf p) =
      mapWitness (fun x => g (f x)) (fun x hx => hg (f x) (hf x hx)) p := rfl

/-- Nonempty source and target do not give a lift of a specified target point.
This finite countermodel isolates the obligation, not a Zariski topology. -/
theorem existence_does_not_lift_specified_point :
    HasPoint onlyA ∧ HasPoint both ∧
      ¬ (∃ x, onlyA x ∧ IdentityRelation Two x Two.b) := by
  refine ⟨⟨Two.a, rfl⟩, ⟨Two.b, trivial⟩, ?_⟩
  rintro ⟨x, hx, hxy⟩
  cases hxy
  cases hx

/-! ## Restricting stability and retaining unknown evidence -/

theorem stableUnder_restrict {Context : Type u} {Certificate : Type v}
    {small large : Context → Context → Prop}
    {valid : Context → Certificate → Prop}
    (included : ∀ x y, small x y → large x y)
    (stable : StableUnder large valid) : StableUnder small valid :=
  fun x y h => stable x y (included x y h)

/-- A registry may have no theorem and no countermodel. This is distinct from
the older two-way mathematical StabilityDecision admission experiment. -/
inductive StabilityKnowledge {Context : Type u} {Certificate : Type v}
    (extension : Context → Context → Prop) (valid : Context → Certificate → Prop)
  | proved (proof : StableUnder extension valid)
  | refuted (proof : ¬ StableUnder extension valid)
  | unknown

inductive ConcreteField where
  | q | r | c
  | primeField (characteristic : Nat)
  deriving DecidableEq, Repr

inductive About where
  | concrete (field : ConcreteField)
  | anyOrdered | anyChar0
  deriving DecidableEq, Repr

inductive Reach where
  | none | ordered | char0
  | fieldSpecific (field : ConcreteField)
  deriving DecidableEq, Repr

def isOrdered : ConcreteField → Bool
  | .q | .r => true
  | _ => false

def isChar0 : ConcreteField → Bool
  | .primeField _ => false
  | _ => true

/-- Denotation on the bounded concrete field vocabulary, not on all fields. -/
def reachHolds : Reach → ConcreteField → Bool
  | .none, _ => false
  | .ordered, f => isOrdered f
  | .char0, f => isChar0 f
  | .fieldSpecific source, target => source == target

def aboutHolds : About → ConcreteField → Bool
  | .concrete source, target => source == target
  | .anyOrdered, target => isOrdered target
  | .anyChar0, target => isChar0 target

def instantiate : Reach → About → Bool
  | reach, .concrete field => reachHolds reach field
  | .ordered, .anyOrdered => true
  | .char0, .anyOrdered | .char0, .anyChar0 => true
  | _, _ => false

/-- Successful quantified instantiation covers every concrete member.
Python/Lean parity is an additional executable gate, not part of this proof. -/
theorem instantiate_sound (reach : Reach) (target : About) (field : ConcreteField)
    (admitted : instantiate reach target = true)
    (member : aboutHolds target field = true) : reachHolds reach field = true := by
  cases target with
  | concrete source =>
      have eq : source = field := by simpa [aboutHolds] using member
      cases eq
      exact admitted
  | anyOrdered =>
      cases reach <;> cases field <;>
        simp_all [instantiate, aboutHolds, reachHolds, isOrdered, isChar0]
  | anyChar0 =>
      cases reach <;> cases field <;>
        simp_all [instantiate, aboutHolds, reachHolds, isChar0]

def concreteExtension (source target : ConcreteField) : Bool :=
  source == target || match source, target with
    | .q, .r | .q, .c | .r, .c => true
    | _, _ => false

def FieldExtends (source target : ConcreteField) : Prop :=
  concreteExtension source target = true

def Char0Extends (source target : ConcreteField) : Prop :=
  FieldExtends source target ∧ isChar0 source = true ∧ isChar0 target = true

def OrderedExtends (source target : ConcreteField) : Prop :=
  FieldExtends source target ∧ isOrdered source = true ∧ isOrdered target = true

theorem orderedExtends_char0Extends {source target : ConcreteField}
    (h : OrderedExtends source target) : Char0Extends source target := by
  cases source <;> cases target <;>
    simp_all [OrderedExtends, Char0Extends, isOrdered, isChar0]

theorem char0Extends_fieldExtends {source target : ConcreteField}
    (h : Char0Extends source target) : FieldExtends source target := h.1

theorem orderedReach_stable :
    StableUnder OrderedExtends (fun field (_ : Unit) => reachHolds .ordered field = true) :=
  fun _ _ h _ _ => h.2.2

theorem char0Reach_stable :
    StableUnder Char0Extends (fun field (_ : Unit) => reachHolds .char0 field = true) :=
  fun _ _ h _ _ => h.2.2

/-- This is a scope countermodel, not a proof that polynomial replay fails. -/
theorem orderedReach_not_fieldStable :
    ¬ StableUnder FieldExtends
      (fun field (_ : Unit) => reachHolds .ordered field = true) := by
  intro stable
  have bad := stable .r .c (by unfold FieldExtends; decide) () (by decide)
  cases bad

theorem instantiation_is_not_extension :
    instantiate .ordered (.concrete .q) = true ∧
    concreteExtension .r .q = false := by decide

theorem none_instantiates_nowhere (target : About) :
    instantiate .none target = false := by cases target <;> rfl

/-! ## Checked arithmetic versus ordered contradiction

The narrow interface below lists arithmetic laws, not an assumed emptiness
theorem. Polynomial parsing/replay and evaluation of an identity remain outside
this proof. Cofactor terms become zero only after evaluating model equations.
-/

structure OrderedArithmetic (Value : Type u) where
  zero : Value
  negativeOne : Value
  add : Value → Value → Value
  mul : Value → Value → Value
  nonnegative : Value → Prop
  zero_nonnegative : nonnegative zero
  add_nonnegative : ∀ a b, nonnegative a → nonnegative b → nonnegative (add a b)
  square_nonnegative : ∀ a, nonnegative (mul a a)
  add_zero : ∀ a, add a zero = a
  mul_zero : ∀ a, mul a zero = zero
  negativeOne_not_nonnegative : ¬ nonnegative negativeOne

def sumValues {Value : Type u} (a : OrderedArithmetic Value) : List Value → Value
  | [] => a.zero
  | x :: xs => a.add x (sumValues a xs)

theorem sum_squares_nonnegative {Value : Type u} (a : OrderedArithmetic Value)
    (squares : List Value) :
    a.nonnegative (sumValues a (squares.map (fun x => a.mul x x))) := by
  induction squares with
  | nil => exact a.zero_nonnegative
  | cons x xs ih => exact a.add_nonnegative _ _ (a.square_nonnegative x) ih

theorem sum_zero_terms {Value : Type u} (a : OrderedArithmetic Value)
    (terms : List Value) (zero : ∀ x ∈ terms, x = a.zero) :
    sumValues a terms = a.zero := by
  induction terms with
  | nil => rfl
  | cons x xs ih =>
      have hx := zero x (by simp)
      have ht := ih (fun y hy => zero y (by simp [hy]))
      simp only [sumValues, hx, ht, a.add_zero]

theorem orderedSOS_contradiction {Value : Type u} (a : OrderedArithmetic Value)
    (squares cofactorTerms : List Value)
    (equations : ∀ x ∈ cofactorTerms, x = a.zero)
    (replayed : a.negativeOne = a.add
      (sumValues a (squares.map (fun x => a.mul x x)))
      (sumValues a cofactorTerms)) : False := by
  rw [sum_zero_terms a cofactorTerms equations, a.add_zero] at replayed
  exact a.negativeOne_not_nonnegative (replayed ▸ sum_squares_nonnegative a squares)

/-- An identity is mapped as equality independently of an ordering. -/
theorem replayed_equality_survives {A : Type u} {B : Type v}
    (interpret : A → B) {lhs rhs : A} (replayed : lhs = rhs) :
    interpret lhs = interpret rhs := congrArg interpret replayed

/-! ## Reindexing an indexed family

This is the logical elimination rule. Exact enumeration, group evidence,
COUNT coverage and member/model binding are additional runtime obligations.
-/
theorem family_member {Index : Type u} (members proved : Index → Prop)
    (allProved : ∀ i, members i → proved i) (i : Index) (listed : members i) :
    proved i := allProved i listed

theorem reindex_forall {Index : Type u} {Other : Type v}
    (f : Other → Index) (P : Index → Prop) (holds : ∀ i, P i) :
    ∀ j, P (f j) := fun j => holds (f j)

/-! ## The atlas itself has an antitone preservation correspondence

This is the elementary polarity behind a table of transformations and claims.
It neither synthesizes transformations nor proves an unfilled table cell.
-/

def commonClaims {Operation : Type u} {Claim : Type v}
    (preserves : Operation → Claim → Prop) (operations : Operation → Prop) :
    Claim → Prop := fun claim => ∀ op, operations op → preserves op claim

def commonOperations {Operation : Type u} {Claim : Type v}
    (preserves : Operation → Claim → Prop) (claims : Claim → Prop) :
    Operation → Prop := fun op => ∀ claim, claims claim → preserves op claim

theorem preservation_polarity {Operation : Type u} {Claim : Type v}
    (preserves : Operation → Claim → Prop) (operations : Operation → Prop)
    (claims : Claim → Prop) :
    PredicateLe claims (commonClaims preserves operations) ↔
      PredicateLe operations (commonOperations preserves claims) := by
  constructor
  · intro h op ho claim hc
    exact h claim hc op ho
  · intro h claim hc op ho
    exact h op ho claim hc

theorem more_operations_fewer_common_claims {Operation : Type u} {Claim : Type v}
    (preserves : Operation → Claim → Prop) {small large : Operation → Prop}
    (included : PredicateLe small large) :
    PredicateLe (commonClaims preserves large) (commonClaims preserves small) :=
  fun _ h op ho => h op (included op ho)

/-! ## Nilpotents distinguish point observation from coordinate-ring equality -/

def dualMul (x y : Int × Int) : Int × Int :=
  (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

def epsilon : Int × Int := (0, 1)

theorem epsilon_nonzero_square_zero :
    epsilon ≠ (0, 0) ∧ dualMul epsilon epsilon = (0, 0) := by decide

/-- Every zero- and multiplication-preserving observation in a structure with
no nonzero square-zero elements kills epsilon. A field is such a structure;
the dual-number algebra itself is not. No general field theory is assumed. -/
theorem reduced_observation_kills_epsilon {Value : Type u}
    (zero : Value) (mul : Value → Value → Value)
    (squareZero : ∀ x, mul x x = zero → x = zero)
    (observe : (Int × Int) → Value)
    (hzero : observe (0, 0) = zero)
    (hmul : ∀ x y, observe (dualMul x y) = mul (observe x) (observe y)) :
    observe epsilon = zero := by
  apply squareZero
  rw [← hmul, epsilon_nonzero_square_zero.2, hzero]

end GrandPortage.Atlas
