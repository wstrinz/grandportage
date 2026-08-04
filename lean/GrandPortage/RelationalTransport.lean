/-
# Relational transport and predicate transformers

Model-changing operations need not be functions and need not preserve every
point. A binary relation is their common point-level semantic core.
-/

import GrandPortage.Points

namespace GrandPortage

universe u v w

def PointRelation (α : Type u) (β : Type v) := α → β → Prop

def PredicateLe {α : Type u} (P Q : α → Prop) : Prop :=
  ∀ x, P x → Q x

def ExistsImage {α : Type u} {β : Type v}
    (R : PointRelation α β) (P : α → Prop) : β → Prop :=
  fun y => ∃ x, P x ∧ R x y

def ForallPre {α : Type u} {β : Type v}
    (R : PointRelation α β) (Q : β → Prop) : α → Prop :=
  fun x => ∀ y, R x y → Q y

theorem existsImage_le_iff_le_forallPre
    {α : Type u} {β : Type v}
    (R : PointRelation α β) (P : α → Prop) (Q : β → Prop) :
    PredicateLe (ExistsImage R P) Q ↔ PredicateLe P (ForallPre R Q) := by
  constructor
  · intro imageLe x hx y hxy
    exact imageLe y ⟨x, hx, hxy⟩
  · intro preLe y
    rintro ⟨x, hx, hxy⟩
    exact preLe x hx y hxy

def IdentityRelation (α : Type u) : PointRelation α α :=
  fun x y => x = y

def RelationComp {α : Type u} {β : Type v} {γ : Type w}
    (R : PointRelation α β) (S : PointRelation β γ) :
    PointRelation α γ :=
  fun x z => ∃ y, R x y ∧ S y z

theorem existsImage_identity
    {α : Type u} (P : α → Prop) (x : α) :
    ExistsImage (IdentityRelation α) P x ↔ P x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem forallPre_identity
    {α : Type u} (P : α → Prop) (x : α) :
    ForallPre (IdentityRelation α) P x ↔ P x := by
  constructor
  · intro h
    exact h x rfl
  · intro hx y hxy
    cases hxy
    exact hx

theorem existsImage_comp
    {α : Type u} {β : Type v} {γ : Type w}
    (R : PointRelation α β) (S : PointRelation β γ)
    (P : α → Prop) (z : γ) :
    ExistsImage (RelationComp R S) P z ↔
      ExistsImage S (ExistsImage R P) z := by
  constructor
  · rintro ⟨x, hx, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hx, hxy⟩, hyz⟩
  · rintro ⟨y, ⟨x, hx, hxy⟩, hyz⟩
    exact ⟨x, hx, y, hxy, hyz⟩

theorem forallPre_comp
    {α : Type u} {β : Type v} {γ : Type w}
    (R : PointRelation α β) (S : PointRelation β γ)
    (Q : γ → Prop) (x : α) :
    ForallPre (RelationComp R S) Q x ↔
      ForallPre R (ForallPre S Q) x := by
  constructor
  · intro h y hxy z hyz
    exact h z ⟨y, hxy, hyz⟩
  · intro h z
    rintro ⟨y, hxy, hyz⟩
    exact h y hxy z hyz

def RelationTotalOn {α : Type u} {β : Type v}
    (R : PointRelation α β) (src : Model α) (dst : Model β) : Prop :=
  ∀ x, src x → ∃ y, dst y ∧ R x y

def RelationSurjectiveOn {α : Type u} {β : Type v}
    (R : PointRelation α β) (src : Model α) (dst : Model β) : Prop :=
  ∀ y, dst y → ∃ x, src x ∧ R x y

theorem relationTotal_hasPoint_along
    {α : Type u} {β : Type v}
    {R : PointRelation α β} {src : Model α} {dst : Model β}
    (total : RelationTotalOn R src dst)
    (sourcePoint : HasPoint src) :
    HasPoint dst := by
  obtain ⟨x, hx⟩ := sourcePoint
  obtain ⟨y, hy, _⟩ := total x hx
  exact ⟨y, hy⟩

theorem relationTotal_isEmpty_against
    {α : Type u} {β : Type v}
    {R : PointRelation α β} {src : Model α} {dst : Model β}
    (total : RelationTotalOn R src dst)
    (targetEmpty : IsEmpty dst) :
    IsEmpty src := by
  intro x hx
  obtain ⟨y, hy, _⟩ := total x hx
  exact targetEmpty y hy

theorem relationSurjective_hasPoint_against
    {α : Type u} {β : Type v}
    {R : PointRelation α β} {src : Model α} {dst : Model β}
    (surjective : RelationSurjectiveOn R src dst)
    (targetPoint : HasPoint dst) :
    HasPoint src := by
  obtain ⟨y, hy⟩ := targetPoint
  obtain ⟨x, hx, _⟩ := surjective y hy
  exact ⟨x, hx⟩

theorem relationSurjective_isEmpty_along
    {α : Type u} {β : Type v}
    {R : PointRelation α β} {src : Model α} {dst : Model β}
    (surjective : RelationSurjectiveOn R src dst)
    (sourceEmpty : IsEmpty src) :
    IsEmpty dst := by
  intro y hy
  obtain ⟨x, hx, _⟩ := surjective y hy
  exact sourceEmpty x hx

theorem relationTotal_comp
    {α : Type u} {β : Type v} {γ : Type w}
    {R : PointRelation α β} {S : PointRelation β γ}
    {src : Model α} {mid : Model β} {dst : Model γ}
    (first : RelationTotalOn R src mid)
    (second : RelationTotalOn S mid dst) :
    RelationTotalOn (RelationComp R S) src dst := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := first x hx
  obtain ⟨z, hz, hyz⟩ := second y hy
  exact ⟨z, hz, y, hxy, hyz⟩

theorem relationSurjective_comp
    {α : Type u} {β : Type v} {γ : Type w}
    {R : PointRelation α β} {S : PointRelation β γ}
    {src : Model α} {mid : Model β} {dst : Model γ}
    (first : RelationSurjectiveOn R src mid)
    (second : RelationSurjectiveOn S mid dst) :
    RelationSurjectiveOn (RelationComp R S) src dst := by
  intro z hz
  obtain ⟨y, hy, hyz⟩ := second z hz
  obtain ⟨x, hx, hxy⟩ := first y hy
  exact ⟨x, hx, y, hxy, hyz⟩

theorem refines_iff_identityRelation_total
    {α : Type u} (src dst : Model α) :
    Refines src dst ↔
      RelationTotalOn (IdentityRelation α) src dst := by
  constructor
  · intro refines x hx
    exact ⟨x, refines x hx, rfl⟩
  · intro total x hx
    obtain ⟨y, hy, hxy⟩ := total x hx
    cases hxy
    exact hy

/-! ## A compiled point-contract fragment

The runtime table should not store each point cell as an independent fact.
The relation is the operation-level semantic object; totality and point
surjectivity are separately earned capabilities. -/

structure PointOperation {α : Type u} {β : Type v}
    (src : Model α) (dst : Model β) where
  relation : PointRelation α β

structure TotalCapability {α : Type u} {β : Type v}
    {src : Model α} {dst : Model β}
    (op : PointOperation src dst) : Prop where
  sound : RelationTotalOn op.relation src dst

structure SurjectiveCapability {α : Type u} {β : Type v}
    {src : Model α} {dst : Model β}
    (op : PointOperation src dst) : Prop where
  sound : RelationSurjectiveOn op.relation src dst

/-- Predicates at different endpoints denote the same condition along every
    related pair of points. This premise is automatic for literal
    same-coordinate inclusion, but not for an arbitrary change of type or
    coordinates. -/
def PredicateCorresponds {α : Type u} {β : Type v}
    (R : PointRelation α β) (P : α -> Prop) (Q : β -> Prop) : Prop :=
  forall x y, R x y -> Iff (P x) (Q y)

theorem totalCapability_hasPoint_along
    {α : Type u} {β : Type v} {src : Model α} {dst : Model β}
    {op : PointOperation src dst}
    (cap : TotalCapability op) : HasPoint src -> HasPoint dst :=
  relationTotal_hasPoint_along cap.sound

theorem totalCapability_isEmpty_against
    {α : Type u} {β : Type v} {src : Model α} {dst : Model β}
    {op : PointOperation src dst}
    (cap : TotalCapability op) : IsEmpty dst -> IsEmpty src :=
  relationTotal_isEmpty_against cap.sound

theorem surjectiveCapability_hasPoint_against
    {α : Type u} {β : Type v} {src : Model α} {dst : Model β}
    {op : PointOperation src dst}
    (cap : SurjectiveCapability op) : HasPoint dst -> HasPoint src :=
  relationSurjective_hasPoint_against cap.sound

theorem surjectiveCapability_isEmpty_along
    {α : Type u} {β : Type v} {src : Model α} {dst : Model β}
    {op : PointOperation src dst}
    (cap : SurjectiveCapability op) : IsEmpty src -> IsEmpty dst :=
  relationSurjective_isEmpty_along cap.sound

theorem totalCapability_everywhere_against
    {α : Type u} {β : Type v} {src : Model α} {dst : Model β}
    {op : PointOperation src dst} {P : α -> Prop} {Q : β -> Prop}
    (cap : TotalCapability op)
    (corresponds : PredicateCorresponds op.relation P Q)
    (targetHolds : Everywhere dst Q) : Everywhere src P := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := cap.sound x hx
  exact (corresponds x y hxy).mpr (targetHolds y hy)

theorem surjectiveCapability_everywhere_along
    {α : Type u} {β : Type v} {src : Model α} {dst : Model β}
    {op : PointOperation src dst} {P : α -> Prop} {Q : β -> Prop}
    (cap : SurjectiveCapability op)
    (corresponds : PredicateCorresponds op.relation P Q)
    (sourceHolds : Everywhere src P) : Everywhere dst Q := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := cap.sound y hy
  exact (corresponds x y hxy).mp (sourceHolds x hx)

/-- Even a relation that is both total and point-surjective cannot transport
    two unrelated predicates. Capabilities decide variance; a claim
    transformer still has to say what proposition exists at the other end. -/
theorem bijectiveRelation_does_not_type_predicates :
    exists (R : PointRelation Two Two) (P Q : Two -> Prop),
      RelationTotalOn R both both ∧
      RelationSurjectiveOn R both both ∧
      Everywhere both P ∧
      ¬ Everywhere both Q := by
  refine ⟨IdentityRelation Two, (fun _ => True),
    (fun x => x = Two.a), ?_, ?_, ?_, ?_⟩
  · intro x _
    exact ⟨x, trivial, rfl⟩
  · intro y _
    exact ⟨y, trivial, rfl⟩
  · intro _ _
    exact trivial
  · intro allQ
    exact absurd (allQ Two.b trivial) (by simp)

inductive PointDirection where
  | along
  | against
  deriving DecidableEq

inductive PointClaimKind where
  | empty
  | nonempty
  | predicate
  deriving DecidableEq

/-- The executable shadow used by the Python kernel. These are declarations
    that evidence for the corresponding semantic capabilities is available;
    the booleans are not themselves evidence. -/
structure PointCapabilityBits where
  total : Bool
  pointSurjective : Bool
  deriving DecidableEq

def compilePointRule (cap : PointCapabilityBits) :
    PointDirection -> PointClaimKind -> Bool
  | .along, .nonempty => cap.total
  | .against, .nonempty => cap.pointSurjective
  | .along, .empty => cap.pointSurjective
  | .against, .empty => cap.total
  | .along, .predicate => cap.pointSurjective
  | .against, .predicate => cap.total

theorem compiled_existential_variance (cap : PointCapabilityBits) :
    compilePointRule cap .along .nonempty = cap.total ∧
    compilePointRule cap .against .nonempty = cap.pointSurjective := by
  exact ⟨rfl, rfl⟩

theorem compiled_universal_variance (cap : PointCapabilityBits) :
    compilePointRule cap .along .empty = cap.pointSurjective ∧
    compilePointRule cap .against .empty = cap.total ∧
    compilePointRule cap .along .predicate = cap.pointSurjective ∧
    compilePointRule cap .against .predicate = cap.total := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end GrandPortage
