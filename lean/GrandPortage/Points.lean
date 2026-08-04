/-
# The point layer

The first transport-table measurement found that twenty-seven of thirty-six
typed point cells agreed with plain subset inclusion. That observation led to
the relational compiler now used by the Python kernel. This file proves the
same-coordinate inclusion fragment and supplies countermodels for the three
directions it refuses; `RelationalTransport.lean` generalizes the result.

Deliberately Mathlib-free.  A model is a predicate, an inclusion is an
implication, and every theorem below is a few lines.  If the point layer needed
heavy machinery, that would itself be a finding.
-/

namespace GrandPortage

universe u v w

/-- A model is its solution set, and a solution set is a predicate.

    This is the kernel's own position -- "a model in this kernel IS its
    solution set" -- taken literally. -/
def Model (α : Type u) := α → Prop

/-- Edges run TIGHTER → LOOSER.  `Refines src dst` is `V(src) ⊆ V(dst)`. -/
def Refines {α : Type u} (src dst : Model α) : Prop := ∀ x, src x → dst x

def IsEmpty {α : Type u} (M : Model α) : Prop := ∀ x, ¬ M x
def HasPoint {α : Type u} (M : Model α) : Prop := ∃ x, M x
def Everywhere {α : Type u} (M : Model α) (P : α → Prop) : Prop :=
  ∀ x, M x → P x

/-- Reindex a predicate contravariantly along a point map. -/
def Pullback {α : Type u} {β : Type v}
    (pointMap : α → β) (predicate : β → Prop) : α → Prop :=
  fun x => predicate (pointMap x)

/-- A predicate true on every target point pulls back to every source point
    whenever the declared point map really maps source points into the target. -/
theorem everywhere_pullback {α : Type u} {β : Type v}
    {src : Model α} {dst : Model β} (pointMap : α → β)
    (maps : ∀ x, src x → dst (pointMap x)) (predicate : β → Prop) :
    Everywhere dst predicate → Everywhere src (Pullback pointMap predicate) :=
  fun holds x hx => holds (pointMap x) (maps x hx)

/-- Pullback along the identity point map changes no predicate syntax. -/
theorem pullback_id {α : Type u} (predicate : α → Prop) :
    Pullback id predicate = predicate := rfl

/-- Predicate pullback is functorial: a composite point map pulls back in the
    opposite, stepwise order. -/
theorem pullback_comp {α : Type u} {β : Type v} {γ : Type w}
    (first : α → β) (second : β → γ) (predicate : γ → Prop) :
    Pullback (fun x => second (first x)) predicate =
      Pullback first (Pullback second predicate) := rfl

/-! ## The three cells inclusion licenses

`ALONG` follows the arrow (src → dst); `AGAINST` runs back against it. -/

/-- `NONEMPTY` travels ALONG: a point of the tighter model is a point of the
    looser one.  Instantiation and nothing more. -/
theorem hasPoint_along {α : Type u} {src dst : Model α}
    (h : Refines src dst) : HasPoint src → HasPoint dst
  | ⟨x, hx⟩ => ⟨x, h x hx⟩

/-- `EMPTY` travels AGAINST: if the looser model has no points, neither can a
    subset of it.  This is the direction that closes cases. -/
theorem isEmpty_against {α : Type u} {src dst : Model α}
    (h : Refines src dst) : IsEmpty dst → IsEmpty src :=
  fun hd x hx => hd x (h x hx)

/-- `PREDICATE` travels AGAINST: something true at every point of the looser
    model is true at every point of the tighter one. -/
theorem everywhere_against {α : Type u} {src dst : Model α} {P : α → Prop}
    (h : Refines src dst) : Everywhere dst P → Everywhere src P :=
  fun hd x hx => hd x (h x hx)

/-! ## The three cells inclusion REFUSES, with countermodels

A refusal backed by a counterexample is a theorem.  A refusal backed by
nothing is a policy, and a table should not contain policies it cannot
distinguish from theorems. -/

/-- Two points, so the countermodels below are not vacuous. -/
inductive Two where
  | a : Two
  | b : Two

def nowhere : Model Two := fun _ => False
def onlyA : Model Two := fun x => x = Two.a
def both : Model Two := fun _ => True

theorem nowhere_refines_both : Refines nowhere both := fun _ hx => hx.elim
theorem onlyA_refines_both : Refines onlyA both := fun _ _ => trivial

/-- `EMPTY` does NOT travel ALONG.  An empty subset of a nonempty model says
    nothing about the model. -/
theorem isEmpty_not_along :
    ¬ (∀ (src dst : Model Two), Refines src dst → IsEmpty src → IsEmpty dst) := by
  intro h
  exact h nowhere both nowhere_refines_both (fun _ hx => hx) Two.a trivial

/-- `NONEMPTY` does NOT travel AGAINST.  This is the shape of the witness
    error: a point of the relaxation need not satisfy what the edge dropped. -/
theorem hasPoint_not_against :
    ¬ (∀ (src dst : Model Two), Refines src dst → HasPoint dst → HasPoint src) := by
  intro h
  -- The countermodel has to be a pair where dst HAS a point and src does not.
  -- My first attempt used `onlyA` as the source, which has a point -- so it
  -- refuted nothing. The empty model is the honest witness.
  obtain ⟨_, hx⟩ := h nowhere both nowhere_refines_both ⟨Two.a, trivial⟩
  exact hx

/-- `PREDICATE` does NOT travel ALONG.  Something true on the tighter model
    need not hold on the looser one -- the generic-versus-everywhere
    distinction, which is the one a `RESTRICTION` costs you. -/
theorem everywhere_not_along :
    ¬ (∀ (src dst : Model Two) (P : Two → Prop),
        Refines src dst → Everywhere src P → Everywhere dst P) := by
  intro h
  have : Everywhere both (fun y => y = Two.a) :=
    h onlyA both (fun y => y = Two.a) onlyA_refines_both (fun _ hx => hx)
  exact absurd (this Two.b trivial) (by simp)

/-! ## Partitions

A branch is `parent AND condition`, so a branch is not a relaxation of the
parent -- it is a PIECE of it.  That distinction cost two live campaigns
before it had a name. -/

structure Cover {α : Type u} (parent : Model α) (ι : Type v) where
  branch : ι → Model α
  contained : ∀ i x, branch i x → parent x
  exhaustive : ∀ x, parent x → ∃ i, branch i x

/-- THE PAYOFF.  Every branch empty, plus exhaustiveness, gives the parent
    empty.  No single branch-to-parent edge can do this, which is why a
    partition is a distinct inference form rather than another edge type. -/
theorem cover_empty {α : Type u} {ι : Type v} {parent : Model α}
    (c : Cover parent ι) (h : ∀ i, IsEmpty (c.branch i)) : IsEmpty parent := by
  intro x hx
  obtain ⟨i, hi⟩ := c.exhaustive x hx
  exact h i x hi

end GrandPortage
