import GrandPortage.CertificateInterpreter

namespace GrandPortage.CertificateInterpreter

universe u v w

/-- The exact operation-preservation premises needed by this expression syntax.
Neither injectivity nor an ordering is assumed. -/
structure OperationMap {A : Type u} {B : Type v}
    (source : Operations A) (target : Operations B) where
  map : A → B
  map_zero : map source.zero = target.zero
  map_one : map source.one = target.one
  map_add : ∀ a b, map (source.add a b) = target.add (map a) (map b)
  map_mul : ∀ a b, map (source.mul a b) = target.mul (map a) (map b)
  map_neg : ∀ a, map (source.neg a) = target.neg (map a)

variable {A : Type u} {B : Type v} {C : Type w}
variable {source : Operations A} {target : Operations B} {third : Operations C}

/-- Evaluation commutes with the map, proved by syntax induction. -/
theorem eval_map (h : OperationMap source target) (point : Nat → A) (e : Expr) :
    eval target (fun i => h.map (point i)) e = h.map (eval source point e) := by
  induction e with
  | zero => exact h.map_zero.symm
  | one => exact h.map_one.symm
  | var => rfl
  | add a b ha hb => simp only [eval, ha, hb, h.map_add]
  | mul a b ha hb => simp only [eval, ha, hb, h.map_mul]
  | neg a ha => simp only [eval, ha, h.map_neg]

/-- A source equality transports even without target algebraic laws or order. -/
theorem equality_transport (h : OperationMap source target) (point : Nat → A)
    (same : eval source point a = eval source point b) :
    eval target (fun i => h.map (point i)) a =
      eval target (fun i => h.map (point i)) b := by
  rw [eval_map h, eval_map h, same]

/-- Roots travel forward; no claim is made that target roots lift back. -/
theorem holds_transport (h : OperationMap source target) (c : Certificate)
    (point : Nat → A) (holds : c.Holds source point) :
    c.Holds target (fun i => h.map (point i)) := by
  intro term member
  rw [eval_map h, holds term member, h.map_zero]

/-- Consequently target emptiness pulls back without an injectivity premise. -/
theorem emptiness_pullback (h : OperationMap source target) (c : Certificate)
    (empty : ∀ point, ¬ c.Holds target point) :
    ∀ point, ¬ c.Holds source point := by
  intro point holds
  exact empty _ (holds_transport h c point holds)

def OperationMap.comp (g : OperationMap target third)
    (f : OperationMap source target) : OperationMap source third where
  map := fun a => g.map (f.map a)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_one := by rw [f.map_one, g.map_one]
  map_add := by intro a b; rw [f.map_add, g.map_add]
  map_mul := by intro a b; rw [f.map_mul, g.map_mul]
  map_neg := by intro a; rw [f.map_neg, g.map_neg]

/-- A concrete map preserves expression evaluation but cannot confer order on
its target: gaussian_has_no_ordering already rules that out. -/
def integerToGaussian : OperationMap integers gaussian where
  map := fun a => (a, 0)
  map_zero := rfl
  map_one := rfl
  map_add := by intro a b; simp [integers, gaussian]
  map_mul := by intro a b; simp [integers, gaussian]
  map_neg := by intro a; rfl

theorem sample_replay_transports (point : Nat → Int) :
    eval gaussian (fun i => (point i, 0)) sample.rhs =
      eval gaussian (fun i => (point i, 0)) (.neg .one) :=
  equality_transport integerToGaussian point
    (derivation_sound integer_laws point sample_derivation)

/-- Forward emptiness fails for this actual operation map: the source has no
root while the target has an exhibited root. -/
theorem forward_emptiness_counterexample :
    (∀ point, ¬ sample.Holds integers point) ∧
      (∃ point, sample.Holds gaussian point) :=
  ⟨sample_empty integer_laws integer_order,
   ⟨imaginaryPoint, unordered_solution_and_replay.1⟩⟩

end GrandPortage.CertificateInterpreter
