import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.ModelTheory.Bundled
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Prime.Infinite

/-!
Phase 2.5c context spike (post-G2 handoff §2.5c, Addendum A §2.5d at the A2 pins).

Two candidate contexts for the 3a algebraic profile:
* `Theory.field.ModelType`, Mathlib's bundled models of the first-order theory of fields;
* `FieldCtx`, a local bundle: a carrier in `Type` with a `Field` instance.

Both get the §3.2 characteristic-set scope; `le_sound` and `contra_sound` are proved for
`FieldCtx`, and maps both ways connect it to `ModelType` while preserving characteristic.
-/

namespace GPBinding.Spike
open FirstOrder Language

/-! ## Characteristic-set scopes (post-G2 §3.2) -/

inductive PrimeSet where
  | finite (primes : List ℕ)
  | cofinite (excluded : List ℕ)
  deriving DecidableEq

structure CharScope where
  char0 : Bool
  primes : PrimeSet
  deriving DecidableEq

/-- The characteristics a scope denotes: 0 when `char0`, plus the selected primes. -/
def CharScope.den (s : CharScope) : Set ℕ :=
  {n | (n = 0 ∧ s.char0 = true) ∨
       (n.Prime ∧ match s.primes with
         | .finite ps => n ∈ ps
         | .cofinite e => n ∉ e)}

/-- Decidable inclusion of denotations. Sound for every case; exact except that a cofinite
prime set is never included in a finite one, which is also exact since primes are infinite. -/
def CharScope.le (a b : CharScope) : Bool :=
  (!a.char0 || b.char0) &&
  match a.primes, b.primes with
  | .finite xs, .finite ys => xs.all fun x => !x.Prime || ys.contains x
  | .finite xs, .cofinite e => xs.all fun x => !x.Prime || !e.contains x
  | .cofinite _, .finite _ => false
  | .cofinite ea, .cofinite eb => eb.all fun x => !x.Prime || ea.contains x

theorem CharScope.le_den {a b : CharScope} (h : a.le b = true) : a.den ⊆ b.den := by
  intro n hn
  unfold CharScope.le at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, hp⟩ := h
  rcases hn with ⟨rfl, hc⟩ | ⟨prime, hm⟩
  · left; refine ⟨rfl, ?_⟩; simp_all
  · right; refine ⟨prime, ?_⟩
    rcases ha : a.primes with xs | ea <;> rcases hb : b.primes with ys | eb <;>
      simp only [ha, hb] at hp hm ⊢
    · have := List.all_eq_true.mp hp n hm; simpa [prime] using this
    · have := List.all_eq_true.mp hp n hm; simpa [prime] using this
    · simp at hp
    · intro mem; have := List.all_eq_true.mp hp n mem; simp [prime] at this; exact hm this

/-! ## Candidate 1: a local field bundle -/

structure FieldCtx where
  carrier : Type
  [field : Field carrier]

attribute [instance] FieldCtx.field

instance : CoeSort FieldCtx Type := ⟨FieldCtx.carrier⟩

def FieldCtx.mem (K : FieldCtx) (s : CharScope) : Prop := ringChar K ∈ s.den

theorem FieldCtx.le_sound (a b : CharScope) (K : FieldCtx) (h : a.le b = true)
    (hK : K.mem a) : K.mem b := CharScope.le_den h hK

/-! ## Statements for the spike: EMPTY / NONEMPTY of one integer polynomial system -/

structure System where
  n : ℕ
  eqs : List (MvPolynomial (Fin n) ℤ)

def System.zeroAt (S : System) (K : Type) [CommRing K] (x : Fin S.n → K) : Prop :=
  ∀ p ∈ S.eqs, MvPolynomial.eval₂ (Int.castRingHom K) x p = 0

inductive Stmt where
  | empty (S : System)
  | nonempty (S : System)

def Stmt.holds : Stmt → FieldCtx → Prop
  | .empty S, K => ¬ ∃ x, S.zeroAt K x
  | .nonempty S, K => ∃ x, S.zeroAt K x

/-- EMPTY and NONEMPTY of the same system contradict (decided on `ProfileOps` data). -/
def Stmt.contra : Stmt → Stmt → Prop
  | .empty S, .nonempty T => S = T
  | .nonempty S, .empty T => S = T
  | _, _ => False

theorem Stmt.contra_sound (a b : Stmt) (K : FieldCtx) (h : a.contra b)
    (ha : a.holds K) (hb : b.holds K) : False := by
  cases a <;> cases b <;> simp only [Stmt.contra] at h <;> subst h <;>
    simp only [Stmt.holds] at ha hb
  · exact ha hb
  · exact hb ha

/-! ## Candidate 2: Mathlib's `Theory.field.ModelType`, and the bridge -/

/-- From a field bundle to a bundled first-order model of the theory of fields. -/
noncomputable def FieldCtx.toModelType (K : FieldCtx) : Theory.field.ModelType.{0, 0, 0} :=
  letI := FirstOrder.Ring.compatibleRingOfRing K
  Theory.ModelType.of Theory.field K

/-- From a bundled model back to a field bundle, through Mathlib's `fieldOfModelField`. -/
noncomputable def FieldCtx.ofModelType (M : Theory.field.ModelType.{0, 0, 0}) : FieldCtx :=
  letI := FirstOrder.Field.fieldOfModelField M
  ⟨M⟩

/-- The round trip rebuilds the field via `Field.ofMinimalAxioms` (unary `Nat.cast`, choice-based
inverse), so characteristic agreement is a theorem about two different instances. -/
theorem roundTrip_natCast (K : FieldCtx) (n : ℕ) :
    ((n : FieldCtx.ofModelType K.toModelType) : K) = (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero, Nat.cast_zero]; rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    rfl

theorem roundTrip_ringChar (K : FieldCtx) :
    ringChar (FieldCtx.ofModelType K.toModelType) = ringChar K := by
  haveI : CharP (FieldCtx.ofModelType K.toModelType) (ringChar K) :=
    ⟨fun x => by
      have h := roundTrip_natCast K x
      change ((x : FieldCtx.ofModelType K.toModelType) : K) = 0 ↔ _
      rw [h]
      exact CharP.cast_eq_zero_iff K (ringChar K) x⟩
  exact ringChar.eq (FieldCtx.ofModelType K.toModelType) (ringChar K)

/-- Scope membership is stable across the bridge. -/
theorem roundTrip_mem (K : FieldCtx) (s : CharScope) :
    (FieldCtx.ofModelType K.toModelType).mem s ↔ K.mem s := by
  simp only [FieldCtx.mem, roundTrip_ringChar]

end GPBinding.Spike
