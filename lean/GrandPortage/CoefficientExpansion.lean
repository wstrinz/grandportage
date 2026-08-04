/-
# Coefficient expansion for bounded polynomial unknowns

The scalar-affine encoding of a bounded polynomial is its finite coefficient
vector. Selected rows are only necessary; complete rows reconstruct the
polynomial; coefficient point-surjectivity supplies a bounded witness but no
uniqueness theorem.
-/

import GrandPortage.Points

namespace GrandPortage

universe u v

/-- A degree-capped polynomial is exactly its coefficients `0, ..., degree`. -/
abbrev BoundedPolynomial (A : Type u) (degree : Nat) :=
  Fin (degree + 1) → A

def zeroBoundedPolynomial {A : Type u} [Zero A] {degree : Nat} :
    BoundedPolynomial A degree :=
  fun _ => 0

def BoundedPolynomialVanishes {A : Type u} [Zero A] {degree : Nat}
    (p : BoundedPolynomial A degree) : Prop :=
  ∀ i, p i = 0

def SelectedCoefficientsVanish {A : Type u} [Zero A] {degree : Nat}
    (selected : Fin (degree + 1) → Prop)
    (p : BoundedPolynomial A degree) : Prop :=
  ∀ i, selected i → p i = 0

/-- Polynomial vanishing entails every selected coefficient check. -/
theorem boundedPolynomialVanishes_entails_selected
    {A : Type u} [Zero A] {degree : Nat}
    (selected : Fin (degree + 1) → Prop)
    (p : BoundedPolynomial A degree)
    (vanishes : BoundedPolynomialVanishes p) :
    SelectedCoefficientsVanish selected p := by
  intro i _
  exact vanishes i

def constantCoefficientOnly : Fin 2 → Prop :=
  fun i => i = 0

/-- The bounded polynomial `y`, with coefficient vector `(0, 1)`. -/
def boundedY : BoundedPolynomial Nat 1 :=
  fun i => if i = 1 then 1 else 0

/-- Omitting the top row accepts `y`; selected rows are not sufficient. -/
theorem selected_coefficients_do_not_imply_polynomial_vanishing :
    SelectedCoefficientsVanish constantCoefficientOnly boundedY ∧
      ¬ BoundedPolynomialVanishes boundedY := by
  constructor
  · intro i hi
    simp only [constantCoefficientOnly] at hi
    subst i
    simp [boundedY]
  · intro vanishes
    have top := vanishes (1 : Fin 2)
    simp [boundedY] at top

def CompleteCoefficientCoverage {degree : Nat}
    (selected : Fin (degree + 1) → Prop) : Prop :=
  ∀ i, selected i

/-- Complete row coverage is equivalent to bounded-polynomial vanishing. -/
theorem selectedCoefficientsVanish_iff_of_complete
    {A : Type u} [Zero A] {degree : Nat}
    {selected : Fin (degree + 1) → Prop}
    (complete : CompleteCoefficientCoverage selected)
    (p : BoundedPolynomial A degree) :
    SelectedCoefficientsVanish selected p ↔
      BoundedPolynomialVanishes p := by
  constructor
  · intro selectedVanish i
    exact selectedVanish i (complete i)
  · exact boundedPolynomialVanishes_entails_selected selected p

def boundedCoefficientVector {A : Type u} {degree : Nat}
    (coefficients : Fin (degree + 1) → A) :
    BoundedPolynomial A degree :=
  coefficients

/-- Complete coefficient equality is equality after reconstruction. -/
theorem boundedCoefficientVector_eq_iff
    {A : Type u} {degree : Nat}
    (left right : Fin (degree + 1) → A) :
    boundedCoefficientVector left =
        boundedCoefficientVector right ↔
      ∀ i, left i = right i := by
  constructor
  · intro equal i
    exact congrFun equal i
  · intro equal
    funext i
    exact equal i

theorem boundedPolynomialVanishes_iff_vector_zero
    {A : Type u} [Zero A] {degree : Nat}
    (p : BoundedPolynomial A degree) :
    BoundedPolynomialVanishes p ↔
      boundedCoefficientVector p = zeroBoundedPolynomial := by
  change (∀ i, p i = 0) ↔ p = (fun _ => 0)
  constructor
  · intro vanishes
    funext i
    exact vanishes i
  · intro equal i
    exact congrFun equal i

/-! ## Reconstruction as a genuine formal polynomial -/

/--
A formal polynomial represented by its coefficient function together with a proof
that all sufficiently high coefficients vanish.

This deliberately small representation keeps the transport formalization
Mathlib-free while still exposing the defining extensional semantics of a
polynomial.
-/
def Polynomial (A : Type u) [Zero A] :=
  { coefficients : Nat → A //
    ∃ bound, ∀ n, bound < n → coefficients n = 0 }

namespace Polynomial

def coeff {A : Type u} [Zero A] (p : Polynomial A) (n : Nat) : A :=
  p.1 n

def zero {A : Type u} [Zero A] : Polynomial A :=
  ⟨fun _ => 0, 0, by
    intro n _
    rfl⟩

theorem ext {A : Type u} [Zero A] {p q : Polynomial A}
    (equalCoefficients : ∀ n, coeff p n = coeff q n) :
    p = q := by
  apply Subtype.ext
  funext n
  exact equalCoefficients n

end Polynomial

/--
Reconstruct a formal polynomial from every coefficient through the declared
degree cap. Coefficients outside the cap are zero.
-/
def reconstructBoundedPolynomial
    {A : Type u} [Zero A] {degree : Nat}
    (p : BoundedPolynomial A degree) :
    Polynomial A :=
  ⟨
    fun n => if inside : n < degree + 1 then p ⟨n, inside⟩ else 0,
    degree,
    by
      intro n above
      have outside : ¬ n < degree + 1 := by omega
      simp [outside]
  ⟩

/-- Reconstruction recovers every coefficient inside the declared cap. -/
theorem coeff_reconstructBoundedPolynomial
    {A : Type u} [Zero A] {degree : Nat}
    (p : BoundedPolynomial A degree)
    (i : Fin (degree + 1)) :
    Polynomial.coeff (reconstructBoundedPolynomial p) i.val = p i := by
  simp [Polynomial.coeff, reconstructBoundedPolynomial, i.isLt]

/-- Reconstruction has no coefficients above the declared cap. -/
theorem coeff_reconstructBoundedPolynomial_above
    {A : Type u} [Zero A] {degree n : Nat}
    (p : BoundedPolynomial A degree)
    (above : degree < n) :
    Polynomial.coeff (reconstructBoundedPolynomial p) n = 0 := by
  have outside : ¬ n < degree + 1 := by omega
  simp [Polynomial.coeff, reconstructBoundedPolynomial, outside]

/--
The reconstructed formal polynomial is zero exactly when all bounded
coefficients vanish.
-/
theorem reconstructBoundedPolynomial_eq_zero_iff
    {A : Type u} [Zero A] {degree : Nat}
    (p : BoundedPolynomial A degree) :
    reconstructBoundedPolynomial p = Polynomial.zero ↔
      BoundedPolynomialVanishes p := by
  constructor
  · intro equal i
    calc
      p i = Polynomial.coeff (reconstructBoundedPolynomial p) i.val :=
        (coeff_reconstructBoundedPolynomial p i).symm
      _ = Polynomial.coeff Polynomial.zero i.val :=
        congrArg (fun polynomial => Polynomial.coeff polynomial i.val) equal
      _ = 0 := rfl
  · intro vanishes
    apply Polynomial.ext
    intro n
    by_cases inside : n < degree + 1
    · let i : Fin (degree + 1) := ⟨n, inside⟩
      simpa [Polynomial.coeff, reconstructBoundedPolynomial,
        Polynomial.zero, inside] using vanishes i
    · simp [Polynomial.coeff, reconstructBoundedPolynomial,
        Polynomial.zero, inside]

/-! ## Bounded witnesses from coefficient point-surjectivity -/

structure BoundedPolynomialLift
    (Retained : Type u) (A : Type v) (degree : Nat) where
  retained : Retained
  dm4 : BoundedPolynomial A degree

def forgetBoundedPolynomial
    {Retained : Type u} {A : Type v} {degree : Nat} :
    BoundedPolynomialLift Retained A degree → Retained :=
  fun source => source.retained

def CoefficientPointSurjective
    {Retained : Type u} {A : Type v} {degree : Nat}
    (source : Model (BoundedPolynomialLift Retained A degree))
    (target : Model Retained) : Prop :=
  ∀ q, target q →
    ∃ sourcePoint, source sourcePoint ∧
      forgetBoundedPolynomial sourcePoint = q

/-- Point-surjectivity yields an honest capped `dm4` coefficient vector. -/
theorem coefficient_point_surjectivity_yields_bounded_dm4
    {Retained : Type u} {A : Type v} {degree : Nat}
    {source : Model (BoundedPolynomialLift Retained A degree)}
    {target : Model Retained}
    (surjective : CoefficientPointSurjective source target)
    (q : Retained) (hq : target q) :
    ∃ dm4 : BoundedPolynomial A degree,
      source { retained := q, dm4 := dm4 } := by
  obtain ⟨sourcePoint, sourceValid, projects⟩ := surjective q hq
  cases sourcePoint with
  | mk retained dm4 =>
      simp only [forgetBoundedPolynomial] at projects
      subst retained
      exact ⟨dm4, sourceValid⟩

def UniqueBoundedPolynomialLift
    {Retained : Type u} {A : Type v} {degree : Nat}
    (source : Model (BoundedPolynomialLift Retained A degree))
    (target : Model Retained) : Prop :=
  ∀ q, target q →
    ∃ dm4 : BoundedPolynomial A degree,
      source { retained := q, dm4 := dm4 } ∧
        ∀ other, source { retained := q, dm4 := other } → other = dm4

def allCoefficientLifts :
    Model (BoundedPolynomialLift Unit Nat 0) :=
  fun _ => True

def unitCoefficientTarget : Model Unit :=
  fun _ => True

/-- Surjectivity alone cannot be strengthened to uniqueness. -/
theorem coefficient_point_surjectivity_does_not_imply_uniqueness :
    CoefficientPointSurjective allCoefficientLifts unitCoefficientTarget ∧
      ¬ UniqueBoundedPolynomialLift
        allCoefficientLifts unitCoefficientTarget := by
  constructor
  · intro q _
    exact ⟨{ retained := q, dm4 := fun _ => 0 }, True.intro, rfl⟩
  · intro unique
    obtain ⟨dm4, _, only⟩ := unique () True.intro
    have zeroIsDm4 : (fun _ : Fin 1 => 0) = dm4 :=
      only (fun _ => 0) True.intro
    have oneIsDm4 : (fun _ : Fin 1 => 1) = dm4 :=
      only (fun _ => 1) True.intro
    have zeroIsOne : (fun _ : Fin 1 => 0) = (fun _ : Fin 1 => 1) :=
      zeroIsDm4.trans oneIsDm4.symm
    have impossible := congrFun zeroIsOne (0 : Fin 1)
    omega

end GrandPortage
