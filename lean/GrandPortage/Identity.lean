/-
# The identity layer, where the actual mathematics is

Measured against the Python kernel:

    point cells (36):    27 agree with plain inclusion, 3 disagree, 6 conditional
    IDENTITY cells (12):  1 agree with contravariance, 3 disagree, 8 conditional

So the point half compresses and this half does not.  Eight of twelve cells are
gated, and that is where all the hand-entered booleans live -- `ring_iso`,
`identity_origin`, `integral`, `coefficients_in_base`, `map_kind`.

This file asks whether that is irreducible.  Still Mathlib-free: an ideal is a
predicate, and the counterexamples live in `Int`, which is in core.
-/

namespace GrandPortage

universe u v

/-- An ideal, as much of one as the variance question needs: a predicate on
    ring elements. -/
def Ideal (R : Type u) := R → Prop

/-- An identity `f = g` holds modulo `I` exactly when `f - g ∈ I`.  This is the
    kernel's own definition of IDENTITY -- "a rewriting valid in the coordinate
    ring", and the coordinate ring is `R/I`. -/
def EqMod {R : Type u} [Sub R] (I : Ideal R) (f g : R) : Prop := I (f - g)

/-- MORE EQUATIONS CUT A SMALLER VARIETY, so the tighter model has the LARGER
    ideal.  This is the orientation everything below turns on, and it is the
    one people get backwards. -/
def IdealGrows {R : Type u} (looseI tightI : Ideal R) : Prop :=
  ∀ f, looseI f → tightI f

/-! ## The one thing that does derive

Contravariance: an identity valid in the LOOSER model's coordinate ring is
valid in the TIGHTER one, because the tighter ideal contains the looser one.

In edge terms, with src tighter and dst looser: this is IDENTITY travelling
AGAINST.  It is the single identity cell that follows from the ideal relation
alone, and the measurement found exactly one such cell. -/

theorem eqMod_against {R : Type u} [Sub R] {looseI tightI : Ideal R}
    (h : IdealGrows looseI tightI) {f g : R} :
    EqMod looseI f g → EqMod tightI f g :=
  fun hfg => h _ hfg

/-! ## And the counterexample that refuses the other direction

`x = 0` is valid in `k[x]/(x)` and false in `k[x]`.  The kernel quotes exactly
that, and it needs no polynomial ring: the same shape lives in `Int`, where
`2 = 0` modulo `(2)` and `2 ≠ 0` modulo `(0)`. -/

/-- The ideal `(2) ⊆ ℤ`, as a predicate. -/
def evens : Ideal Int := fun n => ∃ k, n = 2 * k

/-- The zero ideal. -/
def zeroI : Ideal Int := fun n => n = 0

theorem zero_grows_to_evens : IdealGrows zeroI evens := by
  intro n h
  simp only [zeroI] at h
  exact ⟨0, by omega⟩

/-- An identity DERIVED from the tighter model's equations does not survive
    dropping them.  This is the `identity_origin` distinction, and it is a
    theorem rather than a policy. -/
theorem eqMod_not_along :
    ¬ (∀ (looseI tightI : Ideal Int), IdealGrows looseI tightI →
        ∀ f g, EqMod tightI f g → EqMod looseI f g) := by
  intro h
  -- 2 = 0 modulo (2)
  have h2 : EqMod evens 2 0 := by
    simp only [EqMod, evens]
    exact ⟨1, by omega⟩
  -- so the claim would give 2 = 0 modulo (0)
  have hz : EqMod zeroI 2 0 := h zeroI evens zero_grows_to_evens 2 0 h2
  -- which says 2 - 0 = 0
  simp only [EqMod, zeroI] at hz
  omega

/-! ## Where the eight gated cells come from

The theorem above needs `IdealGrows looseI tightI` -- ideal CONTAINMENT.  The
measurement found two cells that disagree with contravariance, and both
disagree for the same reason: containment is not the relation there.

  * `RESTRICTION` drops inequalities and no equations, so the two ideals are
    EQUAL.  Containment holds both ways and the identity crosses in both
    directions unconditionally.

  * `BASE_EXTENSION` does not compare two ideals in one ring at all.  It sends
    `I` to its extension `Iᵉ` in a larger ring, and an identity over the small
    field persists over the large one.

So the gates are not arbitrary.  Each names WHICH RELATION between coordinate
rings the edge induces, and the transport follows from that relation rather
than from the edge's name. -/

/-- When the ideals are equal, the identity crosses both ways -- and neither
    direction needs a condition.  This is `RESTRICTION`. -/
theorem eqMod_both_ways {R : Type u} [Sub R] {I J : Ideal R}
    (h₁ : IdealGrows I J) (h₂ : IdealGrows J I) {f g : R} :
    EqMod I f g ↔ EqMod J f g :=
  ⟨fun hfg => h₁ _ hfg, fun hfg => h₂ _ hfg⟩

/-- THE SHAPE OF THE REMAINING QUESTION.

    A general edge induces a map on coordinate rings, and every gated IDENTITY
    cell is a condition on that map.  Stated abstractly: an identity crosses
    when the induced map SENDS the source ideal into the target ideal.

    `ring_iso`, `identity_origin`, `integral` and `coefficients_in_base` all
    look like instances of this one condition, checked differently because the
    maps differ.  Whether they really are one condition is the question this
    layer exists to settle, and it is not settled here. -/
def Carries {R : Type u} {S : Type v} (φ : R → S) (I : Ideal R) (J : Ideal S) : Prop :=
  ∀ f, I f → J (φ f)

theorem eqMod_transports {R : Type u} {S : Type v} [Sub R] [Sub S]
    (φ : R → S) (hφ : ∀ a b : R, φ (a - b) = φ a - φ b)
    {I : Ideal R} {J : Ideal S} (h : Carries φ I J) {f g : R} :
    EqMod I f g → EqMod J (φ f) (φ g) := by
  intro hfg
  have := h _ hfg
  rwa [hφ] at this

end GrandPortage
