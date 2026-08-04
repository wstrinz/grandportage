/-
# Are the four gated conditions one condition?

`Identity.lean` ended with a conjecture: `ring_iso`, `identity_origin`,
`integral` and `coefficients_in_base` all *look* like instances of

    Carries φ I J := ∀ f, I f → J (φ f)

checked differently because the maps differ.

**They are not.**  Working through them turns up three distinct shapes, and
saying which is which explains why the eight gated cells resisted compression
while the point cells did not.
-/

import GrandPortage.Identity

namespace GrandPortage

universe u

/-- The converse of `Carries`: the map pulls the target ideal back INTO the
    source one.  Nothing in the earlier file needed this, which is why the
    conjecture looked plausible. -/
def Reflects {R S : Type u} (φ : R → S) (I : Ideal R) (J : Ideal S) : Prop :=
  ∀ f, J (φ f) → I f

/-! ## Shape 1 — `identity_origin : AMBIENT` is not about the map at all

An AMBIENT rewriting holds in the shared coordinate ring BEFORE any of the
model's equations are imposed.  So it is not a claim modulo `I` that happens to
survive: it is a claim modulo the ZERO ideal, and the zero ideal is inside
every ideal.

The condition therefore strengthens the HYPOTHESIS rather than constraining the
map, and the transport is the contravariance theorem applied from a smaller
ideal.  A corollary, not a new rule. -/

def zero {R : Type u} [OfNat R 0] : Ideal R := fun f => f = 0

/-- The zero ideal sits inside every ideal, provided the ideal contains 0. -/
theorem zero_grows {R : Type u} [OfNat R 0] {I : Ideal R} (h0 : I 0) :
    IdealGrows zero I := by
  intro f hf
  simp only [zero] at hf
  exact hf ▸ h0

/-- AMBIENT identities cross to ANY model in the same ring, in either
    direction, and this is `eqMod_against` from the zero ideal.  Nothing about
    `φ` appears. -/
theorem ambient_crosses_anywhere {R : Type u} [Sub R] [OfNat R 0]
    {I : Ideal R} (h0 : I 0) {f g : R} :
    EqMod zero f g → EqMod I f g :=
  eqMod_against (zero_grows h0)

/-! ## Shape 2 — descent needs `Reflects`, and `Carries` will not do

`coefficients_in_base` gates BASE_EXTENSION in the AGAINST direction: an
identity over the big field descends when both sides lie in the base.  That is
a statement about pulling BACK, and `Carries` is the wrong arrow.

The counterexample is the one from `Identity.lean` wearing a different hat.
Take `φ = id` on `ℤ`, source ideal `(0)`, target ideal `(2)`. -/

theorem carries_zero_to_evens : Carries id zeroI evens := by
  intro f hf
  simp only [zeroI] at hf
  simp only [evens, id_eq]
  exact ⟨0, by omega⟩

/-- `Carries` holds and descent still fails.  So a condition of `Carries` shape
    cannot be what licenses BASE_EXTENSION/AGAINST. -/
theorem carries_does_not_give_descent :
    ¬ (∀ {R S : Type} [Sub R] [Sub S] (φ : R → S) (I : Ideal R) (J : Ideal S),
        Carries φ I J → ∀ f g, EqMod J (φ f) (φ g) → EqMod I f g) := by
  intro h
  have h2 : EqMod evens (id 2) (id 0) := by
    simp only [EqMod, evens, id]
    exact ⟨1, by omega⟩
  have hz : EqMod zeroI 2 0 := h id zeroI evens carries_zero_to_evens 2 0 h2
  simp only [EqMod, zeroI] at hz
  omega

/-- What descent actually needs.  Not a condition on the claim's coefficients
    per se -- that is how you CHECK it -- but the reflection property those
    coefficients buy. -/
theorem reflects_gives_descent {R S : Type u} [Sub R] [Sub S]
    (φ : R → S) (hφ : ∀ a b : R, φ (a - b) = φ a - φ b)
    {I : Ideal R} {J : Ideal S} (h : Reflects φ I J) {f g : R} :
    EqMod J (φ f) (φ g) → EqMod I f g := by
  intro hfg
  apply h
  rw [hφ]
  exact hfg

/-! ## Shape 3 — `ring_iso` is both arrows at once

An EQUIVALENCE licenses IDENTITY in BOTH directions, and that is exactly
`Carries` together with `Reflects`.  The kernel's own warning is that a
bijection on POINTS does not give this: `V(x²)` and `V(x)` have the same single
solution and different coordinate rings.  Points give neither arrow. -/

structure RingIso {R S : Type u} (φ : R → S) (I : Ideal R) (J : Ideal S) where
  carries : Carries φ I J
  reflects : Reflects φ I J

theorem ringIso_both_ways {R S : Type u} [Sub R] [Sub S]
    (φ : R → S) (hφ : ∀ a b : R, φ (a - b) = φ a - φ b)
    {I : Ideal R} {J : Ideal S} (iso : RingIso φ I J) {f g : R} :
    EqMod I f g ↔ EqMod J (φ f) (φ g) :=
  ⟨eqMod_transports φ hφ iso.carries, reflects_gives_descent φ hφ iso.reflects⟩

/-! ## The answer

Three shapes, not one:

    identity_origin : AMBIENT    the claim lives at a SMALLER ideal
                                 (nothing about the map)
    coefficients_in_base         REFLECTS  (pull back)
    ring_iso                     CARRIES and REFLECTS
    integral                     CARRIES is even DEFINED -- reduction mod p
                                 is undefined on a coefficient with p in its
                                 denominator, so this gates the existence of
                                 φ rather than a property of it

So the conjecture is refuted, and the refutation is more useful than the
compression would have been.  The eight gated IDENTITY cells did not collapse
because they are answering four different questions:

  * does the claim hold in a smaller ideal than declared?
  * does the induced map push the ideal forward?
  * does it pull the ideal back?
  * is the induced map defined at all?

A single `Carries` gate would have licensed descent, which the counterexample
above refutes outright.  That is the concrete cost of the compression that did
not happen. -/


/-! ## A correction, and it is the most interesting thing here

Above, `coefficients_in_base` is labelled REFLECTS.  Checking that against the
Python kernel's own counterexample says otherwise.

The kernel refuses descent with this:

    x² + 1 = (x + i)(x - i) is a valid rewriting in ℚ(i)[x].  Transported
    AGAINST to the ℚ-model, `i` is not merely unproved -- it is NOT
    EXPRESSIBLE there.  The descended statement is not a false claim, it is
    not a claim.

That is not reflection failing.  For a field extension the reflection property
`Iᵉ ∩ k[x] = I` holds automatically by faithful flatness; nothing needs gating.
What fails is that the claim cannot be WRITTEN in the smaller ring at all.

And notice where that condition went in `reflects_gives_descent`: it did not
appear as a hypothesis, because `f g : R` puts it in the TYPE.  A claim about
elements of `R` is expressible in `R` by construction, so the theorem is true
and simply cannot see the gate.

**So `coefficients_in_base` is a typing artifact.**  It exists because a Python
claim is a STRING, and a string offers no evidence that what it denotes lives
in the base ring.  In a typed setting the condition is discharged by the type
and disappears.

That is a real prediction about the implementation rather than about the
mathematics: the gate is not protecting a mathematical fact, it is standing in
for a type the representation does not have.  It should be checkable --
"do these coefficients lie in the base?" is decidable -- rather than declared. -/

/-- Expressibility, which is what the gate is really asking, and which the
    typed statement above gets for free. -/
def Expressible {R S : Type u} (φ : R → S) (y : S) : Prop := ∃ x, φ x = y

/-- The honest form of descent when the claim is NOT known to be typed at `R`:
    expressibility is a hypothesis, not a consequence. -/
theorem descent_needs_expressibility {R S : Type u} [Sub R] [Sub S]
    (φ : R → S) (hφ : ∀ a b : R, φ (a - b) = φ a - φ b)
    {I : Ideal R} {J : Ideal S} (h : Reflects φ I J)
    (y z : S) (hy : Expressible φ y) (hz : Expressible φ z) :
    EqMod J y z → ∃ f g : R, φ f = y ∧ φ g = z ∧ EqMod I f g := by
  intro huv
  obtain ⟨f, hf⟩ := hy
  obtain ⟨g, hg⟩ := hz
  refine ⟨f, g, hf, hg, ?_⟩
  apply h
  rw [hφ, hf, hg]
  exact huv

/-! ## What a verifier would have to check for `ring_iso`

`RingIso` above bundles `Carries` and `Reflects`, and `Reflects` is the awkward
half: it quantifies over the SOURCE ring and says something about preimages,
which is not a reduction a CAS can run directly.

But it follows from two things that ARE reductions, given an inverse map:

  * every generator of the TARGET ideal pulls back into the source one, and
  * the two maps compose to the identity.

That turns an unaudited boolean into two batches of substitutions -- exactly
the shape `classify_identity` already answers. -/

/-- The backward direction, stated as the verifier can check it. -/
def PullsBack {R S : Type u} (ψ : S → R) (I : Ideal R) (J : Ideal S) : Prop :=
  ∀ g, J g → I (ψ g)

/-- `Reflects` is not primitive: an inverse map plus `PullsBack` gives it.

    This is the specification a `verify_ring_iso` has to meet.  Neither
    hypothesis needs a preimage search -- `PullsBack` is one reduction per
    target generator, and the round trip is a substitution check. -/
theorem reflects_of_pullsBack {R S : Type u} (φ : R → S) (ψ : S → R)
    {I : Ideal R} {J : Ideal S}
    (hback : PullsBack ψ I J) (hround : ∀ f, ψ (φ f) = f) :
    Reflects φ I J := by
  intro f hf
  have := hback _ hf
  rwa [hround] at this

/-- So a verified iso is: forward carries, backward pulls back, and the maps
    round-trip.  All three are checkable, and together they license IDENTITY in
    both directions. -/
theorem ringIso_of_checks {R S : Type u} [Sub R] [Sub S]
    (φ : R → S) (ψ : S → R) (hφ : ∀ a b : R, φ (a - b) = φ a - φ b)
    {I : Ideal R} {J : Ideal S}
    (hfwd : Carries φ I J) (hback : PullsBack ψ I J)
    (hround : ∀ f, ψ (φ f) = f) {f g : R} :
    EqMod I f g ↔ EqMod J (φ f) (φ g) :=
  ringIso_both_ways φ hφ ⟨hfwd, reflects_of_pullsBack φ ψ hback hround⟩

/-! ## `integral` — the fourth shape, and it is partiality

Reduction mod `p` is not a total map on `ℤ_(p)`-coefficients: it is undefined
on anything with `p` in its denominator.  The kernel's own instance is
`d2 = h_2 - (3/8)h_1²`, which travels a perfectly polynomial map and does not
reduce mod 2 because 8 = 2³.

So `integral` is not a property of a map — it is the question of whether the
map is DEFINED at this claim.  Modelled with a partial map, the transport
theorem simply gains a definedness hypothesis, and nothing else changes. -/

/-- A partial map, which is what reduction mod `p` actually is. -/
def Defined {R S : Type u} (φ : R → Option S) (x : R) : Prop := (φ x).isSome

/-- Transport across a partial map needs it defined at the difference.  The
    conclusion is about the images, so there is nothing to say when there are
    no images -- and that is the whole content of the gate. -/
theorem partial_transport {R S : Type u} [Sub R] [Sub S]
    (φ : R → Option S) {I : Ideal R} {J : Ideal S}
    (hcarry : ∀ f y, I f → φ f = some y → J y)
    {f g : R} {d : S} (hdef : φ (f - g) = some d) :
    EqMod I f g → J d :=
  fun hfg => hcarry _ _ hfg hdef

/-- And the failure is not a false claim -- it is the absence of one.  With the
    map undefined there is no image to state anything about, which is the same
    shape as `coefficients_in_base`: the descended statement "is not a false
    claim, it is not a claim". -/
theorem undefined_gives_nothing {R S : Type u} [Sub R]
    (φ : R → Option S) {f g : R} (h : φ (f - g) = none) :
    ¬ Defined φ (f - g) := by
  simp [Defined, h]

end GrandPortage
