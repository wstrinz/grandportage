# grand-portage-lean

A shadow formalisation of Grand Portage's transport calculus. **Not
authoritative.** Its job is to try to break the ontology, not to bless it.

## Why it exists

A measurement against the Python kernel found the transport table splits into
two halves with very different characters:

|                    | agree with the generic rule | disagree | conditional |
|--------------------|------|------|------|
| point cells (36)   | **27** | 3 | 6 |
| IDENTITY cells (12)| 1 | 3 | **8** |

The point half looks like one subset argument repeated. The identity half is
where every hand-entered boolean lives — `ring_iso`, `identity_origin`,
`integral`, `coefficients_in_base` — and none of it follows from points.

That historical measurement has now become an executable architecture. The
Python kernel compiles all 42 point cells (including `UNTYPED`) from relation
totality and surjectivity, with exactly three named evidence refinements:
base-extension scheme emptiness, closed exact-image predicates, and existential
image witnesses. Lean proves the corresponding predicate-transformer laws.
The 14 `IDENTITY` cells (including `UNTYPED`) stay explicit because point maps
do not determine coordinate-ring equality.

## What is here

`GrandPortage/Points.lean` — models as predicates, `Refines` as inclusion.
The three cells inclusion licenses, proved; the three it refuses, with
countermodels. Generic predicate `Pullback` along a point map has its everywhere,
identity, and composition laws here. Plus `Cover` and the partition recombination
law, which is why
a partition is a distinct inference form rather than another edge type.

`GrandPortage/RelationalTransport.lean` - the common point semantics for
operations that are neither inclusions nor total functions. Existential image
and universal precondition form an adjunction; identity and composition laws
are proved. Totality and point-surjectivity derive the four sound
`EMPTY`/`NONEMPTY` directions and compose independently. Same-coordinate
refinement is recovered as totality of the equality relation. Ideal identities
and evidence authority deliberately remain outside this point sort.

The compiled point-contract fragment now mirrors the runtime Boolean compiler.
Its predicate theorems expose an additional premise hidden by the table shape:
endpoint predicates must correspond along the relation. Totality or
surjectivity alone transports existence/emptiness, but cannot type a predicate.

`GrandPortage/JCDm4Valuation.lean` - the integer-arithmetic spine of the JC
polynomial-lift conjecture. If a rational `dm4` had a pole, the cancellation
balances forced by `G1` and `G2` make `c*dm4` strictly lower in valuation than
every other `G3` term, so `G3` cannot vanish. This corrects the final inequality
in the initial informal sketch. It deliberately stops short of claiming the
full polynomial theorem: deriving the balance equations from an actual
polynomial valuation and handling zero charts remain explicit obligations.

`GrandPortage/MappedEquivalence.lean` - an invertible change of coordinates
transports witnesses but does not imply literal solution-set containment in
either direction. This keeps mapped `ring_iso` evidence distinct from a
same-coordinate `containment` claim. A non-involutive integer translation pins
`forward` as the source-to-target point map, preventing polynomial pullback's
contravariance from silently reversing the user-facing convention. It now also
defines predicate reindexing in both directions, composes verified coordinate
changes, and proves that rewriting through a composite is definitionally the
same as rewriting step by step.

`GrandPortage/Identity.lean` — `EqMod I f g := I (f - g)`, the one identity
cell that derives from ideal containment, and the ℤ counterexample refusing the
other direction. Then `Carries`, the shape the remaining eight gated cells
appear to share: an identity crosses when the induced map sends the source
ideal into the target ideal.

`GrandPortage/BackendTrust.lean` - the M2 authority boundary. Backend success,
parsing, validation, and provenance freshness are separate facts. Replayable
certificates are independently checked; direct normal-form decisions remain in
the named backend/verifier TCB; verifier-native structural decisions explicitly
spawn no backend artifact.

`GrandPortage/OperationContract.lean` - the first backend-neutral operation
contracts. Exact saturation and elimination semantics, locally checked
guarantees, and licensed transport consequences are distinct predicates. Ideal
generation lifts generator certificates to ideal-level sound envelopes.
Elimination completeness is a separate inclusion; a polynomial retraction
certificate proves it in favorable cases, while the general Groebner boundary
isolates endpoint interpretation and finite checked basis facts from the
still-explicit Buchberger/elimination theorem. Lean proves the final semantic
bridge here; it does not yet verify the Python parser or Buchberger checker.
Either completeness route combines with no-invention to recover exact
contraction. The section additionally lifts every target-valued point; a
separate countermodel proves exact contraction alone has no point-surjectivity
consequence. Partial elimination lifts and `FiniteEliminationPointLiftCover`
then prove that an n-ary family of locally sound charts with joint coverage
earns the same point-surjectivity proposition; no chart individually does.
`RetainedCoordinateExpressible` states that a source predicate factors through
target evaluation on the retained coordinates. Lean proves that
point-surjectivity transports every such predicate and separately pins the need
for expressibility with a countermodel.

`GrandPortage/Localization.lean` - saturation semantics for one or many
declared guards, plus the exact certificate shape implemented by
`localization_membership_v1`. It proves localized equality does not imply
ambient ideal membership. The rows 7--8 pilot adds the complementary unit-ideal
bridge: if a permitted guard monomial times `1` belongs to the ideal, no point
into a nontrivial target can satisfy the localized quotient. The runtime
independently replays that premise and may persist the derived local `EMPTY`
claim only through `LOCALIZED_UNIT_IDEAL_CERT`; ordinary localized membership
still earns no point authority.

`GrandPortage/CoefficientExpansion.lean` - bounded polynomial unknowns as finite
coefficient vectors and their reconstruction as finitely supported formal
polynomials. Selected coefficient rows are proved necessary only; complete row
coverage is proved equivalent to polynomial vanishing. Coefficient-level point
surjectivity yields an honest bounded witness, while a countermodel prevents it
from being silently strengthened to uniqueness. This is the semantic contract
implemented by the runtime coefficient-expansion checker; the Lean theorem does
not verify the Python parser or substitution engine.

GrandPortage/GradedFaceExtraction.lean - the one-way semantic contract used
by the JC depth-chain assay. Vanishing of a source coefficient family entails
every explicitly selected face equation, while a two-coefficient countermodel
prevents a proper selection from being treated as sufficient. A bounded
extraction is packaged as a total point map: source nonemptiness moves forward
and selected-face emptiness moves back, but face survival earns no source
witness.

`GrandPortage/LaurentLowering.lean` - coefficient-function semantics for the
finite Laurent compiler pass. It proves formal differentiation is additive
under the exact coefficient-ring law, proves checked equality survives a
declared monomial shift and coefficient scaling, proves the support bound that
makes such a shift an ordinary polynomial export, combines that support fact
with equality into the two-pass export contract, and formalizes the live chart
negative control: the legal instance `G=y^-5` makes `6*y^2*G` nonzero, so the
depressed row cannot be replaced by the covered-chart zero row. Runtime
parsing, finiteness budgets, and polynomial arithmetic remain translation-
validation implementation rather than Lean claims.

`GrandPortage/Conditions.lean` — **that conjecture is refuted.** The four gated
conditions turn out to be three different shapes, and one of them is not about
the map at all. Details below.

## The first thing this found

The conjecture was that `ring_iso`, `identity_origin`, `integral` and
`coefficients_in_base` are one condition checked four ways. They are not:

| condition | shape |
|---|---|
| `identity_origin: AMBIENT` | the claim lives at a **smaller ideal** — nothing about the map |
| `coefficients_in_base` | **expressibility** — the claim cannot be *written* in the smaller ring |
| `ring_iso` | **Carries and Reflects** |
| `integral` | **partiality** — whether the induced map is defined at all |

That table's second row is itself a correction. The formalisation's first answer
was `Reflects`, and checking it against the Python kernel's own counterexample
said otherwise: for a field extension `Iᵉ ∩ k[x] = I` holds automatically, so
reflection is not what fails. What fails is that the claim cannot be *written*
downstairs — and stating the theorem with `f g : R` puts that in the type, so
the formal version could not see the gate at all. **That absence is what proved
it is an artifact of claims being strings.**

So the eight gated `IDENTITY` cells resisted compression because they answer
four different questions: does the claim hold in a smaller ideal than declared,
does the map push the ideal forward, does it pull it back, and does the map
exist.

`carries_does_not_give_descent` makes the cost concrete: a single `Carries`
gate would have licensed descent, and there is a two-line counterexample in ℤ
refuting that outright.

And one genuine compression did happen. `identity_origin: AMBIENT` is not an
extra rule — it is `eqMod_against` applied from the zero ideal. A corollary
that had been carrying its own gate.

## Factor-power bridge

`FactorPower.lean` formalizes the semantic half of `factor_power_v1` without
formalizing its JSON parser or polynomial arithmetic. `PositivePowerOf` excludes
the exponent-zero case by construction. The main theorem derives base
vanishing from a right-invertible scalar, a positive power, equation vanishing,
and the target's no-zero-divisors law. This is deliberately stronger in
premises and narrower in conclusion than the JC producer packet: GP does not
assume the pinned quotient/localization is a domain merely because a certificate
says so. `factorPower_and_unitConsequence_are_incompatible` then composes base
vanishing with a checked affine consequence and a second unit witness, yielding
`False` without smuggling model binding or emptiness into the theorem.

## Product-split bridge

`ProductSplit.lean` reuses the factor-power unit and no-zero-divisors interfaces
to derive `left = 0 or right = 0` from a checked unit-times-binary-product
identity. `PartitionContract.lean` then makes the n-ary shape structural: an
indexed branch family, a parent-relative precondition, and a theorem that the
family covers the parent. Its binary instance turns a pointwise factor
disjunction into the two expected parent-and-factor branches. It does not prove
runtime model binding or claim recombination.

## Affine coordinate normalization

`AffineCoordinate.lean` specifies the translation-validation boundary after a
product split. An `AffineTranslation` carries concrete forward and inverse
pivot maps, both inverse laws, and the law identifying a zero normalized pivot
with the original affine equation. Lean packages those laws as a
`MappedEquivalence` and proves both point transports. Runtime Python constructs
`x -> x-s` and `x -> x+s`; the CAS ring-isomorphism verifier must discharge the
laws for each actual ideal before identity authority is enabled.

## Ordered triangular composition

`TriangularChain.lean` states the semantic half of the bounded ordered-chain
checker. A heterogeneous `MappedEquivalenceChain` remembers the intermediate
model types and composes step equivalences in order. Lean proves witness
transport in both directions and `IsEmpty src <-> IsEmpty dst`. The Python
checker does not assume those premises: it earns only exact ordered polynomial
substitution and leaves graph model binding, interpreted units, and forward/
reverse point maps as explicit obligations. Runtime v2 can additionally prove
each affine form modulo declared persistent normalization equations, but the
Lean premise still requires those equations to vanish in the interpreted
model before any mapped equivalence is constructed. The explicit
`normalizedEquation_zero_iff_affine_zero` bridge proves both directions from
the checked receipt, context vanishing, unit witness, and narrow zero laws.
`normalizedEquation_zero_iff_affine_zero_of_inverseEquation` records the
compiler bridge from an explicit polynomial inverse equation to that witness.
`affineEquation_zero_iff_shift_zero_of_inverse` and
`affineEquation_zero_iff_constant_zero_of_factor_zero` formalize the two
depth-6 boundary strata without asserting their source extraction or coverage.

## Unilateral recurrence boundary

`ParametricRecurrence.lean` defines a bounded constant-coefficient forward-
shift operator on a declared unilateral domain. It proves that if a sequence
vanishes from `cutoff` onward but is nonzero at `cutoff-1`, then an operator
annihilates exactly when every coefficient below `cutoff-start` vanishes. This
is the semantic theorem behind the corrected JC `(S^8)` receipt: the adapter
checks `start=6`, `cutoff=14`, and `B_13 != 0`; Lean proves the general
backward-induction argument and the absence of any nonzero constant term. The
theorem does not establish those instance premises or discharge H8.

## Scoped first-order fibers

`FirstOrderFiber.lean` separates two inference steps. A nonzero base-only
necessary scalar excludes every compatible point in the named fiber. A
first-order-empty fiber excludes nonlinear lifts through that same base only
when a caller supplies a sound linearization map. The live JC depth-eight
adapter instantiates the first theorem and deliberately leaves the second
bridge unapplied.

## Trust

No `sorry`. Mathlib-free — core Lean only, so a fresh `lake build` is seconds
rather than an afternoon. Axiom audit:

```
hasPoint_along, isEmpty_against, everywhere_against   no axioms
isEmpty_not_along, hasPoint_not_against               no axioms
cover_empty, eqMod_against, eqMod_both_ways           no axioms
eqMod_transports                                      no axioms
generator_mem_generated, generatedIdeal_least,
saturation_semantics_entails_checked,
  saturation_checked_no_invented_elements,
  saturation_checked_transports_identity_against       no axioms
everywhere_not_along                                  propext
eqMod_not_along, checked_does_not_imply_saturation_semantics,
  exact_saturation_does_not_transport_identity_along   propext, Quot.sound
```

The non-empty entries come from `simp`/`omega` on concrete decidable goals,
not from anything load-bearing.

## Build

```bash
lake build
```
