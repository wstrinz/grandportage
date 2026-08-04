# Operation contracts

**Status:** executable pilots plus one graph-bound localized-unit contract
**Authoritative runtime semantics:** graph format 3, kernel epoch 10
**Formal shadow:** `lean/GrandPortage/OperationContract.lean`


Kernel epoch 10 retains the epoch-9 point-scope split and adds checked local
EMPTY authority. Epoch 9 made point scope explicit on models: exact certificate
arithmetic belongs to `coefficient_domain`, while existence and geometric
coverage belong to `point_universe`. The first consumer is partition
verification, where a geometric hole is a refutation only for a model declared
over `ALGEBRAIC_CLOSURE`; over `BASE` it remains geometric debt. These fields
are deliberately narrower than a general coefficient-algebra ontology.

Grand Portage now has a small operation-contract foundation. Its first job is
to keep three statements from collapsing into one:

1. **Intended semantics** — what an exact mathematical implementation produces.
2. **Checked guarantee** — what local translation validation establishes about
   this particular output.
3. **Licensed consequences** — what follows from that checked guarantee.

A backend success, a parsed result, and a locally verified output do not by
themselves prove that the backend returned the complete mathematical object.

## Contract shape

The Lean core is:

```text
OperationContract Params Source Target
    precondition
    semanticRelation
    checkedGuarantee
    transportObligations
    semantics_entails_checked
    claimTransformerTheorems
```

The theorem points from exact semantics to the checked guarantee, never in the
tempting reverse direction. Claim transformers are theorems derived from these
relations, not strings stored inside the contract. The immutable values in
`grandportage/contracts.py` are runtime shadows for constructors, verifiers,
and audits; they are not proof objects.

## Relational point semantics

The point layer now has a backend-neutral binary relation between differently
typed point spaces. Existential direct image and universal precondition form an
adjunction, with identity and composition laws proved in Lean. Two independent
properties compile to the familiar point cells:

```text
total on source       NONEMPTY along; EMPTY against
surjective on target  NONEMPTY against; EMPTY along
```

Both properties compose. Same-coordinate refinement is totality of the equality
relation, while finite chart lifting supplies surjectivity. This does not absorb
coordinate-ring identities or evidence freshness: those remain separate sorts.

For `PREDICATE`, the same variance also requires the source and target
predicates to correspond along the relation; totality alone cannot type a claim.

The runtime table now compiles every point cell from those two capabilities.
Only three evidence-sensitive refinements are named as overrides: scheme-scoped
emptiness under base extension, closed predicates on an exact image, and an
existential witness for image lifting. `IDENTITY` remains an explicit table
fragment because its rules concern coordinate rings, expression typing, and
certificate scope rather than relations between points.

## Saturation pilot


The saturation and elimination runtime `OperationContract` values now expose
their point relation, baseline totality/surjectivity, predicate transformer,
and conditional capabilities. Construction refuses a contract whose baseline
capabilities disagree with its edge type; stronger facts such as elimination
point-surjectivity must remain named, verifier-earned conditional authority.
This is the first direct runtime projection of the richer contract shape.

For source ideal `I`, polynomial `f`, and recorded output ideal `J`:

```text
exact semantics          J = I : f^∞
checked containment      I ⊆ J
checked generators       each recorded generator of J lies in I : f^∞
formal generated lift    J ⊆ I : f^∞
open                     I : f^∞ ⊆ J
```

Lean proves the one-sided lift and pins the completeness gap with `I = (6)`,
`f = 2`, `J = (6)`: all local checks pass, while `3 ∈ (6) : 2^∞` and
`3 ∉ (6)`. Source containment still licenses the existing
`NECESSARY_CONDITION / AGAINST / IDENTITY` move.

## Elimination pilot

Elimination is genuinely multi-sorted. Let `R` be the source ring, `S` the
retained-coordinate ring, `i : S -> R` the coordinate inclusion, `I` the source
ideal, and `J` the recorded output ideal:

```text
exact semantics             J = inverse_image(i, I)
no-invention check          J subset inverse_image(i, I)
section completeness        r : R -> S, r o i = id, r(I) subset J
Groebner completeness       checked pure-lex basis gives inverse_image(i, I) subset J
combined ideal authority    J = inverse_image(i, I)
section point authority     every target-valued point lifts through r
```

`verify.operation_output` checks the eliminated/retained variable partition,
expression typing, and source membership for every recorded target generator.
It proves only no-invention.

`gp verify-elimination EDGE --section '{"y":"x^2"}'` checks a polynomial
retraction. Retained variables are fixed literally; eliminated variables map to
polynomials in the retained ring; every substituted source generator is proved
inside `J` with independently expanded cofactors. This is stronger than ideal
completeness: evaluating the checked polynomials at any target-valued point
produces a source-valued point that projects back identically.

`gp verify-elimination-groebner EDGE` covers eliminations with no polynomial
section. Singular searches for a bounded pure-lex basis and representation
witnesses; GP's backend-neutral exact checker replays source span, every
critical pair, the elimination order, and retained-basis membership. This earns
ideal completeness only. Search is untrusted and point lifting is not inferred.

`gp materialize-elimination-groebner --src SOURCE --vars u,v --produces TARGET`
is the producer-side form of the same contract. The caller supplies no target
ideal: the retained pure-lex basis becomes `TARGET`. Before anything is
recorded, GP requires two independent current verdicts on the in-memory model
and constructor edge: `verify.operation_output` proves no-invention, and
`verify.elimination_groebner` proves completeness. Only if both pass are the
model, edge, both verdicts, and producer provenance submitted to `S.append` as
one prevalidated batch. Artifact publication precedes that append, so an append
failure may leave content-addressed orphans; this is not claimed to be a
crash-atomic filesystem transaction. The command grants exact contraction, not
point-surjectivity or geometric image authority. Use `--dry-run` to exercise the
same checks without recording artifacts or graph events.

`gp verify-elimination-point-lift EDGE --certificate ...` supplies the missing
point authority independently. A finite certificate gives principal-open
charts: on guard `g != 0`, each eliminated coordinate is a polynomial numerator
divided by a bounded power of `g`. A final polynomial fallback applies when all
guards vanish. That dichotomy covers every point over the declared exact field.
For each source generator, Singular searches for bounded localization/radical
membership cofactors and GP exactly re-expands the stored identity. The search
is untrusted; the persisted finite equalities are the proof object.

The cusp normalization is the first positive pressure case:

```text
Q[u,y,x]/(u^2-x, u^3-y) -> Q[y,x]/(y^2-x^3)
open x != 0:  u = y/x
fallback x = 0: u = 0
```

The fallback is pointwise rather than ideal-theoretic: `y` is not literally in
`(y^2-x^3,x)`, while `y^2` is. The certificate therefore records the checked
vanishing power instead of conflating ideal membership with radical membership.
This earns point-surjectivity but does not earn exact contraction; the latter
still needs a section or Groebner completeness certificate plus no-invention.

## Coefficient-expansion pilot

Bounded polynomial unknowns are lowered to scalar coefficient coordinates
before the exact-affine kernel sees them. The deterministic command

`gp verify-coefficient-expansion --spec lowering.json`

translation-validates that boundary without trusting the script that emitted
the rows. A closed `coefficient_expansion_v1` specification declares the
polynomial parameter, source template variables, scalar coefficient ring,
bounded-variable caps and ordered coordinates, exact substitution images, and
the recorded coefficient rows for each source equation.

The checker distinguishes two contracts:

```text
selected rows   polynomial identity -> the checked rows vanish
complete rows   polynomial identity <-> every row 0..degree vanishes
```

Complete mode rejects a missing overflow coefficient, a wrong or invented row,
a cap with the wrong number of coordinates, coordinate reuse, reordered pack
maps, source equations that smuggle in lowered coordinates, and rows that still
contain the polynomial parameter. Selected mode remains useful for sound kills,
but deliberately reports no converse. The JSON report is translation evidence;
it does not mint elimination or graph-transport authority by itself.

The first live JC assay puts cap 1 on the seven retained polynomials. With cap 0
on `dm4`, all sixteen coefficients of `G1,G2,G3,G5` are checked in fifteen
scalar coordinates. The retained tuple `dm2=1`, `d2=y` satisfies every one of
the seventeen scalar exact-target identities, while its only unrestricted lift
is `dm4=-y/2`; the cap-0 coefficient fiber contains the unit `3/2`. Thus the
scalar point-lift theorem does not survive the degree cap. Raising `dm4` to cap
1 admits the independently checked nonunit example `dm2=y`, `d2=1`,
`dm4=-y/2`.

Lean formalizes finite coefficient vectors, the selected-versus-complete
distinction, polynomial reconstruction, and the precise payoff: coefficient-
level point-surjectivity supplies an existential bounded `dm4` vector, never a
uniqueness theorem.

## Principal-open localization certificate pilot

`gp verify-localization-membership --spec localization.json` checks one
backend-neutral `localization_membership_v1` proof. The specification records
the exact coefficient characteristic and polynomial ring, the ambient ideal,
a finite nonempty list of principal-open guards, and a rational expression as
one polynomial numerator plus one denominator power for every guard.

The certificate separately records a guard-monomial multiplier and cofactors:

```text
(product guard_i^localization_power_i) * numerator
    = sum cofactor_j * ideal_generator_j
```

GP normalizes every polynomial, bounds guards and powers, requires the recorded
membership target to be exactly the left side, and expands the cofactor identity
with the small exact-polynomial checker. The sole licence is
`identity_in_declared_localization_only`. It does not mint an ambient identity,
an edge transport, or a point-lifting fact. This is deliberate: the existing
`RESTRICTION` operation remains the point locus with the same ideal, while this
certificate expresses what becomes zero in the localized coordinate algebra.

Lean's `MultiSatMem`, `GuardMonomial`, and `localization_certificate_sound`
state the same contract. This first surface is standalone translation evidence.
Binding it to a campaign model, elimination pivot, or persisted verdict should
be earned by live H3 use rather than added speculatively.

The positive section control eliminates `y` from `(yx-1, y^2-x)` and uses
`y -> x^2`. The hyperbola `(xy-1) -> (0)` is the decisive separation: its
elimination ideal is exact and the Groebner route can certify it, but the target
point `x=0` has no lift. Exact contraction is therefore not point-surjectivity.

A harder eight-variable live pressure test exercised the other failure mode. A
plausible three-generator retained system was not the full elimination ideal: a
21-element pure-lex basis contained 17 retained elements and exposed a concrete
missing relation. The verifier refused exact promotion, preserving the target as
a sound necessary system. This is the intended operational value of separating
the contract from the backend program.

Lean defines `EliminationCompleteness`, the section and basis boundaries, and a
coefficient-algebra-relative `EliminationPointSurjective` proposition. It proves
that the section lifts every valid target evaluation, and separately provides a
countermodel showing exact contraction alone has no point-lifting consequence.
It now also defines `RetainedCoordinateExpressible`: a source predicate factors
through the target evaluation on retained coordinates. Lean proves that
point-surjectivity transports every such predicate, and gives a countermodel
showing that point-surjectivity alone cannot transport an unrelated predicate.

## Authority and kernel epoch 8

Kernel epoch 8 keeps six facts separate:

- **exact contraction** requires current no-invention plus either a checked
  polynomial section or a checked pure-lex certificate;
- **geometric closure authority** is enough for a closed predicate but not an
  arbitrary point predicate;
- **point-surjective image authority** requires current no-invention plus a
  checked global polynomial section or finite piecewise rational lift cover. A
  pure Groebner certificate never opens it;
- **retained-coordinate expressibility** belongs to the claim, not the map;
- **equivalence-rewrite authority** requires a literal identity map or a current
  verified ring isomorphism, with predicate syntax moving contravariantly;
- **predicate-pullback authority** requires a concrete point map: currently a
  matching exact identity-coordinate map or a checked elimination projection.

The runtime projection of the last three items is intentionally small:

```json
{"condition":{"all":[
  {"relation":"ZERO","expression":"x^2-1"},
  {"relation":"NONZERO","expression":"x"}
]}}
```

Every atom is parsed in the source model's exact polynomial ring. Before a
section-certified constructed elimination, the runtime may reindex that syntax
through any chain of checked coordinate changes. `forward` is the source-to-
target point map, so `ALONG` expression rewriting uses `inverse`, while
`AGAINST` uses `forward`. Substitution is simultaneous and exact. A literal
`IDENTITY_MAP` preserves syntax; a nonidentity mapped equivalence requires both
an authored `ring_iso: true` contract and a current `VERIFIED` verdict.

The rewritten expressions must parse in the retained-coordinate target ring.
An all-`ZERO` conjunction thereby establishes closedness; a conjunction
containing `NONZERO` can travel by the stronger point-lifting theorem. A
structured condition naming an eliminated coordinate is refused even if it is
closed, and a manually asserted `zariski_closed` flag cannot override that type
failure. Free-text predicates remain legal and conservative. Unsupported or
unverified passes may still transport the proposition abstractly, but they lose
machine-readable expression typing and cannot unlock a later elimination.

Lean also defines partial elimination point lifts and an n-ary finite cover.
It proves that joint coverage plus each chart's checked lift/projection law
entails `EliminationPointSurjective`; no individual chart mints global
authority. The runtime's rational charts and all-guards-zero fallback are one
finite exact-affine implementation of those premises.

Lean defines generic predicate `Pullback` along a point map, proves that an
everywhere-valid target predicate pulls back to the source, and proves identity
and composition laws. `MappedEquivalence` specializes that calculus in both
directions and pins the contravariant orientation. The Python projection now
recognizes three concrete maps: checked equivalence substitutions, literal
identity-coordinate maps with matching exact endpoint rings (enforced for exact
RESTRICTION endpoints), and currently
checked constructor-built elimination projections. The last two support the
ordinary `AGAINST` predicate pullback law. No synthesized claim is persisted
and the campaign graph is not mutated.

Manual `IMAGE_CLOSURE` declarations continue to state their closure relation but
do not mint point-surjectivity. Constructed eliminations earn only what their
current evidence proves. The persisted condition syntax advances graph format 1
to 2, and the newly licensed nonclosed predicate transport advances kernel epoch
4 to 5; verified coordinate-map composition then advances the runtime to epoch
6, and generic concrete point-map pullback advances it to epoch 7. Finite
piecewise point-lift covers then advance it to epoch 8 because they license
new nonclosed predicate transports, without changing graph syntax.
Kernel epoch 9 additionally separates exact coefficient domains from the point
universes in which geometric claims are interpreted. The standalone
localization checker adds no graph transport authority and therefore does not
advance the epoch.

Migration remains non-destructive:

```console
gp --graph old/.portage/graph.jsonl migrate --to-current-kernel
```

The source is untouched, prior verdicts remain history but stale, absent
`condition` fields stay absent, and the new fold re-audits transport under epoch
10.

## Implemented contract exposed by rows 7--8: localized unit ideal

The first real rows 7--8 replay supplies a contract smaller than general
localization and stronger than an arbitrary localized identity:

```text
LocalizedUnitIdeal
  object sort:       exact-affine quotient with declared inverted guards
  proposition:       1 belongs to the localized ideal
  evidence:          guard monomial D and cofactors with D = sum h_i f_i
  local consequence: no points over any nontrivial target algebra
  transport:         none by itself
```

`localization_membership_v1` already checks the evidence when its numerator is
`1`. Lean theorem `localized_unit_ideal_has_no_point` proves the point-level
consequence from precisely the localization interface: ideal equations vanish,
guard monomials become units, and the target is nontrivial. The q control uses
`D=q^3*t^2`; the p control uses `D=p^4*t^2`.

Kernel epoch 10 implements that distinction as
`LOCALIZED_UNIT_IDEAL_CERT` plus verifier `verify.localized_unit_ideal`.
`gp verify` searches a bounded guard-monomial frontier, independently expands
any returned cofactors, and persists a proof envelope bound to the exact claim,
model, characteristic, variables, generators, and guards. Search exhaustion is
`UNVERIFIED`. A successful verdict supports only local `EMPTY` on that model;
it grants no parent/source membership, chart coverage, whole elimination chain,
or H3 conclusion. Existing RESTRICTION/ALONG/EMPTY remains refused.

The companion bracket-receipt edge is a different contract. Its lowering uses
Laurent support intervals, formal derivatives, and multiplication by declared
parameter powers before coefficient comparison. Ordinary
`coefficient_expansion_v1` starts after those operations and cannot certify
them. The pipeline is therefore compositional:

```text
frozen source/template receipt                    outside GP authority
  -> laurent_lowering_v1                          implemented
       finite exact inputs
       bounded add / multiply / coefficient scale
       formal derivative / declared y-shift
       exact Laurent equality
       explicit support-clearing shift
       canonical sparse-polynomial export
  -> exact export-to-image binding
  -> coefficient_expansion_v1                     implemented
       selected rows: necessary only
       complete bounded rows: equivalence
```

`laurent_lowering_v1` is a closed straight-line language, not a general CAS.
Its coefficient ring reuses GP's bounded exact-polynomial checker and its
Laurent support is an explicit finite integer-keyed map. A successful replay
licenses the declared Laurent equalities. A distinct export license says only
that the canonical polynomial is the declared monomial shift of the computed
Laurent value; the coefficient checker accepts that wire object directly.
`laurent_coefficient_pipeline_v1` verifies both nested specs
and requires total, unique, exact export-to-image bindings. Thus a hand-edited
intermediate cannot inherit upstream authority merely because its own scalar
rows are self-consistent. It does not prove that the input
template came from the source geometry, that a chart map is valid, that an
antiderivative exists, or that a scaling factor is invertible. The frozen replay is
`fixtures/jc_rows78/laurent_lowering_v1.json`; the bound two-pass artifact is
`fixtures/jc_rows78/laurent_coefficient_pipeline_v1.json`. Its `F_-7` export passes complete
`coefficient_expansion_v1` replay. In the first rows 7--8 replay the
corrected depressed-chart equations pass exactly, while
the old `G=0` right-hand side and a `21 -> 20` mutation fail.

Directly entering the final scalar rows would validate their arithmetic while
skipping the load-bearing chart translation, so it remains intentionally
refused as a promotion shortcut.

### Exact factor-power receipt

`factor_power_v1` is a translation validator for identities
`equation = scalar * base^k`. It recomputes the identity over the declared exact
polynomial ring, requires `1 <= k <= 64`, and admits as `scalar` only one
nonzero coefficient times a monomial in explicitly declared unit generators.
The pass earns only `exact_declared_unit_monomial_times_positive_power_identity`.

The semantic contraction is deliberately a separate step. Lean theorem
`unit_times_positive_power_zero_implies_base_zero` proves it from exactly three
consumer obligations: the equation evaluates to zero, the interpreted target
has no zero divisors, and the coefficient plus generator factors evaluate to
units. Runtime reports those debts and grants no base-vanishing, component,
emptiness, source-membership, or claim-transport authority.

`fixtures/jc_p_axis/factor_power_v1.json` is the first live projection. It
replays the distinct JC receipts `E[3,22] = 5*(c9_11+p*t)^2` and
`E[5,22] = (-5*p)*(c9_11+p*t)^2` in the scoped axis ring. It intentionally does
not claim that the equations vanish in the pinned quotient or that the whole
axis is empty; those need the still-explicit localization/domain bridge and the
affine consequence receipt.

The companion `factor_power_affine_contradiction_v1` pass composes that receipt
with a deliberately narrow affine solve. It requires the selected base to be
literally `pivot - solution`, with the solution independent of the pivot, then
simultaneously substitutes the solution into a second equation and requires the
recorded residual to be one nonzero coefficient times declared unit generators.
For the JC fixture this checks
`c9_11 = -p*t` and `E[1,22] |_(c9_11=-p*t) = 5*p*t^2` exactly.

Lean theorem `factorPower_and_unitConsequence_are_incompatible` links the two
passes semantically from right-inverse witnesses for both unit monomials. The
runtime result remains a contradiction *pattern*: both equations must still be
bound to the same interpreted model, and the domain/unit premises discharged,
before any local emptiness authority exists.

The v0.19 JC p-axis adapter performs that concrete binding and, importantly,
does not add graph authority for this specialized schema. It algebraically
compiles the selected equations and affine residual into an existing
`localization_membership_v1` cofactor identity for a declared guard monomial.
`verify.localized_unit_ideal` then replays the smaller certificate against the
exact graph model and may mint only local `EMPTY`. Thus the factor receipt is a
producer language while localized ideal membership remains the authority
language.
### Exact binary product split

`product_split_v1` independently recomputes identities
`equation = scalar * left * right`, requiring distinct nonzero factors and the
same bounded declared-unit-monomial scalar language as factor-power receipts.
The live fixture checks
`E[2,0] = 10*(c6_0*p+c8_0)*(c7_0*p+c9_0)` and separately checks the landed
`E[4,0] = -p*E[2,0]` identity as the scalar `-10*p` times the same factors.

Lean theorem `unit_times_product_zero_implies_factor_zero` proves the local
semantic disjunction in a no-zero-divisors target with a scalar unit witness.
The receipt verifier itself creates no graph authority. A distinct
`PartitionContract` now represents the n-ary boundary, rather than forcing it
into the one-source/one-target `OperationContract` record.

`gp construct product-split --src MODEL --spec RECEIPTS.json --receipt ID`
exposes the contract through the supported dry-run/`--declare` campaign path;
`operations.product_split` compiles it into two same-ring branch
models, two branch-to-parent `NECESSARY_CONDITION` edges, a covering claim, and
a partition. It does so only when the checked equation is literally a parent
generator and the scalar is a nonzero constant coefficient. The existing
`verify.partition_exhaustiveness` then independently rechecks the emitted
ideals; the real JC `E[2,0]` cover passes against Singular. The valid `E[4,0]`
receipt has scalar `-10*p` and is intentionally refused for branch construction:
its cover is true only on the p-open locus, while the current ideal-only cover
verifier ignores localization guards.

Recombining later branch claims still uses the pre-existing n-ary kernel rule:
all branches must carry the supported claim kind and the exact partition must
have a `VERIFIED` exhaustiveness verdict.

### Affine coordinate normalization

`AffineCoordinateSolve` is the exact consumer immediately after a checked
product split. Given a literal source generator `x - s = 0`, where `s` is a
polynomial independent of `x`, the constructor emits the point-forward map
`x -> x-s`, its inverse `x -> x+s`, and rewrites every source generator and
open condition simultaneously through the inverse. The target keeps the same
ring variables and has `x = 0`; keeping the zero coordinate is deliberate,
because the current ring-isomorphism verifier requires identical endpoint
variable sets.

The edge is an authored `EQUIVALENCE` with `ring_iso: true`, not a pre-verified
identity license. `verify.ring_iso` must still check both ideal pullbacks and
both map compositions before structured coordinate-ring identities cross it.
Lean's `AffineCoordinate.lean` packages exactly those inverse-map laws as a
`MappedEquivalence` and proves the normalized pivot equation. On the JC product
branches this realizes `c8_0 -> -p*c6_0` and, symmetrically,
`c9_0 -> -p*c7_0`; the left branch passes against real Singular.

`exceptional_factor_column_v1` is a bounded evidence contract that can justify
using the same affine operation without itself minting an edge. It freezes a
complete finite family of exact coefficient columns, checks declared common-
factor decompositions under named restrictions, and separates a surviving
unit-pivot determination from compatibility equations. A graph-bound consumer
would still have to bind the exact model and translation. Lean's
`PivotIndependent` theorem supplies the semantic bridge used by the first JC
consumer: if every downstream predicate ignores the solved pivot, translating
that pivot leaves the model literally unchanged. Standalone graph effect is
`NONE`.

`affine_fiber_block_v1` handles the next bounded composition seam. Its runtime
instance must bind an exact affine coefficient matrix, audited unit pivots,
rank witnesses, a residual vector or explicit declaration that the residual is
missing, and the compatibility pairing left after solving the determined
coordinates. Lean's `DeterminedAffineFiber` contract proves that a correctly
characterized block has a point exactly on its compatibility locus and that
its determined coordinates are unique. Neither the matrix rank nor this Lean
theorem supplies source sufficiency: graph binding still requires a concrete
necessary-condition model, and reverse transport requires independent
completeness evidence.

### Ordered localized triangular solves

`localized_triangular_solve_chain_v1` is the bounded composition envelope for
native elimination ladders. Every step names the exact current equation,
requires a coefficient that is one nonzero rational scalar times a monomial in
declared localization generators, solves one pivot without referring to any
chain pivot, substitutes simultaneously through the remaining ordered
generators, and binds both endpoint state fingerprints. The envelope also binds
the native receipt id and SHA-256. Reordering individually valid pivots or
replaying one against another chain state therefore fails.

The first live fixture starts from the five exact JC top-face equations in row
order `(2,5,1,4,3)` and validates the landed solutions with no normalization
debt. The second source face exposed a deliberately refused v1 case: its
polynomialized solutions use `45*t^3=-3`, and every literal discrepancy is a
multiple of `15*t^3+1`. `localized_triangular_solve_chain_v2` records that
persistent equation and checks an exact aligned cofactor at every step. Context
generators may not contain a chain pivot, so v2 is not an implicit general
quotient simplifier.

Lean's `normalizedEquation_zero_iff_affine_zero` proves the one-step semantic
bridge from the exact receipt, context vanishing, a unit witness, and a
no-zero-divisors target. The explicit-inverse corollary records how an adjoined
`unit * inverse = 1` equation supplies that unit witness.
`MappedEquivalenceChain` proves that semantically bound steps compose and
preserve witnesses and emptiness in both directions.

The isolated JC authority adapter supplies two graph-bound consumers. For the
top face it algebraizes the declared `t` principal open by adjoining `GP_INV_t`
and `t*GP_INV_t-1`. For the normalization-bearing second face it recognizes
that `15*t^3+1=0` already supplies the polynomial inverse `-15*t^2`, then checks
that inverse by an exact ideal representation instead of adding a coordinate.

Both chains compile their five translations into a mapped `EQUIVALENCE` and a
closed `mapped_ring_iso_v1` envelope. The producer composes explicit cofactors
for every forward and inverse ideal pullback from the checked step receipts.
`verify.ring_iso` independently expands every cofactor identity and checks both
map round trips. The general solver-backed map verifier remains available and
agrees on the smaller top face; removing its inverse equation makes it fail.
A bad proof envelope is `UNVERIFIED`, not a refutation of the authored map.
Current verdicts license identity transport only between the exact endpoint
quotient rings. They do not bind native source extraction, chart coverage,
parent models, actual-source membership, or H3.

The standalone v1/v2 evidence schemas themselves retain graph effect `NONE`.
Graph format 4 owns the optional proof envelope and ring-isomorphism verifier
version 3 owns its exact replay. No edge type, claim kind, transport cell, or
kernel meaning changed, so kernel epoch 10 remains current.

### Depth-6 graded face extraction

The frozen JC depth-6 receipt provides complete sparse maps for R2B and beta,
so the isolated adapter binds two downstream affine rewrites without inventing
a new graph operation. JC commit cb3136c additionally supplies all 25
depth-2..6 face bodies and the 23-step ordered solve chain. The independent
chain replay checks those transitions but, by itself, only authenticates the
selected face tables.

graded_face_extraction_v1 closes the translation-validation seam. Its routine
checker expands five exact reduced E-system row polynomials under the declared
finite root supports and matches every landed face. Its stronger audit
reconstructs the reduced rows from the normalized root series, fourteen
unit-triangular P-side solves, the defining E-system formula, and the invariant
substitution. Lean's GradedFaceExtraction contract proves the semantic
direction: a source witness lowers to a selected-face witness, so selected-face
emptiness refutes the source. A countermodel proves that selected-face survival
does not supply a source witness.

A follow-up full-template assay establishes an honest graph endpoint without
raising a checker bound. The graph store and core sparse parser do not impose
the specialized checkers' 64-variable ceiling. Complete expansion gives a
78-variable model with 147 nonzero coefficient equations; the selected 25 are
literal members of that generator list. The edge is therefore the existing
NECESSARY_CONDITION relation in one coordinate ring.

Containment verifier version 3 adds one backend-free structural proof case:
when every target generator occurs verbatim among the source generators, exact
parsing plus unit cofactors proves I(target) is contained in I(source).
Malformed equal payloads are refused, and every other case falls through to
the existing backend reduction. The disposable JC campaign earns VERIFIED,
has zero findings, and spawns no CAS.

The persisted graph is about 39.5 MB because the read model duplicates large
structured generators. That is evidence for content-addressed generator
bundles or projection interning, not for flattening or omitting the source.
The remaining upstream premise is original polynomial-pair membership in the
reduced E-system. Reverse lifting, chart coverage, H3, and verdict promotion
remain refused.

No graph format, edge type, claim kind, transport cell, or kernel meaning
changed, so graph format 4 and kernel epoch 10 remain current. Containment
verifier version 2 verdicts become stale and must be rerun under version 3.

## Trust boundary

`grandportage.evidence` provides the common `AffineContext`, read-only
`EvidenceEnvelope`, and authority manifest used to describe this boundary.
Every specialized standalone schema currently declares graph effect `NONE`.
The manifest distinguishes graph-bound `LOCAL_EMPTY` from
`IDENTITY_TRANSPORT`: `verify.localized_unit_ideal` is scoped to one exact
localized model, while `verify.ring_iso` is scoped to its exact endpoint
quotient rings. This is descriptive static metadata, not a runtime plugin registry.

```text
operation contract       mathematical intent and transport theorems
backend lowering         concrete Singular/M2 program and decoder
translation validation  per-run typing, membership, and certificates
authority/provenance     who checked what, under which epoch and inputs
artifact store           exact immutable programs and raw transcripts
```

The next earned steps are explicit concrete maps for the remaining nonidentity
operations, broader chart coverage beyond the current Q/prime-field bounded
principal-open form, and more live use in actual research campaigns. Contracts
remain compiled constructor metadata until the pilots show that persisting them
in the IR buys more than it costs.
