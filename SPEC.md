# Grand Portage operational specification

This is the complete operational reference split from the introductory
[README](README.md). It retains the historical confessions and every verifier
detail; sections are indexed by the command or checker a reviewer must audit.

**Transport typing and obstruction tracking for computational algebra.**

A computation produces an artifact. The artifact does not carry its own license
to conclude. Grand Portage computes which claims remain licensed after each modelling step
under available evidence, and refuses unsupported conclusions.

```
$ gp check
UNSOUND_CONCLUSION  TRANSPORT:INF-C08-HIST
    the C08 residue equation has no solution with all leading coefficients nonzero
      asserted: the branch of the option tree does not exist -- consumed as
                GEOMETRIC emptiness over the theorem's arbitrary char-0 K
      refused : BASE_EXTENSION licenses EMPTY along the extension only at scope
                SCHEME; this claim has scope 'Q(sqrt 17)' (certificate
                NONSQUARE_CLASS, which does not base-change)
      contradicted by: CL-C08-REAL
        (the C08 support has real (hence complex) torus points)
    E8     ALONG   NO  ...
    -> DISCHARGE: Produce a certificate that BASE-CHANGES -- exhibit 1 in the
       ideal over the base field, or a resultant nonzero in the base field --
       and the emptiness transports unchanged.  If no such certificate exists,
       the claim is a fact about Q(sqrt 17) only [...]
```

That finding is a real error that shipped in a public artifact. It took an
independent field-scope audit to find. Here it is a type error at the moment
the edge is drawn.

## What Grand Portage is for

Grand Portage is research middleware for the seams between exact-affine
computations. Use it to record models, typed changes of model, claims, checked
witnesses and certificates, and the precise scope in which an inference is
licensed. It is especially useful when several researchers or agents hand a
campaign back and forth.

It is not a general mathematical database and it is not the right home for
every CAS transcript, Betti table, or one-row-per-object census. Keep bulk
computation in ordinary content-addressed artifacts or Git; use GP for the
compact conclusions, provenance, and transport obligations that future work
must not misread.

For a local checkout:

```console
python -m pip install -e .
gp init --mcp
gp schema                 # read the declaration contract before writing
gp check                  # current actionable debt first
gp check --history        # include superseded generations
```

Version 0.30 retains v0.29's selected-embedding and bounded ordered-real
transport semantics while hardening the evidence layer. Solver-free verdicts
carry native provenance, `UNVERIFIED` attempts remain visible and retryable,
selected-real signs carry independently checked Sturm receipts, and NONEMPTY
claims may exhibit points in a bounded simple quadratic/cubic extension of Q.

## Status

All five layers are built and gated: <!--checks-->1789<!--/checks--> checks, live against Singular 4.2.1,
and it has had eleven live user sessions — see [docs/first-run/](docs/first-run/)
for the first, written up in full.

* **[COMPATIBILITY.md](COMPATIBILITY.md) — graph format 7, kernel epoch 11, selected-embedding identity, native/CAS provenance, extension witnesses, durable artifacts, and conservative migration**
* **[QUICKSTART.md](QUICKSTART.md) — install, a campaign in ten minutes, and the three things worth knowing on day one**
* **[v0.26 release packet](review/v0.26/README.md) — ARR15 open-locus soundness, bounded localization, and MCP custody**
* [DESIGN.md](DESIGN.md) — architecture and the decisions behind it
* [REVIEW.md](REVIEW.md) — **where I am least confident**, for a reviewer
* [Foundations and prior art](docs/FOUNDATIONS-PRIOR-ART.md) - bounded research questions and deliberate deferrals
* [Campaign projections and Three.js explorer](docs/VISUALIZATION.md) - read-only review artifacts and local visualization
* [Portage Command v0](docs/PORTAGE-COMMAND-V0.md) - digest-bound research packets, attempt ledger, and verification-debt overlay
* [Campaign dossier v0](docs/CAMPAIGN-DOSSIER-V0.md) - graded portraits, residual price cards, artifact replay inventory, and profile-based closeout readiness
* [Campaign release v0](docs/CAMPAIGN-RELEASE-V0.md) - transitive profile coverage, replay/licensing debt, and fail-closed content-addressed archives
* [Campaign publication v0](docs/CAMPAIGN-PUBLICATION-V0.md) - exact-scope portrait audit and manuscript-ready residual, replay, and blocker tables
* [JC campaign companion](https://github.com/wstrinz/grandportage-jc-campaign) - extracted signed-off campaign assays and publication fixtures
* `gp frontier INPUT.json` - exact-scope proof-state linking over immutable evidence envelopes
* `gp frontier-bundle MANIFEST.json` - fail-closed aggregation with explicit overlap resolution
* `gp campaign-packet MANIFEST.json` / `gp campaign-ledger MANIFEST.json` - provisional research operations with graph effect `NONE`
* `gp campaign-dossier INPUT.json --source-root CHECKOUT` - publication/gold blockers with source freshness and no graph authority
* `gp campaign-release RELEASE.json --source-root CHECKOUT [--output-dir NEW_DIR|--replay-kit-dir NEW_DIR]` - compile a release, materialize a publication-ready archive, or materialize replay closure independently
* `gp campaign-publication RELEASE.json [--document portrait-audit|manuscript-tables]` - generate author/reviewer closeout tables

Five further documents live in the private workspace only — `HANDOFF.md` and
`TESTPLAN.md` because they describe traps in blind trials not yet run, and
`SCOPE.md`, `KILL-CRITERIA.md` and `EXPERIMENT-B.md` because they name live
campaigns. This file used to *link* the first three, which is a broken link
for every reader here and exactly the kind of drift the check-count spans
exist to prevent.

What they contain, since the summaries name no domain:

* **`SCOPE.md`** — the boundary is a *semantic regime*, not a syntax class.
  This kernel is for exact affine algebra; ordered-field inequalities,
  optimisation, certified numerics and finite censuses are different regimes
  that have each been met in live work and recorded in affine vocabulary
  because that was the vocabulary available.
* **`KILL-CRITERIA.md`** — what would show this is not worth continuing,
  written before the answer is known, because friction is always
  reinterpretable as rigour.
* **`EXPERIMENT-B.md`** — hand-declared relation types measured against 57
  live edges: **88% accurate**, and the errors are mostly not about
  operations. That result is why the operation-constructor layer is three
  functions rather than sixteen.

| layer | module | what it does |
|---|---|---|
| kernel | `grandportage/kernel.py` | transport relations and claim-kind rules, subject to contextual checker gates |
| store | `grandportage/store.py` | append-only graph log; merge is concatenation |
| artifacts | `grandportage/artifacts.py` | immutable raw programs/transcripts addressed outside the semantic graph |
| checker | `grandportage/check.py` | findings, derived severities, exit code |
| projection | `grandportage/frontier.py`, `frontier_bundle.py`, `projection.py`, `visualization.py` | versioned proof frontier and bundle, campaign read model, and guided Three.js explorer |
| campaign operations | `grandportage/campaign.py` | provisional task packets, immutable attempt ledger, and maturity/debt overlay; derived only |
| campaign closeout | `grandportage/dossier.py` | graded portrait, leaf-price ledger, source freshness, and closeout profile evaluation; derived only |
| campaign release | `grandportage/release.py` | transitive archival coverage, self-contained replay resources, licensing debt, checksums, and safe full/replay-kit materialization; derived only |
| campaign publication | `grandportage/publication.py` | exact-scope dependency cards and manuscript-ready residual/replay/blocker tables; derived only |
| evidence manifest | `grandportage/evidence.py` | shared affine context, envelope, compilation targets, and graph-effect boundaries |
| discharge | `grandportage/discharge.py` | refusal → canonical next move |
| CAS + MCP | `grandportage/cas.py`, `mcp.py` | **declare the transport or no process spawns** |
| hook | `grandportage/hook.py` | runs the checker after each tool call and refuses |

Pointed at `d2_plane_72_108`'s live front — see
[the live front](#the-live-front) below.

## The loop, end to end

```
$ python -m grandportage.mcp          # registered by the portable root .mcp.json

  cas_ideal_is_unit(ring_vars=[...], generators=[...],
                    produces="RES_K", describes="the same support over K")
  -> ERROR: no transport declared. A computation that produces a new model
     must say how that model relates to its source.

  cas_ideal_is_unit(..., edge={"src": "RES_L", "type": "BASE_EXTENSION",
                               "why": "the coefficient field changes from
                                       Q(sqrt 17) to arbitrary char-0 K"})
  -> run: OK
     recorded: model RES_K, edge E-RES_K (BASE_EXTENSION from RES_L)

  portage_declare(events=[{claim: EMPTY, certificate: NONSQUARE_CLASS, ...},
                          {inference: "hence empty over every char-0 K"}])
  -> UNSOUND_PREMISE  TRANSPORT:INF-KILL
       refused: BASE_EXTENSION licenses EMPTY along the extension only at
                scope SCHEME; this claim has scope 'Q(sqrt 17)'
       -> DISCHARGE: produce a certificate that base-changes, or restate the
          claim at that scope and stop consuming it as geometric emptiness.
```

The hook then blocks the tool result rather than letting the refusal scroll
past: Codex receives an exit-0 structured `PostToolUse` block, while Claude
Code receives exit 2 and stderr. Codex project hooks must also be trusted and
enabled in `/hooks`. See [examples/](examples/) for the wiring.

## The six relaxation types

Inclusion-style edges point **tighter → looser**: `V(src) ⊆ V(dst)`.
`AGAINST` is reasoning looser → tighter, which is the direction emptiness
travels and the direction that closes cases.

A mapped `EQUIVALENCE` is the deliberate exception. It carries both
`forward` and `inverse` simultaneous substitutions and identifies the two
models through those maps; it does **not** also assert literal containment in
the coordinates as written. `forward` is the point map from source to target,
so polynomial pullback runs contravariantly. `gp verify` checks both ideal
pullbacks and both inverse compositions with the `ring_iso` verifier, while the
literal `containment` verifier skips that edge. Shared-coordinate maps retain
that point-map convention. When endpoint variable names differ, `forward` maps
every source generator to an expression in target variables and `inverse` maps
every target generator back; `{"x":"y"}` therefore verifies an ordinary
presentation rename. Polynomial maps are checked in both endpoint ideals;
rational cross-ring maps stop at an explicit localization-certificate boundary.
They fail closed until the verifier records `VERIFIED`. The exact field
names are `forward` and `inverse`; the plausible aliases `maps` and
`inverse_maps` are refused. Structured predicate conditions also compose through
these verified maps: `ALONG` rewrites with `inverse`, `AGAINST` with `forward`,
and a later section-certified elimination checks the rewritten condition in its
retained ring. A bare flag or stale verdict never supplies this typing authority.

`model.embedding` is optional and closed. `null` and omission both mean an
abstract, embedding-agnostic model. A REAL selection names one `ring_vars`
variable and an exact rational `{lo, hi}` isolating interval. A COMPLEX
selection names the variable, a rational rectangular box, and whether that box
is `EXACT` or only `STRUCTURAL_ONLY`; `conjugate_of` remains descriptive and
does not mint a map. An `IDENTITY_MAP` between two selected endpoints is legal
only when their serialized embedding payloads are identical. A nontrivial
`POLYNOMIAL` map such as `w -> -7-w` or `x -> -x` may still verify as a ring
isomorphism, but it moves the selected image and therefore cannot copy a free
`PREDICATE` unchanged. Identity claims continue to travel through the checked
substitution. When neither endpoint selects an embedding, historical transport
is unchanged.

A structured model-level `PREDICATE.condition` is also a direct verifier input,
not write-only syntax. `gp verify` certifies each `ZERO` atom by exact ideal
membership. It certifies `NONZERO` by proving the atom's vanishing locus empty
with a replayable unit-ideal identity; an atom already zero modulo the model
ideal is refuted. Failed sufficient tests remain visible as `UNVERIFIED`, and
an unchecked condition is reported by `gp check` as `UNTESTED-CONDITION`.

On a `REAL_CLOSURE` model over Q with one variable, one generator, and a
selected REAL interval, the same condition language accepts `POSITIVE`,
`NEGATIVE`, `NONNEGATIVE`, and `NONPOSITIVE`. Each is the sign of `expression`
at the selected root; write `a < b` as `NEGATIVE` on `a-b`. `gp verify` checks
the interval isolates exactly one root using exact Sturm arithmetic, refines it
with rational intervals until the sign separates, and records a deterministic
`selected_real_interval_v2` receipt containing the Sturm chain, variation
counts, refined interval, and zero/endpoint evidence. A separately authored
checker recomputes that arithmetic before the graph fold activates authority.
A malformed isolator or bounded miss is `UNVERIFIED`, never authority.
Incompatible sign assertions on the same
canonical polynomial and selected model create visible contradiction debt.

A `NONEMPTY` claim may pair `witness_point` with a closed
`simple_number_field_v1` certificate. The witness field is Q[a]/(f), separate
from the model coefficient field; v1 accepts only checked irreducible quadratic
or cubic f and only establishes points in `ALGEBRAIC_CLOSURE`. Coordinates are
polynomials or explicit numerator/denominator polynomials in a. Exact quotient
arithmetic checks every equation, open guard, and denominator inverse. BASE and
REAL_CLOSURE extension witnesses remain unsupported rather than silently
changing the model's ambient field or ordering.

Ordinary predicate pullback is also executable in the sound `AGAINST` direction:
a literal identity-coordinate edge preserves syntax only across matching exact
rings (and a mismatched exact RESTRICTION is rejected as ill-typed), and a currently checked `Eliminate` projection embeds retained-coordinate
syntax back into its source. Unspecified polynomial maps remain conservative.

Printed by the kernel itself with `gp table`, so a document quoting it and the
code applying it cannot drift apart.

| edge type | dir | EMPTY | NONEMPTY | PREDICATE | IDENTITY |
|---|---|---|---|---|---|
| `EQUIVALENCE` | ALONG | yes | yes | if selected embeddings are identical | if ring iso |
| `EQUIVALENCE` | AGAINST | yes | yes | if selected embeddings are identical | if ring iso |
| `NECESSARY_CONDITION` | **ALONG** | NO | yes | **NO** | if ambient |
| `NECESSARY_CONDITION` | AGAINST | yes | NO | yes | if denominator-free |
| `BASE_EXTENSION` | **ALONG** | **only with a certificate** | **yes** | NO | yes |
| `BASE_EXTENSION` | AGAINST | yes | NO | yes | if defined over base |
| `IMAGE_CLOSURE` | ALONG | NO | yes | if closed + closure, or retained condition + point lift | if exact contraction |
| `IMAGE_CLOSURE` | **AGAINST** | yes | **if existential** | yes | if denominator-free |
| `SPECIALIZATION` | ALONG | **NO** | **NO** | NO | if p-integral |
| `SPECIALIZATION` | AGAINST | **NO** | **NO** | NO | NO |
| `RESTRICTION` | **ALONG** | NO | yes | **NO** | yes |
| `RESTRICTION` | AGAINST | yes | NO | yes | **yes** |

Five of those cells were **wrong in this file** until a test started comparing
it against the kernel. Every conditional `IDENTITY` cell still showed the
pre-v0.2 rule — the licences that were found unsound and fixed, still
documented as sound in the file a reader meets first. The sentence above about
drift was true of `gp table` and false of this table, and nothing checked.

Three rows carry most of the value:

* **`BASE_EXTENSION` reverses the asymmetry.** Everywhere else emptiness
  travels freely and witnesses do not. Here a `k`-point *is* a `K`-point, so
  `NONEMPTY` travels along the arrow and `EMPTY` needs a certificate. Anyone
  who internalised "emptiness always transports" is primed to get this exactly
  backwards, which is how the erratum above happened.
* **Constructed elimination is one-sided by default; exactness and point lifts
  are separate certificates.** The local verifier proves every recorded target
  generator lies in the source contraction, `J ⊆ ι⁻¹(I)`. `gp
  verify-elimination` checks a global polynomial section; `gp
  verify-elimination-groebner` asks Singular for a bounded pure-lex proof and
  rechecks it with GP's small exact-polynomial checker. Either can earn the
  missing contraction inclusion. `gp verify-elimination-point-lift` instead
  checks finitely many principal-open rational lift charts plus an
  all-guards-zero fallback. Its localization/radical membership cofactors are
  exactly replayed and earn point-surjectivity without pretending to prove
  contraction exactness. Beginning in kernel epoch 8, a structured retained-coordinate
  `ZERO`/`NONZERO` condition can use that authority through verified coordinate
  rewrites, identity refinements, and elimination projections. The pure
  Groebner route remains coordinate-ring authority only.
* **Coefficient expansion is a checked compiler boundary.** `gp
  verify-coefficient-expansion --spec lowering.json` independently reconstructs
  a polynomial template after bounded-coordinate substitution and checks the
  recorded scalar rows. Selected coefficients are licensed only as necessary
  conditions; complete `0..degree` coverage earns the converse and rejects
  omitted overflow rows. The first JC cap assay proves why this is separate
  from scalar elimination: `dm2=1,d2=y` satisfies the scalar exact target but
  needs `dm4=-y/2`, so it cannot lift when `dm4` has cap zero.
* **Finite Laurent lowering is a separate checked compiler pass.** `gp
  verify-laurent-lowering --spec laurent.json` evaluates a closed, bounded
  straight-line program over finite Laurent expressions. Inputs have exact
  polynomial coefficients; nodes may add, multiply, scale, shift by a declared
  `y` exponent, or take the formal derivative. Every declared output equality
  is recomputed. This catches chart-sensitive errors before ordinary bounded
  coefficient expansion, including the rows 7--8 mistake of replacing
  `6*y^2*G` and `-3*y^2*G^2` by zero while `G` remains symbolic. The verdict
  licenses only those finite Laurent equalities: it does not establish the
  source template, chart change, antiderivative existence, guard invertibility,
  or any graph claim transport.
  A requested export succeeds only after an explicit `y` shift clears every
  negative exponent, and emits canonical `sparse_polynomial_v1` accepted
  directly by coefficient expansion. Equality and export are distinct licenses.
  `gp verify-laurent-coefficient-pipeline --spec pipeline.json` verifies both
  passes and requires every downstream source image to equal its named export
  as the same canonical JSON object; a separately self-consistent edited
  intermediate fails.
* **Factor-power receipts expose their semantic debt.** `gp
  verify-factor-power --spec factor.json` checks exact identities of the form
  `equation = scalar * base^k`, with `k > 0` and `scalar` a nonzero coefficient
  times a monomial in declared unit generators. It licenses only that
  polynomial identity. Concluding `base = 0` still requires the equation to
  vanish in the interpreted target, the target to have no zero divisors, and
  the coefficient and declared generators to remain units. The first live
  fixture independently replays the two landed JC p-axis square receipts while
  refusing axis emptiness and graph transport. The companion `gp
  verify-factor-power-contradiction` pass selects one factor receipt, verifies a
  monic affine solution for its base, and recomputes a second equation's exact
  declared-unit residual. It still grants no model binding or emptiness.
  The v0.19 JC adapter supplies that concrete binding without enlarging the
  authority vocabulary: it compiles the specialized contradiction to an
  ordinary localized cofactor certificate. The graph-bound verifier replays
  it and mints `EMPTY` only on the exact `c9_11` axis model; the parent edge
  remains refused.
* **Product splits stop before branch authority.** `gp verify-product-split`
  checks exact binary factorizations with declared-unit monomial scalars. The
  first fixture replays the landed JC `E[2,0]` split and its `-p` multiple
  `E[4,0]`. A successful check licenses the receipt identities only. The
  supported `gp construct product-split --src MODEL --spec RECEIPTS.json
  --receipt ID` path (or the underlying `operations.product_split` constructor)
  may mint two same-ring branch models only when a constant-unit receipt
  equation is literally a parent generator; `--declare` persists them through
  the ordinary closed graph schema. The existing partition verifier then
  independently checks their coverage. The variable-unit `E[4,0]` receipt
  cannot mint a cover until that verifier understands localization guards.
* **Affine product branches normalize through checked coordinate maps.** `gp
  construct affine-solve --src BRANCH --solve c8_0 --value=-p*c6_0
  --produces NORMAL` recognizes only a literal monic affine generator
  `c8_0-(-p*c6_0)`. It translates the pivot to zero, simultaneously rewrites
  every generator and open condition through the inverse map, and emits an
  `EQUIVALENCE` with explicit forward/inverse substitutions. The declaration
  carries `ring_iso: true`, but structured identity transport remains disabled
  until `gp verify` checks both ideal pullbacks and both map round trips. The
  first real Singular replay verifies the JC left-branch translation; the right
  branch has the symmetric `c9_0 -> -p*c7_0` form.
* **Localized coordinate identities now have a deliberately narrow checker.**
  `gp verify-localization-membership --spec localization.json` records
  principal-open guards, explicit denominator powers, and an exact guard-
  monomial/cofactor identity. It licenses only equality in that declared
  localization. It does not turn the open-locus `RESTRICTION` into a different
  coordinate ring, promote the equality to the ambient ideal, or grant point
  transport. This is the first bounded surface for unit-sensitive JC
  elimination pivots; arbitrary localized identities still gain no graph
  authority.
  Version 0.15 adds a second exact-polynomial wire form,
  `sparse_polynomial_v1`, for certificates too large to survive the bounded
  infix AST. It is not a larger parser budget: coefficients, term count,
  variable-power entries, exponents, ring-variable order, and descending
  monomial order are all checked before arithmetic. Small legacy strings remain
  readable and normalize as before. Localization and coefficient-expansion
  replay retain sparse values end to end. In the first live JC application, GP
  independently verified all twelve 163--2,011-term q-window pivots under the
  frozen q-chart digest, granting one localized identity per pivot and no
  whole-chain, ambient, source-membership, or H3 authority.
  The rows 7--8 live packet also supplies two unit-ideal controls: after
  localizing at `q,t`, the row-8 coefficient `-5*q^3*t^2` kills the q bare
  family; after localizing at `p,t`, `5*p^4*t^2` kills the p bare family. The
  exact checker verifies both as localized `1=0` identities, and Lean proves
  such an identity admits no localized point. Version 0.16 implements the
  distinct `LOCALIZED_UNIT_IDEAL_CERT`: `gp verify` may now promote this exact
  proof to persisted `EMPTY` on the recorded open model. The proof is replayed
  and fingerprint-bound; bounded search failure stays `UNVERIFIED`, and the
  existing RESTRICTION law refuses to move the emptiness to the parent.
  The first full composition is retained under `review/v0.19/`: native and
  frozen source digests, specialized receipt, compiled localized certificate,
  real Singular artifacts, folded graph, projection, and explorer. Nothing in
  it licenses the full p chart, actual-source membership, infinite lift, or H3.
* **Evidence contracts have one descriptive source.** `gp evidence` (or
  `gp evidence --json`) lists every standalone affine evidence schema, its
  maturity and compilation target, plus the exact graph effect and containment
  of current authority verifiers. This shared envelope reduces context drift;
  it is deliberately not a dynamic theorem-plugin system.
  The JC `b=0` free-plane assay is a deliberately campaign-local example:
  `exceptional_factor_column_v1` freezes a complete finite coefficient ledger,
  independently checks its `b`/`Delta` factorizations and one reversible affine
  pivot, and retains graph effect `NONE`. It distinguishes a solved rung value
  from a new compatibility equation without adding a graph relation or claim.
  Its depth-eight successor uses `affine_fiber_block_v1`: an exact coefficient
  block may determine named fiber coordinates and expose a residual
  compatibility, but it still grants no graph authority until the residual and
  exact necessary-condition model are materialized and bound.
* **Ordered localized solves now have a bounded composition envelope.** `gp
  verify-localized-triangular-chain --spec chain.json` checks a closed sequence
  of exact equations `unit * (pivot - solution)`, requires the unit to use only
  declared guards, recomputes every ordered post-substitution generator list,
  and binds every step to input/output state fingerprints. The first fixture
  preserves the landed five-step JC source top-face order and expressions. Its
  standalone verdict is intentionally translation validation only. The isolated
  authority adapter compiles each checked chain into a mapped equivalence plus
  `mapped_ring_iso_v1`: explicit cofactors for both ideal pullbacks and exact
  forward/inverse maps. The checker expands this proof without Gröbner search;
  the legacy Singular route remains an independent top-face differential. The
  top face adjoins an inverse coordinate for `t`. On the second face,
  `15*t^3+1=0` supplies the checked polynomial inverse `-15*t^2`, so no redundant
  coordinate is added. Both recorded `review/v0.20/` campaigns earn identity
  transport only between their exact quotient rings; source extraction, parent
  coverage, and H3 remain outside. A mutated cofactor is refused as unverified,
  and removing the top-face inverse equation fails the solver crosscheck.
* **`IMAGE_CLOSURE` AGAINST / `NONEMPTY` is Chevalley.** A point of the Zariski
  closure need not lift. This is why elimination is a sound way to *derive*
  equations and an unsound source of *witnesses* — and why a cell that survives
  everything is an artifact candidate rather than a reason to buy solver time.
  The cell is conditional because `NONEMPTY` has two readings and they diverge
  here alone: a claim that **holds a point** is refused, and one that only
  proves a point **exists** may cross, since the closure of the empty set is
  empty. The register carried that gap for four versions with the repair
  written out, and a campaign finally recorded an existence proof with no
  witness.
* **`SPECIALIZATION` carries nothing.** char 0 → char p transports no existence
  statement in either direction, and that is a theorem, not caution: Fano is
  empty over `Q` and nonempty over `F₂`, non-Fano is the reverse.
* **`RESTRICTION` is `NECESSARY_CONDITION` on points and something else on
  functions.** The six point-cells are *identical*, because both follow from
  `V(src) ⊆ V(dst)` and nothing more — so typing a semialgebraic cut
  `NECESSARY_CONDITION` licenses nothing false, which is exactly what makes it
  the attractor. What it costs is the distinction between a result that holds
  **generically** and one that holds **everywhere** — which, wherever the
  exceptional locus is reachable by real data, is the only distinction that
  matters. The `IDENTITY` row is where
  the mathematics genuinely differs: a restriction adds no equations, so the
  obstruction that stops a derived identity crossing a `NECESSARY_CONDITION`
  is simply absent — both ends share a ring and an ideal, and an `IDENTITY`
  is the same statement at each. That cell was gated on a declared
  `zariski_dense` until an external review broke the condition with the nodal
  cubic `y² = x²(x−1)`, whose real points *are* Zariski-dense and whose
  restricted region is an isolated point. The gate was also answering the
  wrong question: "vanishes at every point of the region" is a `PREDICATE`,
  and that cell refuses. What replaced it is `gp verify`, which decides
  `lhs − rhs ∈ I` by reduction instead of asking anyone to declare it.

## Scope is derived, never declared

Epoch-12 transport instantiates certificate reach at the target field and point
universe through [field.py](grandportage/field.py). Reach summarizes an
interpreter's requirements; it is not the domain on which a bare polynomial
identity holds. A unit-ideal interpretation needs nontriviality; an SOS
contradiction additionally needs an ordered interpretation. Equality may replay
where the contradiction interpretation fails. Evidence, binding and context
gates still apply after reach admission.

`SCHEME` survives as compatibility vocabulary. The legacy Boolean stability
registry is not the current transport rule. See the [atlas mapping](docs/ATLAS-MAPPING-V0.md)
and [requirement profiles](https://github.com/wstrinz/grandportage/blob/d81eb12/docs/REQUIREMENT-PROFILES-V0.md).

Latest historical correction (v0.36 atlas finding): this paragraph previously
explained current transport through Boolean certificate stability. The table
printer was corrected in v0.35; this prose now names reach and interpreter
requirements. Earlier historical confessions remain in this document.

## Predicate policy for new campaign charters

New campaign charters, Cloquet onward, require a machine-readable `condition`
formula for every PREDICATE claim. Prose PREDICATE claims remain legal and retain
existing behavior; they are transport-inert beyond claim kind. No formula is
inferred and graph construction does not refuse prose. `gp lint` lists these
claims as warnings without changing graph authority.

## Quick start

```bash
gp init                          # create .portage/graph.jsonl
portage_declare --file events.json # literal transactional write fallback
gp check                         # type-check; exit 1 if anything is unsound
gp check --json                  # machine-readable findings
gp table                         # print the transport table and certificates
gp show                          # print the graph
gp artifacts check               # audit exact raw CAS executions
gp project --output campaign.json  # complete, derived read model
gp visualize --output campaign.html # read-only Three.js explorer
gp frontier frontier-input.json    # scoped premise updates and open research boundary
gp frontier-bundle fixtures/frontier/current_v1.json  # current cross-consumer boundary
gp campaign-packet fixtures/campaign/matroid/packets.json --format human
gp campaign-ledger fixtures/campaign/matroid/ledger.json --overlay
python scripts/public_snapshot.py  # audit the public/private release boundary

gp --graph fixtures/jc2/graph.jsonl check      # the JC(2) retrodiction
gp --graph fixtures/matroid/graph.jsonl check  # the matroid retrodiction
```

The core checker and JSON projection are pure stdlib: no solver, network, or
model in the loop, and under a second. The generated explorer imports a pinned
Three.js build by default; `--three-root` can point it at a local package.

## The retrodiction gate

```bash
python -m pytest        # <!--checks-->1789<!--/checks--> checks
```

Grand Portage's credibility rests on reproducing, from **data**, what two
hardcoded prototypes produced with their DAGs compiled into the checker:

| domain | flags | positive controls | ground truth |
|---|---:|---:|---|
| JC(2) plane (72,108) | 4 + taint + 2 coverage axes | 9 | three errors that **actually shipped** |
| matroid realizability | 6 | 6 | externally published (Oxley, MacLane, Brandt–Wiebe) |

Both answer keys were pinned before this code existed. Zero false positives in
either domain. Severities are **derived** from contradictions in the graph
rather than assigned by hand, and reproduce the prototypes' hand grading on
9 of 10 findings; the tenth is a declared override carrying its reason.

Twenty-odd mutations assert the gate has teeth — each perturbs one declared
attribute and requires the verdict to move. Some produce a *refused fold*
rather than a different verdict, which is stronger: the graph cannot state the
mutated claim at all.

### Coverage on two axes

`MODELLING_GAPS.md` §3.4 is blunt that the three documented gauge leaks are
**one incident with three witnesses**, so a rule tested only on them proves
very little. The JC(2) fixture now runs a second axis:

| axis | model | declared | gap |
|---|---|---|---|
| `place` | `WINDOW` | `y`, `∞` | **`t`** |
| `order` | `GSYS` | the four consumed Q-slices `M=-1,-2,-3,-5` | **`M=-4`** and **`M=0..12`** |

`M=-4` is the λ row at u-weight 192 — the missing interior rung of the ladder
`156,168,180,[192],204` that `full_system_bridge.G_generators()` asserts. It is
*ambiguous* evidence by `MODELLING_GAPS`'s own reckoning, since `G4_stripped`
has divisor `4(0)+28(−1)` and so has a place story too.

`M=0..12` is the clean one: the pipeline consumes only the `M < 0` slices, and
a truncation by sign of the slice index has no place content at all. Deleting
`place` loses the `t` gap, deleting `order` loses the half-line, and neither
axis recovers the other's item — so both are necessary.

What this does **not** establish is discrimination *within* an axis. That needs
more than one incident per axis, and the source repo does not contain one.

## The live front

`fixtures/gamma_window/` is not a retrodiction. It models the γ-window compiler
work targeting (75,125), which is open right now, so there is no answer key and
none is claimed. Four obligations, all currently standing:

| finding | what it is |
|---|---|
| `GI-GAMMA-IMPORT` | GGV3 §5 asserts γ ∈ {2,3} *without proof*; the corner layer derives only γ ∈ {2,3,4}. A `PREDICATE` moved ALONG a `NECESSARY_CONDITION` edge. |
| `GI-REPLAY-TRANSFER` | the (50,75) certificate is a *replay* of published algebra with `a³=2` supplied as a given. Nothing relates it to (75,125). |
| `GI-BRIDGE` | `a2_certificate()` and `tower_step()` share **not one variable**; the sentence joining them is a `print` statement. |
| `GI-WINDOW-CONFLATION` | two different objects wear the word "window" — a cone that degenerates to a ray, and a depth ledger. |

**Grand Portage discovered none of these.** All four are already written down,
in `SESSION_HANDOFF.md`'s prose and `F2_TOWER.md`'s banner. What changes is the
form: a banner is prose a reader has to find and believe, and it is the first
thing lost at a compaction. A typed edge blocks the conclusion that depends on
it and names its own discharge.

Two things the run showed that the prose does not:

* **`GI-BRIDGE` is the clearest case for the whole approach.** Neither
  computation is wrong; both are individually well-evidenced. The defect is a
  *join* between two computations that share no variable. No evidence ladder
  catches that, because grading either half tells you nothing about the seam.
* **Naming the type is not enough — the direction is a claim.** Typing the
  bridge `NECESSARY_CONDITION` as drawn does *not* discharge it, because a
  `PREDICATE` still cannot travel ALONG. Discharging it requires asserting that
  the kill layer *refines* the period layer, and being accountable for that.
  Which is precisely the assertion the `print` statement skipped.

## What this does not do

### Explicit open-premise slots

An argument can record the claim it still needs without asserting that claim.
A premise slot uses `required_kind`, `at`, and `missing_why` instead of a
claim id. It retains the intended conclusion while full checks refuse the
inference and provide a discharge. Accounting-only checks also report the
open slot, without certifying any field transport. A family claim cannot be
substituted directly for a model premise: retain its counting obligations
and establish the explicit bridge, or leave this slot open.

The frozen `tests/fixtures/dk_retrodiction/transports/X8-X10.json` demonstrates
both missing-premise refusals and a clean control. The accompanying
`transports/verbatim-v0.31.2.md` preserves the source campaign's original
outputs, including its naming and failed repair attempts; it is historical
evidence, not a revised answer key.

### Limits

Stated plainly, because the failure mode of a tool like this is that four
tracked hazards start feeling like a guarantee.

* **It does not find missing equations.** It routes attention to the place or
  the step where one is missing. Every actual advance in the source campaign
  was an equation; the claim here is only that a typed graph shortens the
  search for *which* one.
* **It requires the edge to exist.** If a step is taken without any model
  declaring that a field changed or a chart changed, there is nothing to type.
* **Coverage detects absent structure, never weak structure.** A declared
  component that is merely too weak is invisible, and that is a limitation of
  the whole coverage tradition, not a bug here.
* **The cost is modelling, not typing.** Measured on the second domain: ~95% of
  the effort was deciding what the models *are*; ~5% was assigning types. Any
  plan that treats this as tooling rather than as a discipline will spend its
  money in the wrong place.

## Provenance

Grand Portage is the successor to `whetstone/` in the `math-stuff` repo, where
the same discipline exists as three single-file prototypes with their domains
hardcoded. The design, the transport table, the certificate registry and both
fixtures come from there. The generalization — graph as data, derived
severities, path continuity, probes, merge semantics — is what is new.

The name is the 8.5-mile haul around the Pigeon River falls: the deliberate,
effortful carry between two bodies of water, where you are acutely aware of
what you can bring.

For the distinction from semantic information loss, see the
[observation-axis note](https://github.com/wstrinz/grandportage/blob/d81eb12/docs/OBSERVATION-AXIS-V0.md).
