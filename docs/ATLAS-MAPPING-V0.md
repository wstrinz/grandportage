# GP preservation atlas, v0

Audited against v0.34.0 (`c89d055`), graph format 8, kernel epoch 12.
This is a correspondence audit, not an additional source of transport authority.

## Findings

The packet captures a useful program: relate preservation rules, their semantic
premises, and the evidence that earns those premises. GP already compiles its
point table from relation capabilities. The valuable next step is to account for
the gates around that table, not to replace it with a newly discovered calculus.

No false kernel licence was reproduced in this audit. A real explanatory defect
was reproduced and fixed: `gp table` described certificate transport using the
legacy Boolean scope registry rather than epoch-12 reach. It now distinguishes
policy ceilings from verifier-earned authority.

The new Lean module proves bounded reach interpretation, relational transfer,
witness mapping, ordered certificate interpretation, and a preservation polarity.
An executable comparison checks 139 Python/Lean reach and extension decisions.
These results do not verify the Python implementation end to end, instantiate a
general field library, or establish the algebraic premises of every transport gate.

Three corrections sharpen the broader program. Every binary relation gives the
powerset adjunction, including a partial specialization relation. Mathematical
existence and custody of a particular witness have different requirements.
Certificate equality and the interpretation making it a contradiction also have
different requirements. Absence of authority is neither mathematical falsity nor
a counterexample.

External correspondence is substantial, but not evidence of novelty. Isabelle,
Trocq, and partial Galois transport already overlap. In particular, Trocq's
constraint minimization must not be confused with a proved global minimality
theorem. The promising GP contribution is an explicit account of interpretation,
checked evidence, binding, and composition across a bounded collection of domains.

## Reading and status discipline

`MATCHES` means the stated semantic inference has a correspondence under the
explicit dictionary below. `MATCHES-WITH-GAP` means additional GP-specific
interpretation or evidence premises remain. `UNMAPPED` means no precise external
assignment is established here. `CONTRADICTS` requires the *same premises* and
incompatible conclusions; no current kernel cell earned that status.

These are comparison statuses. They are separate from whether a runtime cell is
licensed, conditional, or conservatively refused. A refusal need not mean that
the inference is mathematically false. In particular, stronger premises can
justify inferences beyond the baseline capability profile.

The sources consulted are listed below with the precise portions used. This is
a targeted primary-source audit, not a claim to have exhaustively read every
work named in the packet. The Isabelle source supplies exact theorem statements;
the Trocq journal manuscript supplies the newer hierarchy and its limitations.
Older categorical and model-theoretic references remain orientation where an
exact GP instantiation has not been constructed.

## Dictionaries

Let `S : A → Prop` and `T : B → Prop` describe solution sets. Keep these predicates
explicit: an empty solution set is possible even when the ambient HOL type is
inhabited. Let `R : A → B → Prop` relate admissible solutions.

- `L`: every source solution relates to some target solution (left total on S,T).
- `R`: every target solution relates to some source solution (right total on S,T).
- `E+`: L transports NONEMPTY along; `E−`: R transports NONEMPTY against.
- `A+`: R transports universal assertions along, given the corresponding
  implication on related points; `A−`: L does the reverse with the reverse
  predicate implication. EMPTY is the constant-false universal assertion.
- `Adj`: `ExistsImage R P ≤ Q ↔ P ≤ ForallPre R Q`, with no totality premise.
  This is already proved in `RelationalTransport.lean`.

### Isabelle Transfer and Lifting

The bounded form of `right_total_alt_def2` gives A+; reverse the relation for A−.
Existential transfer gives E+ and E−. Predicate correspondence is an independent
premise. `bi_unique` is needed for the equality relator, not for these elementary
existential/universal implications. GP coordinate-ring equality is a further
interpretation, not merely equality of point representations. `Quotient` in
Lifting supplies additional representation data and is not an automatic synonym
for an arbitrary GP edge. [I, IL]

### Trocq

Definition 5.7 assigns structures to a relation and its converse. A chosen map
whose graph lies in the relation supplies `M2a`; `M2b` supplies a map agreeing
with related values; `M3` combines them, and `M4` adds coherence. Propositional
totality alone does not supply a chosen map constructively. Thus L supports
`(2a,0)` only with witness-producing data, and R supports `(0,2a)` similarly.
A witnessed isomorphism can supply stronger structure. Edge names alone do not.
Related operations and predicates still need to be registered. Figure 7's
sufficient constraints have conjectured minimality (§6.1); §7.3 minimizes within
the supplied constraints. These are different guarantees. [T]

### Abstract interpretation and partial Galois transport

Adj is a correspondence for powersets ordered by inclusion. An abstract
interpreter additionally needs a concrete/abstract interpretation and sound
transformers; the existence of this adjunction does not make the GP engine an
abstract interpreter or prove optimality. This is the connection used here to
the Cousots' framework. [AI]

Kappelmann's partial Galois connections and equivalences are directly relevant
prior art joining order, dependent relations, and proof transport in Isabelle.
They should be compared before claiming a new bridge between these subjects.
No equivalence between that full framework and GP is established here. [PG]

### Model theory and algebra

For an actual embedding of structures and a specified language, preservation of
existential formulas upwards and universal formulas downwards helps explain the
variance. A GP `PREDICATE` label does not establish that language or an embedding.
The full Łoś–Tarski characterization is a separate theorem, not needed to prove
the finite table. General ACF/RCF transfer, characteristic transfer, and
quantifier elimination remain UNMAPPED to executable GP rules in this audit. [MT]

For IDENTITY use expressions in a coordinate ring and membership of their
difference in its defining ideal. Pullback is contravariant. Field extension is
faithfully flat, but descending a statement also requires that it be expressed
over the smaller field. Equality in a ring cannot be recovered from its ordinary
field-valued points when nilpotents are present. Dual-number observations explain
the missing information; the new Lean example proves the elementary square-zero
obstruction, not a general representability theorem. [FF, DN]

## Complete point inventory: 42 cells

`+` means ALONG, `−` AGAINST. Rule spelling is literal runtime table spelling.
M = MATCHES; G = MATCHES-WITH-GAP; U = UNMAPPED. E/A codes refer to the dictionary
and therefore [I]; every row has Adj as a semantic construction, but Adj alone
does not license that row. Trocq assignments are conditional as explained above.
All licensed cells are still subject to the context and authority gates below.

| Edge | Direction | Kind | Runtime rule | Status | Correspondence or obstruction |
|---|---|---|---|---|---|
| EQUIVALENCE | ALONG | EMPTY | True | M | A+ with false predicate, R |
| EQUIVALENCE | ALONG | NONEMPTY | True | M | E+, L |
| EQUIVALENCE | ALONG | PREDICATE | selected_embedding_identity | G | A+ plus preservation of selected structure |
| EQUIVALENCE | AGAINST | EMPTY | True | M | A− with false predicate, L |
| EQUIVALENCE | AGAINST | NONEMPTY | True | M | E−, R |
| EQUIVALENCE | AGAINST | PREDICATE | selected_embedding_identity | G | A− plus preservation of selected structure |
| NECESSARY_CONDITION | ALONG | EMPTY | False | M | L alone insufficient: empty subset of inhabited set |
| NECESSARY_CONDITION | ALONG | NONEMPTY | True | M | E+, L |
| NECESSARY_CONDITION | ALONG | PREDICATE | False | M | Assertion on subset need not hold outside it |
| NECESSARY_CONDITION | AGAINST | EMPTY | True | M | A−, L |
| NECESSARY_CONDITION | AGAINST | NONEMPTY | False | M | Inhabited superset need not give inhabited subset |
| NECESSARY_CONDITION | AGAINST | PREDICATE | True | M | A−, L and predicate correspondence |
| RESTRICTION | ALONG | EMPTY | False | M | Empty restricted region, inhabited ambient region |
| RESTRICTION | ALONG | NONEMPTY | True | M | E+, inclusion |
| RESTRICTION | ALONG | PREDICATE | False | M | Positivity on region does not extend universally |
| RESTRICTION | AGAINST | EMPTY | True | M | A−, inclusion |
| RESTRICTION | AGAINST | NONEMPTY | False | M | Ambient witness need not satisfy restriction |
| RESTRICTION | AGAINST | PREDICATE | True | M | A−, inclusion |
| BASE_EXTENSION | ALONG | EMPTY | scheme_scope | G | Certificate interpretation; Q-empty x²=2 gains real roots |
| BASE_EXTENSION | ALONG | NONEMPTY | True | G | E+ through actual field embedding and point interpretation |
| BASE_EXTENSION | ALONG | PREDICATE | False | M | Larger field can introduce points violating assertion |
| BASE_EXTENSION | AGAINST | EMPTY | True | G | A− semantically; checked reach can still refuse target |
| BASE_EXTENSION | AGAINST | NONEMPTY | False | M | Real root of x²=2 need not be rational |
| BASE_EXTENSION | AGAINST | PREDICATE | True | G | A− through field embedding and corresponding predicate |
| IMAGE_CLOSURE | ALONG | EMPTY | False | G | Conservative baseline: actual cl(empty)=empty is stronger |
| IMAGE_CLOSURE | ALONG | NONEMPTY | True | G | E+ given actual image-to-closure interpretation |
| IMAGE_CLOSURE | ALONG | PREDICATE | closed_exact_image | G | Geometric closure + closed assertion OR checked point surjectivity + target expressibility |
| IMAGE_CLOSURE | AGAINST | EMPTY | True | G | A− given actual image-to-closure interpretation |
| IMAGE_CLOSURE | AGAINST | NONEMPTY | existential | G | Nonempty closure implies existence; does not lift specified point |
| IMAGE_CLOSURE | AGAINST | PREDICATE | True | G | A− given predicate correspondence |
| SPECIALIZATION | ALONG | EMPTY | False | M | (p)=0 has empty generic fibre and inhabited special fibre |
| SPECIALIZATION | ALONG | NONEMPTY | False | M | px=1 has generic point, no point modulo p |
| SPECIALIZATION | ALONG | PREDICATE | False | M | px=0 forces x=0 generically, not modulo p |
| SPECIALIZATION | AGAINST | EMPTY | False | M | px=1 has empty special fibre, inhabited generic fibre |
| SPECIALIZATION | AGAINST | NONEMPTY | False | M | (p)=0 has inhabited special fibre, empty generic fibre |
| SPECIALIZATION | AGAINST | PREDICATE | False | M | On px=1 every predicate is vacuous modulo p |
| UNTYPED | ALONG | EMPTY | False | U | No semantic relation class admitted |
| UNTYPED | ALONG | NONEMPTY | False | U | No semantic relation class admitted |
| UNTYPED | ALONG | PREDICATE | False | U | No semantic relation class admitted |
| UNTYPED | AGAINST | EMPTY | False | U | No semantic relation class admitted |
| UNTYPED | AGAINST | NONEMPTY | False | U | No semantic relation class admitted |
| UNTYPED | AGAINST | PREDICATE | False | U | No semantic relation class admitted |

The specialization examples compare fibres of an integral presentation. There
is no field homomorphism Q → F_p. Trocq's integer-to-modular-integer examples
must not be assigned directly to GP's field specialization by that analogy.

The IMAGE_CLOSURE/ALONG/EMPTY refusal is an explicit completeness opportunity,
not a soundness defect. A future rule would need earned geometric closure
authority, the right point universe, and checked emptiness interpretation.
Exact ideal contraction alone is a different premise. No licence was added.

## Complete coordinate-ring inventory: 14 cells

These are algebraic correspondences under the stated interpretation. None is
declared to be inexpressible in Isabelle or dependent type theory. G records
the gap between the algebraic argument and GP's concrete evidence binding.

| Edge | Direction | Kind | Runtime rule | Status | Additional premise / obstruction |
|---|---|---|---|---|---|
| EQUIVALENCE | ALONG | IDENTITY | ring_isomorphism | G | Ring isomorphism, not point bijection; nilpotents distinguish |
| EQUIVALENCE | AGAINST | IDENTITY | ring_isomorphism | G | Inverse ring interpretation, not point bijection |
| NECESSARY_CONDITION | ALONG | IDENTITY | ambient_identity | G | AMBIENT origin and denominator-free substitution |
| NECESSARY_CONDITION | AGAINST | IDENTITY | map_polynomial | G | Pullback of ideal relation under denominator-free map |
| RESTRICTION | ALONG | IDENTITY | True | G | Same coordinates and defining ideal; restriction changes points |
| RESTRICTION | AGAINST | IDENTITY | True | G | Same coordinate-ring identity, no substitution |
| BASE_EXTENSION | ALONG | IDENTITY | True | G | Scalar extension carries ideal membership |
| BASE_EXTENSION | AGAINST | IDENTITY | coefficients_in_base | G | Statement downstairs plus faithful flatness [FF] |
| IMAGE_CLOSURE | ALONG | IDENTITY | exact_image_identity | G | Exact ideal contraction AND target expressibility |
| IMAGE_CLOSURE | AGAINST | IDENTITY | map_polynomial | G | Pullback; denominator-free substitution |
| SPECIALIZATION | ALONG | IDENTITY | integral_identity | G | AMBIENT, p-integral coefficients, denominator-free map |
| SPECIALIZATION | AGAINST | IDENTITY | False | M | Equality mod p need not hold generically: p=0 |
| UNTYPED | ALONG | IDENTITY | False | U | No coordinate-ring map admitted |
| UNTYPED | AGAINST | IDENTITY | False | U | No coordinate-ring map admitted |

For specialization, integrality of the displayed identity does not prove an
integral derivation: x=0 follows from px=0 over Q but fails modulo p. For image
closure, vanishing on points is weaker than ideal membership unless extra
radicality premises are supplied. GP's exact-contraction route avoids that gap.

## Context, interpretation, and evidence gates

The inventory is `kernel.TRANSPORT`, not a promise that `audit_inference` admits
every True entry. `check.py` binds evidence, checks expressibility, and applies
epoch-12 field context. A complete implementation correspondence must include it.

| Mechanism | Mathematical obligation | Runtime / proof boundary |
|---|---|---|
| Point context | Comparable concrete fields, same point interpretation and selected structure | `compatible_point_context`; missing one endpoint's context refuses |
| Reach instantiation | Target belongs to a class justified by the certificate | `instantiate`; new Lean `instantiate_sound` for canonical vocabulary |
| NONE | No earned transport authority | No claim that the mathematical conclusion is false |
| FIELD_SPECIFIC | Conservative authority at one concrete field | Neither extension closure nor disproof elsewhere |
| ORDERED | Ordered interpretation of squares and negative one | Refuses C and algebraic-closure point universe |
| CHAR_0 | Certificate valid in the justified characteristic-zero interpretation | A policy ceiling is insufficient; exact F_p replay earns FIELD_SPECIFIC |
| Evidence custody | Current verified result belongs to this claim/context | Receipt, endpoint and payload binding remain Python obligations |
| Selected embedding | Copied predicate means the same thing | Abstract field/ring isomorphism alone insufficient |
| Witness lift | Supplied target point has a checked preimage | Existential nonemptiness is strictly weaker |

The two branches of `closed_exact_image` are materially different. Checked
point-surjectivity with structured target expressibility permits nonclosed
predicates by A+. Otherwise a closed predicate needs independent geometric
closure authority. Exact contraction alone does not discharge that point-level
premise. For `exact_image_identity`, denominator-free substitution is also
required, and expressibility is enforced outside the table. These alternatives
must survive any future attempt to infer “minimum requirements.”

The entirely legacy context path (neither endpoint has `about`) is retained.
`scheme_scope` is a historical rule name: the high-level checker consults earned
reach and target context. The registry's Boolean certificate stability table is
explicitly marked a legacy scope shadow; its name-parity tests do not verify
epoch-12 reach. The new 139-row comparison is a separate, bounded gate.

For ordered SOS, `-1 = x² - (x²+1)` is an identity over C as well as R. It proves
emptiness of x²+1=0 only in an interpretation where squares are nonnegative and
-1 is not. Substituting x=i exposes the boundary. `orderedSOS_contradiction`
proves the interpretation step from explicit arithmetic laws and zero cofactor
terms; it does not verify the parser, polynomial evaluation, or those laws for
an independently formalized real field. `replayed_equality_survives` is merely
congruence of equality under a function, not a claim that arbitrary functions
preserve polynomial operations.

## Multi-premise forms

| Form | Logical correspondence | Status and remaining GP premises |
|---|---|---|
| Exhaustive partition, EMPTY | Every parent point enters a branch; every branch empty | G: checked coverage, all branches, bound claims |
| Exhaustive partition, PREDICATE | Same cover plus assertion on every branch | G: common predicate interpretation and coverage |
| Partition, NONEMPTY / IDENTITY | No generic supported partition rule | U: a different rule would need separate semantics |
| Join of premises | Conjunction introduction at a common interpretation | G: every route licensed, premises co-located, allowed conclusion kind; substantive implication remains an obligation |
| Family-to-member | Bounded universal elimination | G: exact enumeration, BOTH strength, COUNT coverage, proved group, listed member and model binding |
| Reindexing a family | `(∀ i, P i) → ∀ j, P(f j)` | M: new Lean `reindex_forall`; no enumeration authenticity proved |

Calling family elimination Beck–Chevalley would require a specified square and
a proved commutation law. The present bridge needs only universal elimination;
that larger categorical assignment remains UNMAPPED.

## Proof and parity boundaries

The subsequent [certificate-interpreter slice](CERTIFICATE-INTERPRETER-V0.md)
moves one boundary forward: an explicit integer-expression derivation is
evaluated in Lean and yields ordered contradiction, with a concrete integer
instance. The statements below about `Atlas.lean` describe that original module;
they do not erase the newer proof. The Python parser and full rational
normalization remain outside both formal proofs.

`lean/GrandPortage/Atlas.lean` adds bounded transfer, data-level witness mapping,
restriction of stability, three-way knowledge, canonical reach interpretation,
ordered SOS interpretation, family elimination, an antitone preservation
correspondence, and the elementary nilpotent observation example. Existing
`RelationalTransport.lean` supplies Adj and composition. No `sorry` is used.

`scripts/check_atlas_parity.py` compares 90 reach instantiations and 49 concrete
extensions with `lean/AtlasParity.lean`: Q, R, C, F_2, F_3, F_5, F_7, plus the two
universal target classes. This covers every branch shape of the canonical
decision functions, not every prime or malformed payload. It is not a proof of
Python/Lean equivalence. Parser validation, primality, authority freshness,
point-universe gates, and full graph composition are outside this comparison.

## Primary sources

- **[I]** Isabelle/HOL [Transfer theory](https://isabelle.in.tum.de/library/HOL/HOL/Transfer.html):
  totality, uniqueness, `right_total_alt_def2`, quantifier transfer, equality.
- **[IL]** Isabelle/HOL [Lifting theory](https://isabelle.in.tum.de/library/HOL/HOL/Lifting.html): Quotient interface.
- **[T]** Cohen, Crance, Mahboubi, *Trocq: Proof Transfer for Free, Beyond
  Equivalence and Univalence*, TOPLAS, [author manuscript](https://inria.hal.science/hal-05192017/file/main.pdf),
  Definitions 5.7–5.8, Remark 5.10, Figure 7 and §6.1, Theorem 6.7, §7.3, §8–10;
  [published DOI](https://doi.org/10.1145/3737283).
- **[AI]** Cousot and Cousot, [POPL 1979 author page and section summary](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL79.shtml),
  especially §5 and §7. The downloaded original is scanned; no full-text audit
  of that paper is claimed here.
- **[PG]** Kappelmann, [Transport via Partial Galois Connections and Equivalences](https://arxiv.org/abs/2303.05244),
  APLAS 2023 with extended arXiv version; [accompanying AFP formalization](https://www.isa-afp.org/entries/Transport.html).
- **[MT]** Speirs, [Model Theory notes](https://speirs.sites.ku.dk/files/2017/10/ModelTheoryNotes.pdf),
  §5.1 preservation; orientation, not a completed GP model-theoretic instantiation.
- **[FF]** Stacks Project, [Flat modules](https://stacks.math.columbia.edu/tag/00H9)
  and [Faithfully flat descent](https://stacks.math.columbia.edu/tag/03O6).
- **[DN]** Stacks Project, [Tangent spaces](https://stacks.math.columbia.edu/tag/0B28): dual-number points.
