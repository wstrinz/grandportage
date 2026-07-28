# REVIEW.md — what to attack, and where I am least confident

A brief for an independent reviewer. Deliberately not a tour: the parts that
work are visible from the tests. What follows is where the risk actually is,
ordered by how much damage a mistake would do.

**v0.4, seven days old, four live user sessions, <!--checks-->717<!--/checks--> checks.** One external
adversarial review has happened and found eight defects; §7 is what it taught.
Treat everything here as provisional.

---

## The claim, stated so it can be falsified

> A computation produces an artifact. The artifact does not carry its own
> license to conclude. Grand Portage records what each modelling step *loses*
> and refuses the conclusions that loss does not support.

Four failure modes would each sink it, and they are not equally likely:

1. **A wrong cell in the transport table.** The system would then refuse sound
   steps or license unsound ones *with confidence*, which is worse than not
   having it. **Five cells were wrong in v0.1 and all five were in the
   `IDENTITY` row.** See §1.
2. **A leaky boundary.** The enforcement claim is "no CAS process without a
   declared edge". **It was false twice** — once inherited, once introduced by
   the fix for the inherited one. See §2.
3. **It induces plausible mislabelling.** If the required `edge` argument makes
   people pick the type easiest to justify rather than the true one, it
   launders guesses into typed facts. **Still unmeasured.** T1 tests it.
4. **It misleads a reader about a campaign's state.** Distinct from unsoundness
   and newly demonstrated: T3's agent read a healthy campaign as a failing one
   because no read path showed accepted findings. See §5.

---

## 1. THE TRANSPORT TABLE — attack this first

`grandportage/kernel.py`, the `TRANSPORT` dict. Everything else is data or
plumbing. Gate 0 (`tests/test_cell_ledger.py`) now carries one row per cell with
a proof, a counterexample, or the exact side condition — **read the arguments,
not just the verdicts.** Two rows have already been wrong while the cell was
right, and no test can catch that.

Semantics: edges point **tighter → looser**, `V(src) ⊆ V(dst)`. `ALONG` is
src → dst. `AGAINST` is dst → src, the direction emptiness travels.

**The v0.1 errors, all one mistake.** An identity is a claim about *functions*,
and the ring map `O(dst) → O(src)` runs **opposite** the point map. So
identities pull back and do not push forward. Five cells assumed otherwise:

| cell | licensed, falsely |
|---|---|
| `NECESSARY_CONDITION/ALONG` | `x = 0` escaping `V(x)` to the whole line |
| `EQUIVALENCE/*` | a rewriting across a **point**-level equivalence; `V(x²)` and `V(x)` share one point and disagree about `x = 0` |
| `SPECIALIZATION/AGAINST` | lifting `p·x = 0` out of characteristic `p` |
| `SPECIALIZATION/ALONG` | gated on the **map** being denominator-free; reduction needs the **claim's** coefficients `p`-integral |
| `BASE_EXTENSION/AGAINST` | `x²+1 = (x+i)(x−i)` descending to `Q`, where `i` is not unproved but *inexpressible* |

**What I want checked now:**

- **Is `IMAGE_CLOSURE/ALONG/IDENTITY` right to be unconditional?** I argue yes:
  the image is dense in its closure, so the pullback is injective. That makes it
  the one lossy type where identities travel *with* the arrow, and it is the
  cell that shows a uniform "identities only pull back" rule would be too
  strong. If that is wrong, the whole repair is misconceived.
- **`identity_origin` is a claim-level approximation.** `AMBIENT` (holds before
  the model's equations) is *sufficient* for surviving a widening, not
  *necessary* — the exact condition is `LHS − RHS ∈ I(dst)`, which is
  edge-relative. Registered in `KNOWN_CONSERVATISM`. **Is the approximation the
  right one, or does it refuse something common?**
- **`integral` and `coefficients_in_base` are the same question twice** — do the
  rewriting's coefficients lie in the target's coefficient ring? Consulted at
  the two edge types that change that ring. **Should they be one declared
  coefficient ring instead of two booleans?** They cannot be today: models carry
  `field` as free text, so the kernel cannot compare fields.
- **`DEGREE_COUNT` in `BUILTIN_CERTIFICATES`** → `SCHEME`. Is it really
  field-independent in every use, or only where leading coefficients do not
  vanish? Unchanged since v0.1 and still the entry I trust least.

## 2. THE CAS BOUNDARY — attack this second, and expect to win

`grandportage/cas.py`. The module docstring claims **"there is no string path to
a solver."** That claim has now been false twice.

- **v0.1:** `body` and the expression half of `decls` went to Singular
  unvalidated. `body=["poly g0 = 1;"]` shadowed a ring variable.
- **v0.2, introduced by the fix:** the decl **type** half, `ring`, `ring_vars`,
  anything behind a `//` comment (the token matcher failed **open**, and
  `execute()` ran), and multi-line entries. Reproduced against real Singular:
  the same ideal `(g0)` returning `GP_G[1]=1`, exit 0, no error, parsing
  cleanly, recorded into the graph through the MCP tool.

Both fixes were denylists. The current one validates five fields and strips
comments. **A denylist over a real grammar extended by one round of adversarial
thinking gets exactly one round deeper**, and that is now an empirical claim
rather than an aesthetic one. The real fix is a typed statement AST with no free
strings, deferred to v0.3.

**So: find the third bypass.** It is the single most valuable thing this review
can produce, and the prior on it is high.

## 3. SCOPE DERIVATION AND THE CERTIFICATE

`kernel.derive_scope`. An emptiness claim's scope comes from its *certificate
kind*, never from the author's label — and this is the field the T2 audit found
the tool's own author mislabelling in the tool's own fixture.

**Gap A is still open: nothing validates a certificate against a computation.**
v0.2 built the pattern for a different field — `cas_classify_identity` decides
`identity_origin` by reducing `LHS − RHS` instead of asking — but certificates
are the harder instance, because *"does this computation support this
certificate kind?"* needs interpretation where origin classification does not.

Built-ins can no longer be redefined from a graph. Restating one identically
still works, because that is how branches merge.

## 4. THE `IDENTITY` VOCABULARY — the newest and least exercised

Three new declarable attributes, all shipped in one pass, all with **two live
claims between them** across the whole corpus:

- `identity_origin` on claims — `AMBIENT` / `DERIVED` / `UNKNOWN`, blank raises
- `ring_iso` on `EQUIVALENCE` edges
- `integral`, `coefficients_in_base` on claims

`UNKNOWN` is the `UNTYPED` bargain one level down: a required field whose honest
answer is always available. **Is that bargain actually honoured, or does
`UNKNOWN` become the default in practice and quietly disable the whole row?**
That is a prediction on the record for T1.

`ring_iso` deserves particular suspicion: it is an **unaudited boolean** that
re-opens every cell it gates. There is no `UNJUSTIFIED-RING-ISO` rule
corresponding to `UNJUSTIFIED-EQUIVALENCE`, and nothing asks for the inverse
map. In v0.2 it was also unreachable through the supported path while settable
through the raw one — fixed, but the asymmetry of care is the smell.

## 5. THE READ SURFACES — a category the other sections miss

Nothing here can license a false conclusion. It can only cause a human to draw
one, which is why the v0.2 pass never looked and why T3 found three defects at
once: no read path showed accepted findings, `portage_check`'s `full` parameter
was declared in its schema and never read, and `gp show` printed neither
inferences nor claim certificates while MCP's `portage_show` printed both.

A fresh agent consequently reported a campaign whose nine findings had all been
examined and accepted as *"gate failing, five live blockers."* Exact inverse.

**Attack this by asking a human question, not a soundness one:** *"what is the
state of this campaign, and what is it carrying on purpose?"* Then check the
answer against `.portage/baseline.json` by hand.

## 6. THE GRAPHS — the best available evidence about failure mode 3

`docs/first-run/campaign-graph.jsonl`, ten edges declared by an agent doing real
work. For each: is the type correct or merely defensible? Is the **direction**
right? Does `drops` name what is lost or restate `why`? Where `UNTYPED` was
chosen, was that honest or evasive?

Hardest to look at: `GE7`/`GE8`/`GE9` (the γ-chart family) and `GE10`.

**Note the observer effect:** that agent had read `BRIEF.md`, which names
mislabelling as the worst failure mode. It then avoided it. Weak evidence, and
T1 exists to replace it.

**Gap B is unfixed on purpose.** Two auditors found `GE7`/`GE8`/`GE9` are case
branches, not relaxations, and the type system has no vocabulary for a
containment that holds only on a branch. Leaving it open is what makes T1
informative about it — if a blind agent hits the same wall independently, that
confirms the gap is systematic rather than one agent's slip.

The deeper form of the question, which I now think is the right one: **does a
model node denote a conjunction of conditions or a union of branches?** For a
conjunction, "more informative" and "smaller solution set" coincide. For a
union they invert — which is exactly how `GE2` came to be drawn backwards while
its own prose said the right thing.

## 7. WHERE THE BODIES ARE BURIED

Six defects found and fixed. **Five are the same family — quiet damage between a
producer and its consumer — and that family is the reason this project exists,
so a seventh is likely.**

1. `poly g0 = ...` shadowing a ring variable, producing false `UNIT` verdicts at
   every prime *(inherited)*.
2. An illegal `_ASSAY_` identifier: Singular errored, kept going, printed empty
   markers, **exited 0** *(inherited)*.
3. `_parse_outputs` capturing one line of a multi-generator basis, so
   `GP_G[1]=f6` read as "the ideal is `(f6)`" *(mine)*.
4. `gp accept --only` **replacing** the baseline instead of merging, destroying
   a version-controlled record of knowingly-carried obligations. The broken path
   was the one the docs recommended *(mine, caught by luck)*.
5. A bulk `gp accept -m` overwriting the per-finding reason of every
   already-accepted finding — **#4 again, narrower**, and it survived the fix
   for #4 *(mine, found by external review)*.
6. The v0.2 CAS fix closing two of five doors and claiming the room was sealed
   *(mine, found by external review)*.

**The pattern in #5 and #6 is worth more than either.** Both are *the same
mistake as the thing being fixed, committed while fixing it*: #4's lesson was
"destroying a record must be explicit" and #5 destroys records; the original
boundary bug was "validated one field, waved through the one beside it" and #6
validates three fields and waves through the three beside them.

**Fixing a defect appears to make its neighbourhood *less* visible, not more.**
If that generalises, the highest-value review target is always the code written
in the last repair — not the code that has sat untouched.

## 8. Things I already know are weak

Stated so review effort is not spent rediscovering them.

- **`ring_iso` and `integral` are unaudited booleans.** No rule asks for
  evidence, unlike `EQUIVALENCE` which at least has `UNJUSTIFIED-EQUIVALENCE`.
- **Coverage detects absent structure, never weak structure.** A declared but
  too-weak component is invisible. Inherited from the whole coverage tradition.
- **One incident per axis.** `place` and `order` each fire and each is
  necessary, but neither shows discrimination *within* an axis.
- **Merge safety is unit-tested only.** No two real agents have ever merged.
  T4 is now unblocked (the fold was order-dependent until v0.2 and that would
  have made T4 measure the wrong thing).
- **`ladder` is unvalidated free text.** Nothing checks that
  `independently-audited` means what a campaign means by it — and the CL-DICT
  verification found a case where a source repo's own "two independent
  mechanisms" claim was one mechanism written twice.
- **No timestamps.** Deliberate — the files stay diffable and git carries the
  when — but a baseline entry cannot say *when* a debt was accepted, and a
  resuming reader cannot tell what the last session was working on.
- **Gap C, D, E from the T2 audit are all still open:** an inference can attach
  to a proxy edge; there is no retraction mechanism; `ev: "note"` bypasses the
  checker entirely.

## 9. What a good review produces

In descending order of value:

1. **A third CAS bypass.** §2. High prior.
2. **A wrong cell, or a ledger row whose argument does not match its cell.**
   §1. Two such rows have already been found and both had correct verdicts —
   a test checks a verdict, never a reason.
3. **A seventh member of the §7 family**, ideally in code written during the
   v0.2 repair.
4. **A layer disagreement.** MCP schema, `Transport`, the fold and the kernel
   must agree what a field means. `witness` meant opposite things in two layers;
   `ring_iso` existed in one and was rejected by another; `full` was declared in
   a schema and never read. That is three, so look for a fourth.
