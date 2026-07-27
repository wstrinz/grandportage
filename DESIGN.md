# DESIGN.md — Grand Portage

## 0. What this is, at the smallest size that is still true

Computations produce artifacts. An artifact does not carry its own license to
conclude. Grand Portage records what each modelling step *loses*, and refuses
the conclusions that loss does not support.

Everything below is machinery for making that refusal **mechanical**,
**localized**, and **enforceable at the moment of spend**.

The claim is not novelty of idea. Typed relaxations, coverage metrics,
CEGAR-style signature closure and provenance graphs all exist. What is empty is
the specific slot: the provenance literature captures *what ran* — retrospective
provenance for executions, prospective provenance for recipes — and states
outright that PROV's formal semantics do not address the relationship between
provenance and the semantics of the processes described. Recipe, execution
record, and nothing about what the output *licenses you to conclude*. That is
the slot, and it is empty by the field's own admission.

## 1. Architecture

Five layers. Enforcement lives in exactly one of them.

```
  agent
    |
    | (4) MCP: wraps the CAS.  `edge` is a REQUIRED argument.
    v                          No declaration -> no CAS process spawned.
  .portage/graph.jsonl  <---- (1) store: append-only event log
    |                              fold is deterministic and total
    | (2) kernel: 5 types x 2 directions x 4 claim kinds
    v
  (3) checker  ->  findings  ->  discharge moves
    |
    | (5) hook: runs the checker after each tool call and REFUSES
    v
  agent cannot proceed
```

Drop the hook and you have telemetry. Drop the MCP server and you have a linter
nobody runs. Drop the kernel and you have a graph database.

### 1.0 kernel — `grandportage/kernel.py`

Pure stdlib, no I/O, imports nothing else in the package. Answers exactly one
question: given an edge type, a direction and a claim kind, is the transport
licensed? Plus `derive_scope`, which computes an emptiness claim's scope from
its certificate rather than trusting the author's label.

Deliberately takes plain values rather than objects, so it is callable from a
test, a checker, a mutation harness or an MCP handler without any of them
agreeing on a class.

### 1.1 store — `grandportage/store.py`

`.portage/graph.jsonl`, one JSON event per line, append-only. The graph is the
fold. Two properties earn this shape:

**Resumability.** After three weeks the graph is the state, not the transcript.
A fresh agent reads a typed artifact instead of reconstructing intent from 400
messages. That is the difference between a campaign and a session.

**Safe fan-out.** Merging branches is *concatenating logs and folding again*.
Re-declaring an entity with byte-identical content is idempotent, so branches
sharing a prefix merge silently. Re-declaring it differently is a hard error
naming both versions. So a merge of twenty agent branches either composes or
fails loudly — and merging twenty *untyped* branches is precisely how you
generate the error class this lineage already shipped an erratum for.

Validation is at fold time, not check time. A claim asserting field-independence
on a field-relative certificate is a **malformed graph**, not a finding: letting
it in and flagging it later would mean the graph itself records something false.
Same for a disconnected inference path, an untyped edge with no stated debt, and
a severity override with no reason.

### 1.2 checker — `grandportage/check.py`

Deterministic, no model in the loop. Five rules:

| rule | fires when |
|---|---|
| `TRANSPORT` | an inference's path crosses an edge that refuses its claim |
| `TAINT` | a model was *built by* a refused inference |
| `COVERAGE` | `touched(axis) \ declared(model, axis)` is nonempty |
| `REFINEMENT-TYPE` | a refinement edge is typed as anything but `NECESSARY_CONDITION` |
| `UNTYPED-EDGE` | an edge records a modelling debt |

Plus `probe()`: a counterfactual transport that no inference asserts. Probes
are how the sharpest controls are written — see §3.

### 1.3 discharge — `grandportage/discharge.py`

`(edge type, direction, claim kind) -> the canonical next move`. This is the
part that lets a campaign drive itself, and it is worth being precise about how
little intelligence is involved: **it is a lookup table.**

A typed failure is localized and named — "edge E8 is `BASE_EXTENSION` and the
emptiness it carries has a field-relative certificate" is a work item with an
address, not a vague sense that something is off. Each cell has a canonical
discharge, so the loop is: compute → type the step → checker localizes the
refusal → look up the move → dispatch → repeat. A work queue derived from a type
error, which is how a build system with autofix behaves. It works because the
failure is specific enough to name the move; vague failures do not generate work.

**The honest limit, and it should be read every time this is quoted: it routes
attention to where an equation is missing. It does not find the equation.**

### 1.4 MCP server — `grandportage/mcp.py` + `cas.py`

The forcing function. The tool signature makes the transport declaration a
**required argument**:

```python
cas_eliminate(ideal=I, vars=[...], produces="SUB2_ELIM",
              edge={"src": "SUB2", "type": "IMAGE_CLOSURE",
                    "map_kind": "POLYNOMIAL"})   # REQUIRED
```

Omit `edge` and you get a `TypeError` before any CAS process is spawned.
`{"type": "UNTYPED", "debt_why": "..."}` is a legal value — an explicitly
recorded debt, which the checker reports at severity `DEBT`. What is not legal
is silence.

This is `MODELLING_GAPS.md`'s recommendation applied at the boundary: there is
no detector for "you forgot to model X"; there are good detectors for "you
modelled X somewhere and not here". The fix is not a better detector, it is a
forcing function that makes the richer object get declared, plus a ten-line
mechanical rule over the resulting inventory.

Two constraints on the implementation:

* **Keep state in `.portage/`, not in the protocol.** The MCP spec is moving
  toward statelessness at the transport layer; a transport graph is stateful and
  that state must not live in a session.
* **The identifier assert is non-bypassable.** A CAS program object must be the
  only thing the runner accepts, and its constructor must check emitted
  identifiers against ring variables and reserved words *before the program text
  exists*. This is earned by a specific defect: a `poly g0 = ...` shadowing a
  ring variable `g0` produced confident false `UNIT` verdicts at every prime for
  months, and the blast radius was contained only by a standing social rule.

### 1.5 hook — `grandportage/hook.py`

`PostToolUse`, exit 2 with the finding on stderr. The only part with teeth.

Two decisions that cost something to get wrong. It **fails closed on a
malformed graph** — that is a real defect and the agent just caused it — but
**open on a missing one**, because most tool calls in most repos have nothing to
do with a proof campaign and a hook that blocks every session gets disabled
within a day. And it blocks on findings **not in `.portage/baseline.json`**: a
campaign mid-flight legitimately carries unrepaired errata, and blocking on
those forever trains the operator to turn the hook off, which is worse than no
hook. Accepting a finding is a decision with a cost, so the baseline is a file a
reviewer can read rather than someone's memory of the normal warnings.

## 2. Data model

Seven event kinds: `certificate`, `model`, `edge`, `claim`, `inference`,
`built_by`, `note`.

The important omission: **there is no `expected_flag`.** The prototypes carried
the answer on the inference, which is right for a retrodiction artifact and
wrong for a tool — the checker must derive findings without being told which
inferences are supposed to fail. Answer keys live in `fixtures/*/expect.json`
and are read only by tests.

### Derived severity

The prototypes graded severity by hand and said so. Grand Portage derives it:

```
refused transport
  and the graph holds a claim at the conclusion's model
     asserting the OPPOSITE existence statement   -> UNSOUND_CONCLUSION
  otherwise                                       -> UNSOUND_PREMISE
edge is UNTYPED                                   -> DEBT
```

So "this is a true positive, not a conservative refusal" becomes a fact about
the graph. It turns on **model identity** — placing a `NONEMPTY` claim on the
model an inference concludes about is itself the modelling act that makes the
contradiction visible. No scope lattice is involved and none is wanted; the
field lives in the model.

This reproduces the prototypes' hand grading on 9 of 10 findings. The tenth
(`INF-A10-SURV`, graded `TRIAGE` because the project's recorded wording was
actually correct) is a fact about what was historically *asserted*, not about
the graph — so it is carried as a declared override that the store requires a
reason for and the report prints alongside the derived value.

## 3. Why probes exist

The two sharpest credibility checks in both prototypes are **counterfactual**,
and neither is a property of a recorded inference:

* **Contrast pair.** Push two emptiness claims — both computed over the same
  small field — across the *same* edge in the *same* direction. One is licensed
  and one is not, and the only difference is the certificate. As recorded
  inferences these travel over *different* edges, so comparing them directly
  proves nothing; only the probe isolates the certificate as the sole cause.
* **Non-vacuity.** Retype an `EQUIVALENCE` as `NECESSARY_CONDITION` and check it
  would now forbid something. If it would not, the positive control on that edge
  proves nothing, because the type was never load-bearing for it.

Both prototypes needed this and neither named it.

## 4. The two registers

Cells where the kernel and the mathematics disagree, kept as **data** rather
than as prose, so that "we refuse this soundly", "we refuse this out of
caution" and "we license this knowing better" are never confused. Both print in
`gp table`.

### `discharge.KNOWN_CONSERVATISM` — refused more strictly than the truth

Three entries.

1. **`IMAGE_CLOSURE / ALONG / EMPTY`.** The closure of the empty set is empty,
   so the step is sound; the kernel refuses it because the cell derives from
   the generic inclusion `V(src) ⊆ V(dst)`, which licenses `ALONG`/`EMPTY` for
   no lossy type. Kept because it is unreachable in practice — asserting the
   constructible image is empty requires computing the constructible image,
   which is the thing nobody computes — and because inheriting it unchanged
   keeps the retrodiction an exact regression.
2. **`NECESSARY_CONDITION / ALONG / IDENTITY`.** `AMBIENT` is *sufficient* but
   not *necessary*: the exact condition is that `LHS − RHS` lies in the
   **target's** ideal, which a `DERIVED` identity can also satisfy. Edge-
   relative, and the exact test needs models to carry machine-readable ideals —
   today a model is a description, not an object with equations.
3. **`IMAGE_CLOSURE / AGAINST / NONEMPTY`.** Sound under the existential
   reading of `NONEMPTY`, false under the witness reading, and the table can
   encode only one. The witness reading is pinned because it is the one every
   claim in the corpus makes.

### `discharge.KNOWN_UNSOUND` — licensed more loosely than the truth

**Empty, and it prints as `(none)` rather than being omitted**, because an
absent section is not an assertion and `(none)` is.

This register exists because its absence let a real defect hide. When
`BASE_EXTENSION / AGAINST / IDENTITY` was found to license a false descent —
`x² + 1 = (x + i)(x − i)` travelling from `Q(i)` down to `Q`, where `i` is not
merely unproved but *not expressible* — the admission was written into a test
docstring, appeared in no `gp check`, no `gp table` and no design doc, and then
survived a review that was specifically hunting it. An external reviewer had to
rediscover it from the mathematics.

The cell was fixed rather than registered, which is why the list is empty. **An
entry here is a bug with a deadline, not a design decision:** it means the tool
will confidently license something its own authors believe is false, which is
this project's stated failure mode occurring inside the project. A test asserts
the list stays empty.

## 5. What the port found in the prototypes

Recorded here rather than buried, because they are the return on making the
graph a validated data structure:

1. **A disconnected inference path.** `matroid_transfer.py` routes its Fano
   no-saturation control (a claim about the Fano ideal over `Q`) across the
   *non*-Fano saturation edge over `F₂`. There is no continuity check in the
   prototype, so it passed silently. Ported over its own edge; verdict
   unchanged, route now real. `test_store.py` keeps re-introducing it as a
   regression.
2. **An overstated annotation.** `whetstone_dag.py` describes `INF-KSYZ-REV` as
   "the direction that would be FORBIDDEN on a `NECESSARY_CONDITION` edge". True
   for `NONEMPTY` and `PREDICATE`; false for the claim actually recorded, which
   is an `IDENTITY` — and `NECESSARY_CONDITION` carries `IDENTITY` both ways
   when the map is denominator-free, which E3's is. The E3 mutation does have
   teeth, just on `INF-KSYZ` (which carries `EMPTY` ALONG) rather than on the
   inference the note points at.
3. **A published fact that lived only in prose.** "Non-Fano is representable iff
   char ≠ 2" was in `MATROID_TRANSFER.md`'s text but not in its graph, so the
   true-positive grading of the saturation trap had to be asserted. Recorded as
   a claim, it is derived. Note the kernel forces its certificate to be declared
   field-relative, which is correct: non-Fano *is* realizable over `Q`.

## 6. Build order from here

1. **MCP server** (§1.4) — the forcing function. Nothing else changes behaviour
   at the moment of spend.
2. **Hook** (§1.5) — teeth.
3. **The Jacobian program.** Point it at `d2_plane_72_108/`'s live frontier
   rather than at its history: 26 subcase-2 cells + 171 subcase-1 branches + 27
   alternate-regime branches, and roughly 300 further kills currently in audit.
   The retrodiction proves it reproduces known verdicts; the frontier is where
   it either earns its keep on open work or does not.
4. **Submodule swap.** `math-stuff` takes `grand-portage` as a submodule and
   `whetstone/` retires to a pointer.

Two questions the frontier run should be designed to answer, and neither is
answered by anything built so far:

* **Does the coverage rule generalize past one axis?** `MODELLING_GAPS.md` §3.4
  is blunt that the three documented gauge leaks are *one incident with three
  witnesses*, not three incidents — so the existing 3/3 headline overstates its
  support, and a rule that discriminates *within* the place axis cannot be built
  from that evidence. The axis machinery is generic here, but the only items
  that would tell us anything new are on axes never yet tested (base field, case
  partition).
* **Does declare-or-refuse survive contact with real use?** The cost is
  modelling, not typing. A forcing function that makes modelling mandatory at
  every CAS call is either the whole value of the tool or the reason nobody uses
  it, and no amount of design settles which.
