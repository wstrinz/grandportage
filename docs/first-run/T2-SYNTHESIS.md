# T2 — independent edge audit: synthesis

Four auditors, four lenses (type, direction, content, adversarial), all barred
from `FINDINGS.md` and `BRIEF.md`. Two claims verified by hand before relaying;
both held.

**Pass condition declared beforehand:** ≥ 8 of 10 edges confirmed on type *and*
direction, and no edge with a wrong direction.

**Result: FAILED on type. PASSED on direction, narrowly.** Three edges are
mistyped (two auditors converged), one is drawn backwards but inert, and the
single most load-bearing field in the system carries a value that is factually
false.

---

## 0. The finding I have to own first

**`GC-A2-KILL` declares `UNIT_IDEAL_CERT` for an ideal that is verifiably not
the unit ideal — and I wrote it**, in `fixtures/_port/gen_gamma_window.py`, not
the first-run agent.

Verified independently:

```
is 1 in I?  -> False
basis size: 19
auditor point kills all generators? -> True
```

`a2_certificate()` exhibits **nilpotency** (`g₂⁵, g₅⁴ ∈ I`), not a unit. Its own
printed verdict says so — *"terminal coeff-equations + y-order WINDOW-DEPTH
contradiction (bigraded)"* — and its docstring says outright that this is
**"NOT a scalar syzygy on the G-system generators"**. I labelled it from the
shape of the conclusion rather than from the computation.

**Why this is the worst possible place for it.** `derive_scope` is described in
its own docstring as "the single most load-bearing line in the whole system",
and it derives `scope = SCHEME` — field-independence — **from the certificate
label and nothing else**. The certificate is the one field where the author's
word is taken at face value and never checked against what was computed. So a
false label mints a false field-independence claim directly, and the note on
`GI-REPLAY-TRANSFER` then reasons *from* it:

> "Note the certificate BASE-CHANGES and the ladder is exact-checked: neither
> the evidence grade nor the field scope is what stops this."

That sentence is false as written.

The honest certificate is probably `EXACT_VALUATION_COLLISION`, which also
base-changes — so the *conclusion* may survive. But nothing in the record
establishes it, and the argument ingests `a³ = 2` as a given, which is
field-sensitive on its face.

**This is the strongest possible evidence for the fix it implies.** The tool's
author, writing the tool's own showcase fixture, mislabelled a certificate in
the one field the tool trusts blindly. No user discipline fixes that; only a
check does.

---

## 1. Convergent findings — two or more auditors, independently

### (a) `GE7`/`GE8`/`GE9` are case branches, not relaxations

*Type and direction auditors, independently.*

γ is a **function of the counterexample**, not a choice: `Chart.push` preserves
x-exponents, so `deg_x P₁ = 2δ` is an invariant of the source. A reduced pair
has exactly one γ. Therefore

    V(REDUCED_5_20) ⊆ V(GCHART_G3)     is FALSE as a total statement.

Only `V(REDUCED) ∩ {γ=k} ⊆ V(GCHART_Gk)` holds. The type auditor put it
sharply: `GCHART_G2` requires `deg_x C = 3` and `GCHART_G3` requires
`deg_x C = 2` **of the same source data**, so GE7 and GE8 cannot both be sound
containments unless `V(REDUCED_5_20) = ∅` — which is the thing under
investigation. And the only instance of the source the session actually computed
(`GC-DELTAPRIME-IS-GAMMA1`, `deg_x P₁ = 8`, i.e. γ=1) violates both.

**Live consequence:** `GI-G3-KILL-LIFTS` rides `NC/AGAINST/EMPTY` to land
`EMPTY` on `REDUCED_5_20` — killing the reduced pair outright on the strength of
one branch, which contradicts the campaign's own standing γ=4 obligation.

**One step from a worse one:** pushing `GC-A5-DERIVED` (a `PREDICATE` at
`GCHART_G3`) back via `NC/AGAINST/PREDICATE` would assert the γ=3 cap
`deg_y(C_{−k}) ≤ k+2` for γ=2 pairs, whose cap is `(k+3)/4`. **The graph would
license it.**

### (b) The (a5) negative control does not test (a5)

*Adversarial and type auditors, independently. Verified by hand.*

Dropping `1−w·a` withholds `a ∈ K^×`. But `a ∈ K^×` follows from **(a3)**, not
(a5): `F₋₁ = y⁷` and `F₋₁ + 3C₋₁C₋₂ = 0` with `C₋₁ = ay³`, `C₋₂ = by⁴` give

    y⁷ + 3ab·y⁷ = 0   ⟹   3ab = −1   ⟹   a ≠ 0 and b ≠ 0.

Confirmed: `g3_kill_generators()` emits 13 coefficient equations plus
`1−z·m₁₀` and `1−w·a`, and **no `3ab + 1`**. So the control's exhibited point
`a = b = 0` is excluded by (a3) regardless of (a5).

What (a5) actually buys is the *exponents* `p=3, q=4` — and those are hard-wired
into the generators of **both** models, so neither model varies them and neither
tests (a5) at all. (a5) *is* load-bearing, by a route the control never
exercises: the `u⁰` generator is `3a²m₁₀²` only because `2p−10` is the strict
minimum, which needs `p ≤ 4`. A genuine control perturbs `p`.

**And the conclusion escaped the checker entirely.** "(a5) is LOAD-BEARING" is
carried by an `ev: "note"` event and by prose in `STEP2_GAMMA_CHART.md` §4. The
graph correctly records *no inference* from `GC-A5-LOAD-BEARING` (`NONEMPTY`
does not travel `AGAINST`) — and the reasoning for that refusal is right — but
the mathematical conclusion was then asserted in a note, where nothing types it.

### (c) `GE10` is drawn backwards, and the refusal that depends on it is fragile

*Direction, adversarial and content auditors.*

`GCHART_G4_LEDGER` is the chart **plus** a cap, so `V(LEDGER) ⊊ V(GCHART_G4)`
and the ledger belongs at `src`. Inert today — `UNTYPED` licenses nothing. But:

> **The moment α₄ is derived and someone types `GE10`
> `NECESSARY_CONDITION`** — the natural move, and the campaign's own stated
> discharge — **the recorded path `[GE10, AGAINST]` becomes
> `PREDICATE/AGAINST/NC = yes`, and the graph licenses precisely the
> extrapolation it exists to forbid.**

A guard that disarms itself when its obligation is discharged is worse than no
guard, because that is the moment nobody is looking. Reversing the edge makes
the same claim travel `ALONG`, where `PREDICATE/ALONG/NC = NO` — a
type-dependent refusal becomes a structural one.

The adversarial auditor went further: the ledger model and `GE10` **exist only
so that `GI-G4-CAP-EXTRAPOLATION` has an edge to be refused on**. For γ=3 the
cap is simply a `PREDICATE` claim at `GCHART_G3` with no separate ledger and no
edge. Drop the ledger and the extrapolation is caught by the evidence ladder
instead.

---

## 2. Gaps in the tool

Ordered by severity.

| # | gap | evidence |
|---|---|---|
| **A** | **The certificate is never validated against the computation.** It is the one field that determines field-independence and the one field nothing checks. | §0 — the tool's author got it wrong in the tool's own fixture |
| **B** | **No vocabulary for a case-split edge.** An edge whose containment holds only on a branch cannot be expressed, so it gets typed as a total containment and licenses transports that are false off-branch. | §1(a), two auditors |
| **C** | **An inference can be attached to a proxy edge.** Path continuity checks that the path *connects*; nothing checks it is the step the `asserted` text describes. | `GI-G4-CAP-EXTRAPOLATION` asserts a cross-family extrapolation on an edge between two other models |
| **D** | **No retraction mechanism.** The log is append-only and conflicting redeclaration is a hard error, so `GE10` cannot be corrected except by hand-editing — which destroys the guarantee append-only exists to give. | forced by §1(c) |
| **E** | **`ev: "note"` escapes the checker entirely.** A conclusion recorded as a note is carried but never typed. | §1(b) |

**C is structurally the same defect `GI-BRIDGE` was created to catch** — a join
asserted between objects with no edge between them — committed by the framework
in its own bookkeeping.

---

## 3. Findings for the campaign, not the tool

- **`E-G3_ELIM_KILL` should be `NECESSARY_CONDITION`, not `IMAGE_CLOSURE`.**
  `IMAGE_CLOSURE` asserts an equality (dst = closure of the image); the target
  misses `3ab = −1`, a consequence of the source in surviving variables only.
  Harmless to the kill (`EMPTY/AGAINST` is yes for both) but it closes the
  `IMAGE_CLOSURE/ALONG/PREDICATE` cell, which is unsound here. The type
  auditor's note that the equality "survives only vacuously because the target
  came out empty, and using the computed answer to justify the type that
  transports that answer is circular" is the sharpest single line in the audit.
- **`GE9`'s witness is wrong**: it witnesses the *absent* drop, compares dst to
  a sibling rather than to src, and its claim that "every y-exponent is legal in
  every slot" is contradicted by `GCHART_G4`'s own depth floor `J ≥ 5(I−1)`. The
  right witness is already in the graph, unused (`GC-DELTAPRIME-IS-GAMMA1`).
- **`GE7`/`GE8` witnesses point the wrong way** — they exhibit points of *src*
  satisfying the dropped congruence, where a `NECESSARY_CONDITION` witness needs
  a point of dst \ src. Not assertion; *inverted* evidence.
- **`GC-A5-DERIVED` is graded `exact-checked` for a slope the producing code
  labels FITTED.** `fit_alpha`'s own docstring: *"alpha is FITTED to published
  data, not derived — that is exactly the debt this module records."* The
  asymmetry is the finding: α at γ=4 was refused as "two points, one guess" and
  recorded as a type error; α at γ=3 came from the same non-derivation with five
  fit points and was graded `exact-checked`.
- **10 of the headline "30/30 published data points" cannot fail.** `fit_alpha`
  sets α as a max over tops; `check_cap` then asserts the inequality *for those
  same tops*, which holds by construction. Plus a cap-tight-at-apex check that
  is `0 = 0` for every α. This is the vacuity failure mode the source repo has
  logged three times.
- **`map_kind`'s documented criterion does not produce its declared values.**
  The operative test is pullback integrality (|det| = 1), not forward
  denominator-freeness. Load-bearing: it gates `IDENTITY` transport.

---

## 4. What the audit says about the *first run*

The blind-run question (T1) is still open, but T2 sharpens the prediction.

The first-run agent's edges are **mostly right on direction and mostly wrong on
type**, and the type errors are all the same error: treating a case branch as a
relaxation. That is not carelessness — it is the tool having no way to say what
was true. **B is not a user failure; it is a missing feature that presents as a
user failure**, which is the most dangerous kind of gap because it looks like
the discipline working.

The one thing the agent got unambiguously right — refusing to record an
inference from `GC-A5-LOAD-BEARING`, with the correct cell cited — it then
undermined by asserting the conclusion in a note. So even the good instinct
leaked around the checker, via E.
