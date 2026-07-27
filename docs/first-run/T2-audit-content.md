# T2 audit — lens 3: `drops` / `witness` / `map_kind` content quality

Independent auditor, no access to `FINDINGS.md` or `BRIEF.md`. Read the graph,
the mathematics, the code, and the source repo.

**Verdict: the metadata fields are doing real work in three of six edges, and
are decorative or wrong in the other three.**

---

## Findings that concern the TOOL (not the campaign)

These matter most, because they are defects in Grand Portage rather than in the
work it was recording.

### 1. An inference can be attached to a proxy edge, and nothing catches it

`GI-G4-CAP-EXTRAPOLATION` asserts *"the γ=4 window cap can be read off the γ=2
and γ=3 values of α"* and is recorded on `path: [["GE10", "AGAINST"]]`.

`GE10` is `GCHART_G4 → GCHART_G4_LEDGER`. The **asserted step is not that
edge** — it is an extrapolation *across the chart family*, from `GCHART_G2` and
`GCHART_G3` to `GCHART_G4_LEDGER`, and no edge with those endpoints exists in
the graph. The refusal was correct; the reason was not.

**This is structurally the same defect `GI-BRIDGE` exists to catch** — a join
asserted between objects with no edge between them — committed by the framework
in its own bookkeeping. Path continuity (`store.validate`) checks that the path
*connects*; nothing checks that the path is the step the `asserted` text
describes. An author can attach any assertion to any connected path.

**This is the highest-value finding of the audit and it is a real gap.**

### 2. `map_kind`'s documented criterion does not produce the declared values

The schema says POLYNOMIAL/IDENTITY_MAP iff "the coordinate change is
denominator-free". Under the **forward** map that is false for all three chart
edges: `φ₃(y) = y⁻²` and `φ₄(y) = y⁻¹` are equally not denominator-free, yet
GE7/GE8 are `RATIONAL` and GE9 is `POLYNOMIAL`.

The values are *correct* — but the operative criterion is **pullback
integrality** (`φ⁻¹` integral iff δ=1, equivalently |det| = 1), which the schema
never states. This is load-bearing: `map_polynomial` is the cell that licenses
`IDENTITY` rewriting across a `NECESSARY_CONDITION` edge, so GE9 is granted a
transport GE7/GE8 are refused, on a justification a checker cannot reproduce
from the field's own definition.

### 3. The ladder is unvalidated free text, and it bit

`GC-A5-DERIVED` is graded `exact-checked`, but its own cite concedes the slope
was **fitted**, and `gamma_chart.py`'s `fit_alpha` docstring says so outright:
*"alpha is FITTED to published data, not derived — that is exactly the debt this
module records."*

The asymmetry is the finding: **α at γ=4 was refused as "two points, one guess"
and recorded as a type error; α at γ=3 was obtained by the same non-derivation
and graded `exact-checked`** on the strength of having five fit points instead
of zero. The type layer caught one and the evidence layer waved the other
through — which is exactly the orthogonality the design claims, working against
itself when nothing validates a ladder grade.

---

## Findings that concern the CAMPAIGN

### GE9's witness is wrong, and a better one was already in the graph

Declared witness: *"δ=1 means φ₄ imposes no congruence at all, so the γ=4
ledger is strictly DENSER … every y-exponent is legal in every slot."*

Three defects: it witnesses the **absent** drop (the congruence) rather than the
declared one (polygon shape); it compares dst to a **sibling** (G2/G3) rather
than to src; and "every y-exponent is legal in every slot" is **contradicted by
`GCHART_G4`'s own model description**, which carries the depth floor
`J ≥ 5(I−1)` — at `I=0` that forbids `J = −6`. Density cannot be asserted at all
while the cap is the open obligation `GE10` records.

**And the graph already contains the right witness, unused.**
`GC-DELTAPRIME-IS-GAMMA1` establishes that `Δ′ = {(0,0),(3,0),(4,1),(0,5)}`
reproduces all three published integers (`[P₁,Q₁]=x²`, `deg P₁=10`,
`deg Q₁=15`) while having `deg_x = 8` against the 2 that γ=4 requires — an
exhibited polygon consistent with everything the target retains and not the
source's. Transcription replaced an available exhibited witness with an
assertion.

### The witnesses point the wrong way on GE7 and GE8

Both exhibit points of the **source** satisfying the dropped congruence. A
`NECESSARY_CONDITION` witness must exhibit a point of **dst \ src**. Showing
that published solutions obey the congruence is, if anything, weakly consistent
with the target implying it. Not assertion — *inverted* evidence.

GE8's is the stronger of the two: the exponent lists **saturate** the
congruence class between cap and floor, which is real evidence the congruence is
operative rather than coincidental.

### `drops` restates `why` on three of six edges

Worst on GE8 (verbatim, same symbols). Structurally unavoidable on
`E-G3_ELIM_NO_A5`, where exactly one generator was removed and naming it *is*
the content — a schema complaint, not a quality failure.

### One witness meets the standard completely

`E-G3_ELIM_NO_A5`: an exhibited K-rational point (`a=0`, with the degeneration
`E = −S·T` and `S≠0, T=0`), independently re-verified against
`g3_kill_generators()` — all 14 generators vanish, and `1−w·a = 1 ≠ 0` puts it
genuinely outside the source. **This is what the other five should look like.**

### `E-G3_ELIM_KILL`'s witness is maximal but does not say so

`G3_ELIM_KILL` is declared `EMPTY`, so a dst-point witness is **impossible in
principle** and the structural (variable-occurrence) witness is the strongest
available. The record does not say this, so a reader cannot tell whether the
author reached for a point and failed or knew none could exist.

### `GC-G4-CHART-EXISTS` overstates

*"a γ=4 chart at (5,20) **exists**"* conflates "the γ=4 member of the family is
well-defined and unique" (true, exact-checked) with "a γ=4 window system is
realized at (5,20)" (open — it is precisely what `GI-GAMMA-IMPORT` records).

---

## Rework queue, auditor's priority order

1. GE9 `witness` — replace with the Δ′ object already in the graph
2. `GC-A5-DERIVED` ladder/statement — `exact-checked` for a fitted α
3. `map_kind` semantics across GE7/GE8/GE9 — state the pullback convention
4. `GC-G4-CHART-EXISTS` — "well-defined and unique", not "exists"
5. GE8 `drops[0]` — verbatim restatement
6. `GI-G4-CAP-EXTRAPOLATION` path — recorded on a proxy edge
7. `E-G3_ELIM_KILL` witness — add "dst is EMPTY, so this is maximal"
8. GE7 `witness` — supply a genuine dst\src point
9. GE10 `map_kind` — absent where GE4/GE5/GE6 carry `IDENTITY_MAP`
