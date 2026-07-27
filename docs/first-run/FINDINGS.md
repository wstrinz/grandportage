# FINDINGS — Grand Portage first run

Started: 2026-07-26. Tool version: grand-portage @ 09466d9, v0.1.0.
math-stuff pinned at 86d8fb0.

See BRIEF.md for what is being tested. Both "it works" and "it is useful" are
separate questions and a "no" on either is a result.

Task: Step 2 of the γ-window compiler — derive (a5) `deg_y(C_{-k}) ≤ k+2` from
the γ-chart map, for γ ∈ {2,3,4}.

---

## Does it work

**Everything ran. Nothing crashed. Two rough edges, one of them real.**

1. **`portage_show` / `portage_transport_table` are exactly the right first two
   calls** and I used them in that order without being told twice. The table's
   left column is `edge type × direction × claim kind`, which is the shape of
   the question you actually have. No complaints.

2. **The hook fired, and the block was CORRECT but the discharge message was
   incomplete.** I deliberately recorded `GI-G4-CAP-EXTRAPOLATION` — an
   inference across an `UNTYPED` edge — in order to put the residual obligation
   *on the record as a type error*, which is exactly the design pattern the
   graph's four baselined findings already use (`GI-GAMMA-IMPORT` is the same
   shape). The write succeeded; the hook then blocked me.

   The block is right: I did record an unsound step. But the discharge message
   offers exactly one move —

   > *"Name the relaxation. What does this step LOSE? ... Until it is named, no
   > conclusion crosses this edge."*

   — and that move is **unavailable by construction**. If I could name the
   relaxation, there would be no obligation to record. The other legitimate
   move, `gp accept --only <id> -m "why"`, is documented in README.md but is
   **not mentioned anywhere in the discharge text**. A first-time user hits a
   wall whose only signposted exit is the one that is closed.

   → *Fix:* when a finding is `UNSOUND_PREMISE` on an `UNTYPED` edge whose
   `debt_why` is populated (i.e. the author has already said "I know, and here
   is why I can't type it"), the discharge should offer both moves: name it, or
   accept it into the baseline with a reason.

3. **`gp accept --only <id>` DESTROYS the existing baseline. This is the one
   real bug and it is a bad one.**

   `README.md` documents `gp accept --only <id> -m "why"` as the way to
   *"knowingly carry **one more** finding"*. It does not carry one more. It
   replaces the file.

   ```
   before:  accepted = [GI-BRIDGE, GI-GAMMA-IMPORT, GI-REPLAY-TRANSFER,
                        GI-WINDOW-CONFLATION, GE4, GE5, GE6]     (7 entries)
   after `gp accept --only TRANSPORT:GI-G4-CAP-EXTRAPOLATION`:
            accepted = [GI-G4-CAP-EXTRAPOLATION]                 (1 entry)
   ```

   Seven entries and the campaign's `note` gone, no warning. Root cause is two
   lines: `cli.py:150-153` computes `findings = C.run(g)`, filters to `--only`,
   and hands the result to `hook.save_baseline`, which at `hook.py:95` builds
   `payload = {"accepted": sorted(f.fid for f in findings), ...}` and writes it.
   Nothing ever reads the file it is about to overwrite. Without `--only` the
   behaviour is accidentally correct (all findings are re-listed); `--only` —
   the documented incremental path — is the broken one.

   **How I noticed, and why that matters:** I noticed only because the hook
   *immediately* went red again with the four baselined findings I had never
   touched. If the tool had been quieter, or if I had accepted the *last*
   obligation of a session rather than one in the middle, this would have
   silently discarded a campaign's entire record of knowingly-carried
   obligations — and the file is version-controlled and read by humans as the
   authoritative list. That is the failure mode the tool exists to prevent,
   occurring in the tool.

   I restored `.portage/baseline.json` by hand from `git show HEAD:` and left a
   note in it. **Fix:** `save_baseline` should merge with `load_baseline`, or
   `--only` should be `--add` and refuse to run without it.

4. **The hook blocks *all* tool calls, including the ones that would discharge
   it — and including writing this file.** The matcher is `"*"`, so once a
   finding is live, `Read`, `Write` and unrelated `Bash` all fail. I could not
   write down what the hook had blocked until I had un-blocked it, which
   inverts the order BRIEF.md asks for. It also means the failure text is
   emitted once per attempted call — I saw the same 40-line block five times in
   a row.

   Not obviously wrong: a hard stop is the point. But `PostToolUse` on `*` is a
   blunt instrument, and exempting reads (`Read`, `Grep`, `Glob`) would cost
   nothing in enforcement and a lot less in flailing.

5. **There is no way to smoke-test `cas_ideal_is_unit` without writing to the
   graph.** Every call requires `produces` (a model id) and `edge`, so the
   cheapest possible "does Singular actually work through WSL from here" probe
   permanently adds a model and an edge. I wanted a health check and the only
   available one was a real declaration. Minor, but it pushed me toward
   composing the *real* call first and finding out about plumbing failures
   inside it — the opposite of what you want on a first run.

6. **`cas_ideal_is_unit` worked first time, through WSL, on a 16-variable /
   15-generator system, and its result line is honest.** `GP_G = GP_G[1]=1`,
   followed by prose refusing to call it a kill until a certificate kind is
   attached. That refusal is correct and I would have skipped the step without
   it. The second run returned `GP_G[1]=f6` — non-unit — which is the *first
   element of the basis*, not the basis; the output format does not say so, and
   a reader could take `GP_G = GP_G[1]=f6` for "the ideal is (f6)". It is not.
   Print the length, or the whole basis, or say "leading element".

7. **Idempotent-redeclaration is loud and correct** — I hit no conflicts, but
   the error text in `store.py` ("the fold will not blend them") is the right
   posture and I'd have known what to do.

8. `portage_declare` returning the full `portage_check` output on every write is
   good: I never had to remember to check. It does mean the four baselined
   findings are re-printed on every single call, which is ~40 lines of noise per
   write once you have a real graph. Worth a `--quiet`-equivalent.

## Is it useful

**Yes on two specific occasions, and I can name them. Overhead on one.**

### Where `edge` caught something I would have skipped

**(1) `map_kind` on the γ=3 chart forced me to look at a determinant, and the
determinant is the whole finding.**

I was about to declare the step `REDUCED_5_20 → GCHART_G3` and had to answer
`map_kind: POLYNOMIAL / RATIONAL / IDENTITY_MAP`. `y ↦ y^{-2}` has a
denominator, so `RATIONAL`. That made me actually compute the exponent matrix,
and its determinant is **−2, not ±1**. GGV3 calls φ₃ "the automorphism φ of
K[x,y,y⁻¹]" (tex:1735). **It is not an automorphism.** It is an injective
endomorphism — a 2-fold cover — and its image lies in the sublattice
`J ≡ γI (mod δ)`.

That is not pedantry, it is the missing information in the model: **every
congruence pattern GGV3 states as unexplained data is that sublattice.**
(a6)'s `C_0` has only even y-exponents; (a3)'s `F_{-1} = y⁷` only odd;
(b5)'s `C_{-1}` runs `1, −2, −5, …, −20` and (b6)'s `C_1` runs `−1, −4, −7, −10`
— all exactly `J ≡ 2I (mod 3)`. Nothing in (a1)–(a6) or (b1)–(b6) says so.
So the `drops` field has a real entry: **stating the conditions abstractly, as
`f2_tower.py` does with literals, throws away the congruence.**

I would not have computed that determinant if the schema had not asked. I'd
have written "coordinate change, fine" and moved on. This is the single
strongest data point for the tool in this session.

**(2) The transport table forced the direction of the kill, and the obvious
reading is the wrong one.**

I intended to model GGV3's elimination of `C_{-3}..C_{-7}` as a step and then
transport the resulting emptiness. `IMAGE_CLOSURE` (an elimination) carries
`EMPTY` **AGAINST** the arrow and not ALONG. So the kill flows
`eliminated model → full model`, i.e. backwards along the projection. I had it
the right way round only *after* reading the row. And it flagged a related
trap I was about to walk into: I considered truncating the deep window
(`C_{-3}..C_{-7}`) to keep the Gröbner basis small. Truncation adds equations —
a `NECESSARY_CONDITION` with the *truncated* model as the tighter one — and
`EMPTY` does **not** travel ALONG that edge. **A kill proved on a truncated
window proves nothing about the real one.** I would probably have truncated and
believed the answer.

**(3) The claim-kind column stopped me making a claim I had already typed into
a print statement.**

I wrote `"(a5) IS LOAD-BEARING HERE: drop 1-w*a and the ideal is no longer the
unit ideal"` into `gamma_chart.py`'s output — as an assertion, from having
looked at the algebra. Before publishing it I ran the negative control
(`G3_ELIM_NO_A5`). It was right, but only because I checked. Then the table
made me notice the second half: the result is `NONEMPTY` at the *target* of a
`NECESSARY_CONDITION` edge, and `NONEMPTY`/AGAINST is **NO** — so the witness
says nothing about the source and must not be read as weakening the kill. It is
a statement about which hypotheses the *proof* needs, not about the geometry.
I recorded the claim and **deliberately recorded no inference from it**, with
the reason written into the note.

That distinction is exactly the sort of thing that gets lost in prose and then
resurfaces two sessions later as "but we showed it was nonempty".

### Where it was pure overhead

`GE9` (`REDUCED_5_20 → GCHART_G4`). Once `GE7` and `GE8` were written, `GE9` is
the same sentence with δ=1 substituted. Filling in `why`, `drops`, `witness`,
`cite` for the third member of a one-parameter family was transcription. The
only thing that changed — and it *is* interesting — is that δ=1 makes the map
unimodular, so the covering loss vanishes and `map_kind` flips to `POLYNOMIAL`.
But I already knew that from writing `GE7`. **Cost paid: ~4 minutes of typing
for one bit of information.** This is the case `portage_suggest_edge` would fix:
propose the neighbour's type and `drops`, make me confirm and diff.

### Did I pick a type because it was easy to justify?

**Once, nearly, and the schema is what stopped me.** For `GE10`
(`GCHART_G4 → GCHART_G4_LEDGER`) I had two published values of the cap slope,
α = 1 at γ=3 and α = 1/4 at γ=2, and `α = 4^(3−γ)` fits both and would have
given γ=4 a number. Typing that edge `NECESSARY_CONDITION` and writing "the cap
extrapolates" would have been *easy to justify and wrong* — two points, one
guess. The existence of `UNTYPED` + `debt_why` as a **legal, first-class**
answer is what made recording the hole cheaper than papering over it. If
`UNTYPED` had felt like a failure state I would have fitted the curve.

That is the failure mode BRIEF.md names as the most important one, and on this
occasion the tool prevented it rather than induced it.

### Did any discharge message tell me what to do next?

**Two of three.**
- `UNTYPED-EDGE` debt → "Name the relaxation. What does this step LOSE?" — yes,
  usable, and the LOSE framing is genuinely better than "what kind of step is
  this". I answered it correctly for GE7/GE8/GE9 without looking anything up.
- `TRANSPORT: NECESSARY_CONDITION does NOT license PREDICATE ALONG` → yes, and
  the two named exits ("re-derive in the target model" / "exhibit the converse
  and retype") are the two real exits.
- `TRANSPORT` on an `UNTYPED` edge → **no**, see "Does it work" item 2. It
  offers only the move that is unavailable.

### Fields whose meaning I had to look up

- `ladder` — not in the tool schema at all; I inferred `claimed` /
  `exact-checked` / `independently-audited` from the existing graph rows and
  from SESSION_HANDOFF.md. A `portage_declare` caller who has not read the
  research repo cannot fill this in.
- `witness` — the schema says "explicit evidence that the step is NOT an
  equivalence". Clear once read, but it is optional and I nearly skipped it; it
  turned out to be where the best content went (the congruence evidence in
  GE7/GE8). Worth promoting to required for `NECESSARY_CONDITION`.

## Bypasses

**One, and it is deliberate. I did not route around the CAS tool; there was one
place it fit and I used it, and one place I judged it does not apply.**

1. **`gamma_chart.py` (the whole Step-2 derivation) is plain Python, not
   `cas_ideal_is_unit`.** Not a bypass in the sense BRIEF.md means: Step 2's
   content is Newton-polygon lattice combinatorics — exponent arithmetic,
   supporting faces, congruence classes. `cas_ideal_is_unit` is a Gröbner
   *emptiness* engine; there is no ideal here and no emptiness question.
   Routing it through Singular would have been theatre. **Recording it anyway
   because the honest version of "I used the tool" has to include "and here is
   where it had nothing to say."**

2. **Wanted to bypass and did not:** the `(a5) ⟹ C_{-1}=ay³, C_{-2}=by⁴` step.
   `y⁷ = −3C_{-1}C_{-2}` is a monomial, `K[y,y⁻¹]` is a UFD whose units are the
   monomials, so each factor is a monomial — two lines, no CAS. I considered
   forcing it through `cas_ideal_is_unit` with a Rabinowitsch generator to
   satisfy the letter of the rule, and decided that would be a *fake* datum for
   this experiment. The valuation argument is in `gamma_chart.py`
   `a5_forces_monomials()` with the reasoning written out.

3. The one genuine CAS-shaped question in Step 2 — the γ=3 kill, GGV3
   tex:1866-1878 — went through `cas_ideal_is_unit`. See below.

Running total of "wanted to bypass": **1** (item 2). Acted on it: **no**.

4. **sympy was used to *expand* the kill polynomial into 13 coefficient
   generators**, which are then handed to `cas_ideal_is_unit`. That is
   marshalling, not deciding — no algebraic question is answered by it. It is
   in `gamma_chart.py:g3_kill_generators()` so the CAS input is pinned to
   source rather than to a shell one-liner I typed once.

   One genuine modelling point came out of it: I could have passed `y` as a
   ring variable and given the identity as a *single* generator. That would
   have asked "does there **exist** a `y` making this vanish", which is a much
   weaker question than "does it vanish identically". The 13-generator form is
   the correct one. Nothing in the tool would have caught the weaker version —
   it would have run fine and returned a wrong-but-plausible answer.

---

## Verdict

**Keep it on. It found things, and it found them in the two places where I was
about to be sloppy rather than in the places I was already being careful.**

Concretely, in one session on real open work the required `edge` argument
produced: a determinant I would not have computed, which showed GGV3's
"automorphism" is a ramified cover and that the resulting congruence is the
unexplained structure in four of their own conditions; the correct direction
for an elimination-based kill, where the intuitive direction is unsound; a
refusal to truncate a window in a way that would have produced a confident
wrong answer; and — the one I care about most — it made recording a hole
cheaper than fitting a curve through two points. `UNTYPED` + `debt_why` being
*legal* rather than a failure state is what did that. If I had had to choose a
type, I would have chosen one.

Against that: the `--only` bug destroyed a version-controlled record and I
caught it by luck; the hook's `*` matcher blocks the work of discharging it;
and the discharge text for an `UNTYPED` transport names only the exit that is,
by construction, unavailable. All three are small and none is a design problem.

**On the 95/5 question the README poses** — the cost is modelling, not typing,
and that is right, but the split here was not 95/5. Roughly two-thirds of the
`edge` declarations were genuine modelling that changed what I did. The other
third (`GE9`, and most of `drops`/`cite` on the second and third member of a
family) was transcription, and it was tedious in a specific, fixable way:
**the tedium was always "say again what you said for the neighbouring edge,
with one field changed."** That is the exact shape `portage_suggest_edge` should
target — not "guess the type from the computation", but "offer the sibling
edge's declaration as a diff and make me change the field that differs." The
one bit of new information in `GE9` (δ=1 makes the map unimodular, so
`map_kind` flips to `POLYNOMIAL` and the congruence loss vanishes) is precisely
what a diff would have surfaced and a from-scratch form buried.

So: **works, with one real bug; useful, with a clear and narrower brief for the
suggest tool than the README assumed.**
