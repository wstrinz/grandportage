# BRIEF — first run of Grand Portage on real work

**Read this before starting. It changes what counts as success.**

## What this is

Grand Portage is a **v0.1 prototype**, and this is the **first time it has been
pointed at live work**. It has 160 checks behind it and two domains of
retrodiction against answer keys pinned before the code existed, so the checker
is not what is on trial.

**Two questions are on trial, and they are separate:**

1. **Does it work?** Do the MCP tools behave, does the hook fire when it should
   and stay quiet when it should not, do the error messages make sense, does
   anything crash or block spuriously?
2. **Is it useful?** Does being *required* to declare what each computation
   step loses help you think, or is it a tax you pay to get to the maths?

**A "no" on either is a real result and is what this run is for.** Do not
manage the outcome. A finding of "this is a tollbooth and here is exactly where
it got in the way" is more valuable than a session that went smoothly because
the tool was quietly avoided.

## The one rule that protects the experiment

> **Use the MCP CAS tool for algebra even when a direct sympy call would be
> faster, and if you route around it, say so and say why.**

This is the whole risk. When a required argument is annoying, the natural move
is to drop to a script and skip it — and then the session goes fine and we
learn nothing. Every time you find yourself wanting to bypass
`cas_ideal_is_unit` or `portage_declare`, that impulse **is the data**. Write it
down instead of acting on it, or act on it and write down that you did.

Same for the hook: if it blocks you, do not delete it and carry on. Record what
it blocked, whether the block was correct, and whether the discharge message
told you what to do next.

## The tools

Start with these two, in this order:

- `portage_show` — the graph is the state, so read it first. Four obligations
  are already recorded and accepted into the baseline; they will not block you.
- `portage_transport_table` — the five relaxation types and the certificate
  registry, printed from the kernel. Read it before deciding an edge type.

Then:

- `cas_ideal_is_unit(ring_vars, generators, produces, describes, edge)` — runs
  Singular (via WSL) and records the typed edge. **`edge` is required.** There
  is no default and no inference; omitting it is an error before any solver
  process starts.
- `portage_declare(events)` — record models, claims, inferences, certificates.
  This is how a conclusion gets submitted to the checker. **An unrecorded
  conclusion is an unchecked one.**
- `portage_check` — findings plus their discharge moves.

`gp check`, `gp show`, `gp table` do the same from the shell if that is easier.

### On `edge`

Every computation that produces a new model has to say how that model relates
to its source. The question the schema asks is **"what does this step LOSE?"**,
not "what kind of step is this" — the second invites a guess, the first has an
answer you already know:

| loses | type |
|---|---|
| nothing, and you can exhibit the converse | `EQUIVALENCE` |
| equations | `NECESSARY_CONDITION` |
| a larger coefficient field | `BASE_EXTENSION` |
| an elimination or projection (you get the Zariski *closure*) | `IMAGE_CLOSURE` |
| a change of characteristic | `SPECIALIZATION` |
| not yet known | `UNTYPED` + `debt_why` |

`UNTYPED` is legal and is the right answer when you genuinely do not know.
**Prefer it to a guess.** It records the hole, blocks conclusions across it, and
costs nothing until you try to conclude something. Silence is the only illegal
option.

## The task — Step 2 of the γ-window compiler

From `math-stuff/d2_plane_72_108/SESSION_HANDOFF.md`, "Step 2 — NEXT, and not
started":

> Derive **(a5)** `deg_y(C_{−k}) ≤ k+2` from the γ-chart map — `x ↦ xy³,
> y ↦ y⁻²` for γ=3; `x ↦ xy², y ↦ y⁻³` for γ=2 — acting on the reduced polygons
> that `polygon_reduction.case_f2(0)` already derives (`P: [(0,0),(0,10),(6,0),
> (8,2)]`, bracket `x²`, matching GGV3's published `deg P₁ = 10`,
> `deg Q₁ = 15`).
>
> **Build it for γ ∈ {2,3,4}**, not {2,3}.

That last line is the point of contact with the tool. `GI-GAMMA-IMPORT` — one
of the four accepted obligations — is exactly the reason you cannot narrow to
{2,3}: GGV3 §5 asserts γ ∈ {2,3} **without proof** (`tex:1716`, verbatim: *"We
do not provide proofs for this first part"*), while the corner layer derives
only γ ∈ {2,3,4}. Note also that `polygon_reduction.case_f2`'s own repair
comment records `chart_exponent(5,20) = 4`.

There is **no published chart map for γ=4**. Deriving one, or establishing that
none exists, is part of the work.

### Entry points (all read-only, in the pinned submodule)

```
math-stuff/d2_plane_72_108/polygon_reduction.py    case_f2(0)
math-stuff/d2_plane_72_108/gamma_from_corner.py    step 1, 43 checks
math-stuff/d2_plane_72_108/ENDPOINT_CONTRACT.md    the window contract
math-stuff/d2_plane_72_108/SESSION_HANDOFF.md      full context
```

**`math-stuff/` is READ-ONLY.** It is a submodule pinned at `86d8fb0`. Read it,
import from it, run against it — write nothing to it. New work goes in this
directory.

## What to record

Keep `FINDINGS.md` in this directory as you go. Two sections, and the second
matters more:

**Does it work** — anything that crashed, blocked wrongly, printed something
confusing, or made you look up what a field meant.

**Is it useful** — and be specific rather than kind:

- Where did declaring `edge` make you notice something you would have skipped?
- Where was it pure overhead — you knew the answer and typing it changed nothing?
- Did you ever pick a type because it was the easiest to justify rather than
  because it was right? (That is the most important failure mode there is: a
  tool that induces plausible mislabelling is worse than no tool.)
- Did any discharge message actually tell you what to do next?
- How many times did you want to bypass the tools, and did you?

## What good and bad both look like

**Working and useful:** the `edge` argument caught a step you were about to
take without thinking, or `UNTYPED` let you record a real gap instead of
papering it over.

**Working but not useful:** everything behaved, and declaring edges was pure
transcription of things you already knew. → the fix is probably a
`portage_suggest_edge` tool that proposes a type from the computation's shape
and makes you confirm it. **Deliberately not built yet**, because building it
before this run would be guessing at the answer to the only question this run
exists to settle.

**Not working:** it blocked something correct, or the graph would not fold, or
a message was unusable. → file it precisely; the tool is four days old.

Do the mathematics properly regardless. The tool is being tested *by* real
work, not instead of it.
