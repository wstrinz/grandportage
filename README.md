# Grand Portage

**Transport typing and obstruction tracking for computational algebra.**

A computation produces an artifact. The artifact does not carry its own license
to conclude. Grand Portage records what each modelling step *loses*, and
refuses the conclusions that loss does not support.

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

## Status

All five layers are built and gated: 338 checks, live against Singular 4.2.1,
and it has had one real user session — see [docs/first-run/](docs/first-run/).

* **[HANDOFF.md](HANDOFF.md) — start here if you have no context**
* [DESIGN.md](DESIGN.md) — architecture and the decisions behind it
* [REVIEW.md](REVIEW.md) — **where I am least confident**, for a reviewer
* [TESTPLAN.md](TESTPLAN.md) — what to run next and what each run could falsify

| layer | module | what it does |
|---|---|---|
| kernel | `grandportage/kernel.py` | the transport table — the only code with mathematical judgement in it |
| store | `grandportage/store.py` | append-only graph log; merge is concatenation |
| checker | `grandportage/check.py` | findings, derived severities, exit code |
| discharge | `grandportage/discharge.py` | refusal → canonical next move |
| CAS + MCP | `grandportage/cas.py`, `mcp.py` | **declare the transport or no process spawns** |
| hook | `grandportage/hook.py` | runs the checker after each tool call and refuses |

Pointed at `d2_plane_72_108`'s live front — see
[the live front](#the-live-front) below.

## The loop, end to end

```
$ python -m grandportage.mcp          # registered in .claude/.mcp.json

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

The hook then returns exit 2 on the next tool call, so the refusal blocks
rather than scrolls past. See [examples/](examples/) for the wiring.

## The six relaxation types

Edges point **tighter → looser**: `V(src) ⊆ V(dst)`. `AGAINST` is reasoning
looser → tighter, which is the direction emptiness travels and the direction
that closes cases.

Printed by the kernel itself with `gp table`, so a document quoting it and the
code applying it cannot drift apart.

| edge type | dir | EMPTY | NONEMPTY | PREDICATE | IDENTITY |
|---|---|---|---|---|---|
| `EQUIVALENCE` | ALONG | yes | yes | yes | if ring iso |
| `EQUIVALENCE` | AGAINST | yes | yes | yes | if ring iso |
| `NECESSARY_CONDITION` | **ALONG** | NO | yes | **NO** | if ambient |
| `NECESSARY_CONDITION` | AGAINST | yes | NO | yes | if denominator-free |
| `BASE_EXTENSION` | **ALONG** | **only with a certificate** | **yes** | NO | yes |
| `BASE_EXTENSION` | AGAINST | yes | NO | yes | if defined over base |
| `IMAGE_CLOSURE` | ALONG | NO | yes | if Zariski-closed | if denominator-free |
| `IMAGE_CLOSURE` | **AGAINST** | yes | **NO** | yes | if denominator-free |
| `SPECIALIZATION` | ALONG | **NO** | **NO** | NO | if p-integral |
| `SPECIALIZATION` | AGAINST | **NO** | **NO** | NO | NO |
| `RESTRICTION` | **ALONG** | NO | yes | **NO** | if Zariski-dense |
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
* **`IMAGE_CLOSURE` AGAINST / `NONEMPTY` is Chevalley.** A point of the Zariski
  closure need not lift. This is why elimination is a sound way to *derive*
  equations and an unsound source of *witnesses* — and why a cell that survives
  everything is an artifact candidate rather than a reason to buy solver time.
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
  is simply absent, and the question becomes whether a polynomial vanishing on
  an open piece vanishes throughout.

## Scope is derived, never declared

The single most load-bearing line in the system. An emptiness claim's scope
comes from its **certificate kind**, not from the author's label:

```
UNIT_IDEAL_CERT            -> SCHEME   (1 in I over Q stays 1 in I over K)
NONZERO_RESULTANT          -> SCHEME   (res in Q* stays in K*)
EXACT_VALUATION_COLLISION  -> SCHEME   (an inequality between integers)
NONSQUARE_CLASS            -> field-relative, by construction
NO_RATIONAL_POINT_SEARCH   -> field-relative, by construction
```

Declaring a field-relative certificate at `SCHEME` scope is a **fold error**,
not a finding: the graph refuses to state it at all.

## Quick start

```bash
gp init                          # create .portage/graph.jsonl
gp check                         # type-check; exit 1 if anything is unsound
gp check --json                  # machine-readable findings
gp table                         # print the transport table and certificates
gp show                          # print the graph

gp --graph fixtures/jc2/graph.jsonl check      # the JC(2) retrodiction
gp --graph fixtures/matroid/graph.jsonl check  # the matroid retrodiction
```

Pure stdlib. No solver, no network, no model in the loop. Under a second.

## The retrodiction gate

```bash
python -m pytest        # 338 checks
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
