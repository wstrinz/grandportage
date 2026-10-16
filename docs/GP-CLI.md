# `gp`: the campaign CLI

`tools/gp.py` is the only surface for a 3P campaign: no MCP and no hooks. The profile and the Kernel fold decide every status; the CLI files and renders. Run it as:

```
python tools/gp.py --campaign campaigns/3p-matroids <command> ...
```

## Commands

| Command | Does |
|---|---|
| `init` | Starts `ledger.jsonl` for the statement in `campaign.json`. |
| `claim <label> (--matroid M \| --system FILE \| --nf FILE \| --udg GRAPH [--gauge]) --kind K [--target P] (--char p \| --char0 \| --outside p,q \| --real \| --semireal \| --rat-field) [--premise NAME] [--goal yes\|no]` | Files a claim. It stays open until a receipt supports it. For the 3b forms, see [3b claims](#3b-claims). |
| `cover <label> --candidates FILE --n N --m M [--premise NAME[=data] ...] [--supports L1,L2]` | Records a candidate cover for the DECIDE goal's spine rule. It is a ledger record, not a claim. See [Graph-bound claims and the spine rule](#graph-bound-claims-and-the-spine-rule). |
| `submit <label> <receipt.json>` | GP replays the receipt. If the claim becomes held, the receipt is its support. Otherwise the refusal is logged. |
| `submit-batch <batch.json>` | The same for many receipts in one fold. `batch.json` is a JSON list of `{"label": ..., "receipt": PATH}`. Each item gets the record a single `submit` would write. If any item is refused, GP refolds without the refused receipts, so every support it appends is held by the ledger it leaves. Items held only alongside other batch receipts are resubmitted one at a time. File claims first with `claim`, which does not fold. |
| `withdraw <label> --reason TEXT [--cascade]` | Withdraws a claim, permanently (GP 0.51). Both runners retract its support and theorem warrants on every fold, so it, and every claim whose only derivations pass through it, stop being held. It folds before and after and prints the claim, what it no longer holds and any change in the goal verdict, with a warning that readers older than 0.51 will not see the withdrawal. Refused: an unknown label, a claim already withdrawn, an empty reason, a `goal` or `spine` claim (withdraw the cover or the exclusion instead), a legacy cover record, and, without `--cascade`, a withdrawal that would un-hold other held claims (they are listed). The label stays taken: `submit` and `submit-batch` refuse it. |
| `restate --reason TEXT` | Binds an edited `campaign.json`. Every other command first checks that the statement's SHA-256 equals the bound one (set at `init`, or by the latest `restate`), parses those same bytes, and refuses otherwise. `restate` appends a versioned event carrying the old and new hashes and the reason. A merge requires both branches to bind the same statement. |
| `status` | Starts with one line per matroid giving χ(M), built only from held claims ("fully held", or what is still unknown). Then it lists held, open, refused and withdrawn claims, with earned-but-unclaimed reach. A withdrawn row gives its time and reason; a claim resting on one reads `not held: rests on withdrawn X`. |
| `explain <label>` | Shows the licence tree: certificates, rules, premises, reach and named premises. Each certificate names its `stored receipt` (the SHA-256 of `receipts/<sha256>.json`, or of an inline receipt's canonical JSON) and, when it differs, the `submitted file`'s. On a cover, it shows the candidates, each one's exclusion and its state, the premises and the theorems. |
| `frontier` | Lists open claims (withdrawn claims are left out), each with its last refusal and smallest fix, then any DECIDE goal with OPEN cover premises, missing candidate exclusions and held claims or covers that do not count for its parameters. It uses the same bridges and spine join as `status`; an undecided goal stays open. "Frontier empty" requires every claim held and, when present, the goal decided. |
| `tailings --export [FILE]` | Exports refused attempts, earned widenings, open items, open premises and withdrawn claims (source, reliability, completeness). |
| `emit-lean <label>` | Emits a Lean theorem for a held claim inside the warrant generator's coverage. Otherwise it says why not. |
| `merge <other-campaign-dir>` | Lands the other branch's new records in this ledger, only if the merged log still folds. See [Branches and merges](#branches-and-merges). |

Every refusal states what was refused, the rule, the scope, and the smallest fix. A failed replay names its cause: the equation or guard that fails at a point, a residual term of an identity, or a coefficient. The exit code is 1 on a refusal.

## Claims

- **`--matroid M`** takes a matroid *name*: one listed in `campaign.json`, or one you added as `matroids/M.json`. It is not a path. It encodes M with `tools/encode-matroid.py`. The system has one column per element, with the first frame fixed. Non-bases give equations and bases give guards (`nonzero`). The claim binds the encoding digest and carries the named premise `ENCODING-FRAME`. The premise is proved in Lean (`GPBinding.Matroid.frame_iff`). `gp` shows it as discharged when the Lean encoder re-derives the claim's system exactly, and OPEN otherwise. Guards are numbered in the encoder's order, starting at 0.
- **`--system FILE`** takes `{"variables": [...], "equations": [...], "nonzero": [...]}` directly.
- **Zero guards are refused.** A guard whose canonical form over ℚ is the zero polynomial (`0`, or `(x+1)^2 - x^2 - 2*x - 1`) holds nowhere. `claim` refuses it under the rule `nonzero guards` and names the guard's index. This applies to every kind and scope, and to a cover's branches. `submit` refuses a receipt for a claim filed with one before this check. A nonzero constant guard is allowed. Subtler vacuity is not detected; see [LIMITS.md](../LIMITS.md).
- **Kinds**, read in every field of the scope's characteristics:
  - `EMPTY`: no point.
  - `NONEMPTY`: a point in every such field, so it needs a point over the prime field or ℚ.
  - `NOT_IN_IDEAL` with target `1`: geometric nonemptiness. There is a point in every algebraically closed field of the scope, or equivalently over the algebraic closure, since ACF_p is complete. The Comparator challenges state the first form.
  - `IN_IDEAL` and `VANISHES_ON` take `--target`.
- **For a matroid,** p ∈ χ(M) is `NOT_IN_IDEAL --target 1 --char p`, and p ∉ χ(M) is `EMPTY --char p`.
- **Scopes:**
  - `--char p` is one characteristic.
  - `--char0` is characteristic 0.
  - `--outside 2,3` is characteristic 0 and every prime except those listed. `--outside ""` is every characteristic.

## Receipts

A receipt holds exactly one certificate or one rule:

```json
{"certificate": {...}}
{"rule": {...}, "premises": ["label", ...]}
```

Add `"characteristic": p` to any certificate to replay it mod p. The rational identity's residual must then vanish mod p, and the certificate holds at {p}. If the same data also replays over ℚ, GP earns the wider ℚ reach as well and reports it as "earned, unclaimed".

Every number is exact: an integer or a fraction written `"p/q"`. Decimals are refused. Without it the certificate replays over ℚ, and its reach is characteristic 0 plus every prime that avoids its denominators, and its guard values for points.

| `type` | Fields | Certifies |
|---|---|---|
| `ideal` | `cofactors` (one per equation), `m`, `k`, optional `guards` (indices) | Σ qᵢ·eqᵢ = h^m·(∏ selected guards)^k. EMPTY uses m = 0 and h = 1; IN_IDEAL uses m = 1; VANISHES_ON uses m ≥ 1. Without `guards`, every guard is used. |
| `point` | `point`: `{"x1": "3/2", ...}` | NONEMPTY. Every equation is zero and every guard is nonzero (a unit mod p). |
| `proper_coefficient` | `monomial`, e.g. `"a"` | NOT_IN_IDEAL(1) of a single equation with no guards. The equation has a nonzero coefficient, a unit mod p, at that non-constant monomial. |

Rules (`premises` are claim labels, filed and held first):

| `type` | Fields | Moves |
|---|---|---|
| `map` | `map`: `{"target var": "poly in source vars"}`, `eq_certificates`, `guard_certificates` | R3. NONEMPTY and NOT_IN_IDEAL(1) move source → target; EMPTY and VANISHES_ON move target → source. The obligations are `ideal` certificates on the source system, in the target's order. For each target equation *e*: VANISHES_ON(*e*∘map), with one cofactor per source equation and `m` ≥ 1. For each target guard *g*: EMPTY of the source with *g*∘map added as a last equation, with cofactors for the source equations and then one for *g*∘map, `m` = 0, and `k` for the source guards (0 if there are none). |
| `inclusion` | `eq_certificates`, `guard_certificates` | R2. The locus of one system lies inside another's. |
| `bridge` | none | NONEMPTY gives NOT_IN_IDEAL(1) on the same system. |
| `r1`, `split` (`on`), `cover` | as named | R1 and the R4 split and cover. |

A point over F_p[a]/(m) works in three steps:
1. Hold `NOT_IN_IDEAL --target 1 --char p` on `{m(a) = 0}` by `proper_coefficient`.
2. Move it to the target system with `map`, sending each variable to its coordinate polynomial in `a`, with mod-p obligation certificates.
3. Do not stop at NONEMPTY. An F_4 point is not a point of F_2.

## Branches and merges

A branch is a copy of the campaign directory. Work on each copy with `gp` as usual, then run `gp --campaign A merge B` to bring B's records into A. B is never written.

- **Keys are branch-safe.** A new claim's key is a hash of its label and statement, mapped into [2³², 2³² + 2⁵²). Two branches never give one key to different claims, barring a hash collision, which the guard refuses like any tie. The same claim filed on both branches gets one key and is merged as one record. Keys filed before this scheme stay as filed.
- **The guard.** The merged ledger is A's records, then each of B's that A lacks. Records equal except for their timestamp count as one. The merge lands only if the Kernel's `resolve` accepts the merged log of each runner: the characteristic claims (`gp_ledger --guard`) and the ℝ, ℚ, semireal, number-field and goal claims with the claims they rest on (`gp_ledger3 --guard`). Every key is in one part, and conflicts are per claim and warrant id, so the two checks see every collision. If either refuses, `gp` refuses with the Kernel's reason, and neither ledger changes.
- **Conflicts.** Resolve them on one branch, then merge again:
  - `conflicting current bindings: k`: one key bound to different statements or scopes.
  - `conflicting warrant contents: k`: one claim supported differently on the two branches, where neither branch has seen the other's support. Submit one receipt on both branches; the later support wins.
  - `withdrawal and replacement: k`: one branch retracts a warrant the other supersedes.
  - The adapter also refuses one label naming different claims, and two different receipts for one claim (`conflicting warrant contents: k (the branches support … by different receipts)`): receipts are named per claim, so their Kernel warrants are equal.
- **Withdrawals** (`withdraw` records) are joined by content like any record. A withdrawal persists in the merged event set, so it beats a support filed on the other branch, and both merge orders give the same state. `merge` lists the claims withdrawn on the other branch and any claim here that is no longer held. A `withdraw` record must name a claim of the merged ledger.
- **Raw retraction and supersession** are Kernel events that `gp` does not write: withdrawal is the profile's only lifecycle operation, sent to the runners as withdrawn keys. The guard reads `retract` and `supersede` ledger records, but a merge that would land one is refused.

## 3b claims

3b claims are about one field rather than a characteristic: ℝ, ℚ itself, or every semireal field (a field where −1 is not a sum of squares). Number-field points are 3b claims too. `gp_ledger3` decides them through the 3b profile (`Plan3.run`); see [3B-PROFILE-DESIGN.md](3B-PROFILE-DESIGN.md).

One ledger can mix 3a and 3b claims. A claim goes to `gp_ledger3` when:
- its statement is 3b;
- its support is a 3b certificate or rule;
- or its rule rests on a claim that went there.

The 3a claims such a rule uses are replayed there too. Every other claim is decided as before.

### Filing

| Scope flag | Meaning |
|---|---|
| `--real` | the field ℝ |
| `--semireal` | every semireal field (so ℝ and ℚ too) |
| `--rat-field` | the field ℚ itself |

A system file for these scopes may add sign conditions: `"signs": [["x - 1", ">0"], ["y", "<0"], ["z", "=0"]]`. A sign may also be written `1`, `-1` or `0`.

| Claim | Kinds and scopes | Reads |
|---|---|---|
| `--system F` without signs | `EMPTY` at any of the three; `NONEMPTY` only with `--real` | "no point over ℝ / over ℚ / in any semireal field with …"; "has a point over ℝ with …" |
| `--system F` with signs | `EMPTY` or `NONEMPTY`, `--real` only | the same, with the sign conditions |
| `--system F --kind COVER --real` | the file adds `"branches": [{"equations", "nonzero", "signs"}, ...]` | "every point over ℝ with … satisfies one of its branches" |
| `--nf F --kind NONEMPTY --char0` | F is `{"symbol": "t", "minimal_polynomial": "t^2 - 2", "variables", "equations", "nonzero", "point": {"x": "t", ...}}` | "m is irreducible over ℚ and, at every root t of m in a field of characteristic 0, the point satisfies …" |
| a 3a `NOT_IN_IDEAL --target 1 --char0` claim | filed as in 3a | "has a point over an algebraically closed field of characteristic 0 (over ℂ, for instance)" |

GP refuses a claim at filing when:
- the file does not parse (an undeclared variable, a decimal, a sign other than −1, 0 or 1);
- it asks for a point in every semireal field, or over ℚ alone. No evidence gives either. A rational point is the 3a claim `NONEMPTY --char0`.

`--matroid` stays 3a-only.

### Receipts

Numbers are exact, as in 3a. Polynomials in a point are written in the certificate's `symbol`.

| `type` | Fields | Proves |
|---|---|---|
| `real_point` | `symbol`, `polynomial` m, `interval` [lo, hi] isolating one root θ of m, `point` {var: polynomial in θ}. With no `polynomial`, `point` is rational. | NONEMPTY over ℝ. Each condition is decided exactly at θ: equations are 0, guards ≠ 0, sign conditions hold. |
| `sos` | `cofactors` (one per equation), `squares` (`"p"` or `["w", "p"]`, w ≥ 0), optional `gram` [{`monomials`, `matrix`}], `guard_power` k, optional `guards` | EMPTY in every semireal field, or over ℝ. The identity (∏guards)^(2k) + Σ w·p² + Σ cofactor·equation = 0 must hold exactly. No sign conditions. |
| `ordered` | `cofactors` (equations, then `=0` sign conditions), `positive_powers` (one per strict sign condition), `guard_power`, `cone` [{`atoms`: strict-condition indices, `squares` or `gram`}], optional `guards` | EMPTY over ℝ with sign conditions (Positivstellensatz) |
| `case_tree` | `points` (`[x, y]` per vertex), `tree`; optional `cited` | EMPTY over ℝ. Nodes are below. |
| `rational_root` | none | EMPTY over ℚ: one variable, and an integer equation with no rational root |
| `root_cover` | `interval` [lo, hi]; optional `point` as in `real_point` | COVER: the interval isolates the parent's root (Descartes), and one branch holds there |
| `alg_point` | `symbol`, `polynomial` m, `point` {var: polynomial}, optional `bezout` [[a, b], ...] (GP searches for the pairs if omitted) | NOT_IN_IDEAL(1) at characteristic 0, the complex relaxation. The equations vanish mod m and every guard is coprime to m. |
| `nf` | optional `gcd_degrees` | the number-field point. Irreducibility is checked by the rational-root test, degree 2 or 3. |

**Selected guards.** `guards` on `sos` and `ordered` (and on an ordered case-tree leaf) lists guard indices, numbered from 0 in the claim's `nonzero` order. Write an entry as `i`, or as `[i, e]` for `e` copies (gᵢ^e, e ≤ 64). Then ∏guards is the product of the selected guards only. Each is nonzero on the locus, so the refutation stays sound (`selectGuards_sub`). Without `guards`, every guard is used. In a case tree, the indices count the branch's guards: the system's, then the `nonzero` splits on the path.

**Case-tree nodes.** A rhombus is `[w, [a, b, c, d]]`, a weighted 4-cycle. GP cites its four edge equations and both diagonal guards, unless `cited` is true. Then write `[w, [a, b, c, d], [eab, ebc, ecd, eda], [gac, gbd]]`.

| Node | Fields | Checks |
|---|---|---|
| `{"collision": {...}}` | `rhombi`, `pair` [u, v] | L1a leaf. The weighted relations sum to p_u − p_v, and the guard \|p_u − p_v\|² is cited. |
| `{"unit": {...}, "then": node}` | `rhombi`, `pair` [u, v], `via` [a, b], `sign` ±1 (default 1); `edge` when `cited` | L1b step. The weighted relations sum to (p_u − p_v) − sign·(p_a − p_b), and (a, b) is an edge of the branch. The child is checked with \|p_u − p_v\|² − 1 = 0 added as the branch's last equation. Steps chain (`unitOk_real`). |
| `{"ordered": {...}}` | as the `ordered` receipt | leaf over the branch system |
| `{"split": "zero", "poly": p, "zero": node, "nonzero": node}` | | p = 0 joins the equations; p ≠ 0 joins the guards |
| `{"split": "sign", "poly": p, "neg": node, "zero": node, "pos": node}` | | the three signs of p |

| Rule | `premises` | Moves |
|---|---|---|
| `{"type": "narrow"}` | one claim of the same system and kind at a wider scope | every semireal field → ℝ or ℚ. Nothing narrows from a characteristic scope (ℂ) into ℝ. |
| `{"type": "k1a"}` | a held 3a EMPTY claim at a scope containing characteristic 0 | EMPTY in every semireal field (or ℝ, ℚ) on the same system |
| `{"type": "k1b"}` | a held 3a NONEMPTY claim (a rational point) at such a scope | NONEMPTY over ℝ on the same system. A complex point (NOT_IN_IDEAL(1)) never gives a real one. |

3a rules (map, inclusion, bridge, …) still act on 3a claims, including claims held by `alg_point`. They never take 3b premises.

Example: √2 over ℝ, with `sqrt2.json` = `{"variables": ["x"], "equations": ["x^2 - 2"], "signs": [["x", ">0"]]}` and `r.json` = `{"certificate": {"type": "real_point", "symbol": "w", "polynomial": "w^2 - 2", "interval": ["1", "2"], "point": {"x": "w"}}}`:

```
python tools/gp.py --campaign C claim sqrt2 --system sqrt2.json --kind NONEMPTY --real
python tools/gp.py --campaign C submit sqrt2 r.json
```

### Named OPEN premises and the DECIDE goal

`--premise NAME[=data]` attaches a named premise. Each one stays OPEN: no checker for it is admitted.

| Name | Asserts |
|---|---|
| `KUMMER-INDEPENDENCE=2,3,...` | The square classes of these rationals are independent in ℚ*/ℚ*². |
| `AMP-THM1` | u(n) for n ≤ 21 and the extremal-graph lists are as in Alexeev–Mixon–Parshall, Theorem 1. Minimum-degree bounds are derived from it, not assumed. |
| `GP74-NON-UD[=names]` | The named graphs among Globus–Parshall's 74 are not unit-distance graphs. Each can be discharged by its own EMPTY-over-ℝ claim. |
| `ENUM-COMPLETE[=manifest-sha256]` | The enumeration with this manifest lists every candidate graph. |
| `ENCODING-FRAME` | Comes with `--matroid` (the 3a frame) and `--udg` (`GPBinding.UDG.udg_frame_iff`). Discharged when the Lean encoder re-derives the claim's system. On a `--system` claim it stays OPEN. |

A claim held by a rule from a premised claim carries that claim's OPEN premises:
- `status` adds "(modulo …)";
- `explain` prints the premise and a "conditional:" line.

A campaign statement may declare a DECIDE goal in `campaign.json`. Its `udg` parameters give the goal its
meaning: Q(n, m) := ∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P.

```json
"goal": {"kind": "DECIDE", "name": "Q22", "statement": "...", "negation": "u(22) ≤ 60", "udg": {"n": 22, "m": 61},
         "readings": ["distinct points", "unordered pairs", "Euclidean distance exactly 1", "extra unit distances allowed"]}
```

`status` then opens with:
- the goal and its readings;
- each side: held, conditional, open or not held;
- the verdict.

A goal without `udg` parameters is never decided. See the next section for how each side is held.

### Graph-bound claims and the spine rule

`--udg GRAPH` files a claim on a graph's unit-distance system. GRAPH is a graph6 string, or a file with one graph6
line or JSON `{"n": 4, "edges": [[0, 1], ...]}`. `tools/encode-udg.py` encodes it. With `--gauge`, the first edge
is pinned at (0, 0) and (1, 0).
- It is a 3b claim: `--kind EMPTY` or `NONEMPTY`, at `--real` (also `--semireal` or `--rat-field` for EMPTY).
  `--udg` cannot be combined with `--system`, `--matroid` or `--nf`.
- The claim records `udg: {n, edges, gauge, sha256}`, with the edges canonical (i < j, sorted). `sha256` is the
  digest of `{"edges", "n"}`, and the claim's input is `udg:<sha256>`.
- It carries `ENCODING-FRAME`. `gp_ledger3` re-derives the system with the Lean encoder (`GPProfile.UDG`). The
  premise is discharged when the two are equal. Filing refuses a graph whose two encodings differ.

**Q** is held by a claim filed `--goal yes` when:
- it is a `--udg` NONEMPTY claim over ℝ, and it is held;
- its frame is equal;
- its graph has the goal's n vertices and at least its m edges;
- it rests on no OPEN premise.

The theorems are `udg_frame_iff` and `realize_sound`, composed as `udg_realize`. Filing refuses `--goal yes` on a
`--system` claim, and on a graph with the wrong n or too few edges.

**Not Q** is never held by a claim. Filing refuses `--goal no` everywhere. Instead, `gp cover` records a cover:
- the candidate graphs, each canonical with its SHA-256;
- N and M;
- the named premises it rests on: `ENUM-COMPLETE[=manifest-sha256]`, `AMP-THM1`, `GP74-NON-UD[=names]`;
- `supports`: labels of claims that back its argument. They are shown in views and not used by the rule.

Its meaning is `CoverComplete N M L`. A cover needs a completeness warrant. Either it names a premise, or it lists every
labelled graph on N vertices with at least M edges (`exhaustive`, `coverComplete_of_all`; checked only up to
100,000 graphs). Otherwise filing refuses it.

`status` shows not Q as:
- **held** when some cover for the goal's (n, m) has no OPEN premise and every candidate is excluded;
- **conditional on …** when every candidate is excluded but the cover names OPEN premises;
- **open** otherwise, listing the candidates without an exclusion.

A candidate is excluded by a held `--udg` EMPTY claim over ℝ on the identical labelled graph, with its frame equal.
Its own OPEN premises carry over. The theorems are `spine_sound`, `candidate_isEmpty` and `udg_frame_iff`.

These do not count:
- an exclusion held only in every semireal field (narrow it to ℝ with rule `narrow`);
- an exclusion at characteristic 0, or on a `--system` claim;
- an exclusion on a relabelled copy of the graph;
- a cover for another (n, m).

The join that applies these rules is trusted Python; see `TCB.md`. It matches candidates to exclusions and compares
n, m and edge counts.

Exclusion systems must not carry "non-edge ≠ 1" guards. Extra unit distances are allowed, so excluding only faithful embeddings is unsound for NONE.

## Lane P campaigns (0.52)

A campaign whose `campaign.json` says `"profile": "P"` takes these commands (`tools/gp_lanep.py`); others are refused there, and the P commands are refused elsewhere. See [USING-GP](USING-GP.md#lean-proposition-claims-lane-p-052).

| Command | Does |
|---|---|
| `register <Decl> [--as NAME]` | Binds a code to a campaign-local `def X : Prop`: its closure hash (SHA-256 over the canonical serialisation of every campaign-local constant it uses) and the environment stamp. `--prose TEXT --as NAME` registers a prose statement (a text hash, never holdable). |
| `claim <label> (--lean X \| --prose X) [--premise H]... [--theorem T \| --from L]` | Files a claim of `X` (or `¬X`) under premises `H`. `--theorem T` is a `lean_theorem` warrant: the binder adds `H₁ → … → Hₙ → X := T` to the Lean kernel and audits `T`'s axioms. `--from L` weakens `L` (Kernel narrowing). |
| `discharge <label> --premise H --by L2 [--as NEW]` | Files the claim `(s, S)` derived from `<label>` = `(s, S ∪ {H})` and `L2` = `(H, T)`, `T ⊆ S`. Refused on a statement mismatch (a code mismatch) or when `L2` has premises the result would drop. Not held while `L2` is not. |
| `submit <label> --hand-proof F --state complete\|sketch [--condition H]...` | A recorded-only warrant (also `--script F`, `--numerical F`, `--external F --tier N`): file locator and SHA-256. It never holds; a reviewer's condition is an OPEN premise. |
| `fidelity <X> --level L --by WHO --ref REF` | unaudited < LLM-audited < human-audited < anchored, attached to the code; "anchored" shows as asserted. |
| `present <label> --venue V --tag TAG [--premise H]...` | A presentation (tags `COMPARATOR`, `LEAN`, `REPLAY`, `CERT`, `SCRIPT`, `HAND`, `NUMERICAL`, `PROBE`, `CONJECTURE`, `OPEN`). |
| `bind [--replay]` | Builds the package and runs the binder; prints each code's freshness and each theorem's verdict. `--replay` (lean4checker) is phase P2. |
| `status`, `explain <label>`, `frontier` | Per claim: held or open (or unbound, naming the changed constant), the tier (`tier 2 (unreplayed)`) or the best recorded tier, the OPEN premises, presentations (OVERSTATED) and the lowest fidelity. `explain` draws the warrant path and marks its weakest step; `frontier` ranks OPEN premises by the claims they would unlock. |
| `withdraw <label> --reason TEXT [--cascade]`, `merge <dir>` | As for 3a/3b claims; a P withdrawal retracts all of the claim's warrant slots. |

New `gp-ledger/v1` ops: `register`, `pclaim`, `discharge`, `pwarrant`, `fidelity`, `present`, `bind`, `pwithdraw` (and `pattempt` for a build timeout). Bind reports are stored as `receipts/<sha256>.json`, checked on every read.

## Logs

Keep `cost-log.jsonl` and `friction-log.jsonl` in the campaign directory, following `campaigns/schemas/`. Classify every refusal as `useful`, `false` or `ergonomic`. Check them with `python tools/check-campaign-logs.py campaigns/3p-matroids`.

## Roles

Search tools such as Singular, Macaulay2 and Sage are untrusted. GP replays everything they propose. The ledger is written only by `gp`. The builder fixes CLI and checker problems you report and never writes campaign claims.

### Runner freshness

`gp` rebuilds a Lean runner (`gp_ledger`, `gp_ledger3`) unless the stamp next to it (`<runner>.gpstamp`) records the SHA-256 identity of the sources it was built from: the profile and Kernel `.lean` files, their lakefiles, the manifest and the toolchain pin. Modification times play no part. A build is announced on stderr; a failed build is refused with the target and the last lines of lake's output, and a missing toolchain with the elan install hint.
