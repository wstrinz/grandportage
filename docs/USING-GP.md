# Using GP on your own problem

From a clone to a campaign of your own, in any directory. Guarantees: [GUARANTEES.md](../GUARANTEES.md); limits: [LIMITS.md](../LIMITS.md); every command: [GP-CLI.md](GP-CLI.md).

## Install

You need [elan](https://github.com/leanprover/elan), Python 3.10 or later, and a C compiler named `cc` on `PATH`. Hex v0.9 compiles a little C code (`HexModArith`, `HexArith`) into the runners. Linux and macOS have one. On Windows, a small `cc` that forwards to the toolchain's own `leanc` (clang) works, given mingw-w64 (msvcrt) C headers, since Lean ships none. `gp` uses only the standard library; the log checker needs `jsonschema` (`pip install -r requirements-dev.txt`).

```bash
git clone https://github.com/wstrinz/grandportage.git
cd grandportage/profile
lake build gp_ledger gp_ledger3   # elan installs the pinned toolchain first
```

`gp` decides every status with two Lean runners in `profile/.lake/build/bin/`, `gp_ledger` and `gp_ledger3`. It builds a missing or stale runner on first use, once the pinned toolchain is installed (hence the `lake build` above). The profile and both runners took about 30 minutes on a busy Windows machine under Lean `v4.35.0-rc3` with Hex v0.9.0; a fresh clone also compiles Hex and its C code.

A stamp beside each runner (`<runner>.gpstamp`) records the SHA-256 identity of its sources (profile and Kernel `.lean` files, lakefiles, manifest, toolchain pin); a mismatch means a rebuild. A runner built by `lake` alone has no stamp, so the first `gp` command reruns `lake build` (a no-op) and writes it.

## Concepts in one screen

- **Campaign:** a directory holding `campaign.json` (your statement) and `ledger.jsonl`, written only by `gp`. `init` binds the statement's SHA-256, and every command checks it.
- **Claim:** a polynomial **system** (variables, equations, `nonzero` guards and, over ℝ, sign conditions), a **kind** (`EMPTY`, `NONEMPTY`, `NOT_IN_IDEAL --target 1`, `IN_IDEAL`, `VANISHES_ON`, `COVER`) and a **scope**: characteristics (`--char p`, `--char0`, `--outside p,q`) or one field (`--real`, `--rat-field`, or `--semireal` for every field where −1 is not a sum of squares).
- **Evidence:** a receipt holds one **certificate** (an ideal identity, a point, a sum of squares, a real root in an interval, …) or one **rule** (map, inclusion, bridge, narrow, …) whose premises are held claims. GP replays it exactly; its producer (your CAS, say) is not trusted.
- **Held, open, refused:** a claim is **held** when the Kernel fold over the whole ledger reaches a warrant for it, **open** until then, and **refused** when its last attempt failed, with the rule, the scope and the smallest fix.
- **Reach:** a certificate holds a claim only where its arithmetic is valid; one that divides by 2 does not reach characteristic 2. Wider reach than claimed is reported as "earned, unclaimed".
- **Named OPEN premises** (`--premise NAME`) are metadata: `gp` prints them ("modulo …"), and the Kernel neither sees nor checks them. The names form a fixed list ([GP-CLI](GP-CLI.md)); a hypothesis of your own cannot be filed as a premise yet, so carry it as a named hypothesis in Lean.
- **Identities:** a polynomial identity f = 0 is `IN_IDEAL --target f` on a system with no equations. A long target can come from a file (`--target @FILE`).
- **What GP cannot state:** a claim must be a polynomial system with a kind and a scope. Determinants, matrix positivity, cones, reachability and other for-all statements are outside GP 0.50, as are matroids other than simple rank-3 ones given by their lines. The census profile in [GUARANTEES](../GUARANTEES.md) has no `gp` command; it runs from its own package.
- **Belay and rope:** GP is a **belay**, keeping your own work honest; trusting a held claim means trusting GP's [TCB](../TCB.md). A **rope** is a Lean theorem in Mathlib vocabulary that stock Comparator checks, with no trust in GP.

## A worked example, end to end

Copy the inputs outside the repository and define `gp`:

```bash
cp -r ~/grandportage/docs/examples/using-gp ~/gp-demo && cd ~/gp-demo
gp() { python ~/grandportage/tools/gp.py "$@"; }
# PowerShell: function gp { python $HOME\grandportage\tools\gp.py @args }
```

Blocks are captured output, replayed by `tests/test_gp50_using_gp_example.py`; `...` elides.

### 1–2. The statement, and `init`

`campaign.json` is free-form JSON; `gp` reads only `family` (matroids, for `--matroid` claims) and a DECIDE `goal`.

**Matroid records.** `--matroid NAME` takes a simple rank-3 matroid given by its lines. It is listed under `"family"` in `campaign.json`, or kept as `matroids/NAME.json` with a cited `"source"`:
```json
{"name": "F7", "source": "...", "elements": ["1", "2", "3", "4", "5", "6", "7"],
 "lines": [["1", "2", "4"], ["2", "3", "5"], ["3", "4", "6"], ["4", "5", "7"], ["1", "5", "6"], ["2", "6", "7"], ["1", "3", "7"]]}
```
Only `name`, `elements`, `lines`, `source` and `answer_key` are read; any other key is refused, so a record is never filed as a different matroid. `"lines": []` is the uniform matroid U(3, n). State matroids of other ranks, or ones given by a matrix, as `--system` claims.

```console
$ mkdir demo
$ cp campaign.json demo/campaign.json
$ gp --campaign demo init
ledger started for demo/campaign.json
```

### 3. An algebraic claim, its certificate and its reach

`two-points.json` is x − 1 = 0, x + 1 = 0. Over ℚ it has no point: (−½)(x − 1) + (½)(x + 1) = 1. The receipt `empty-q.json` is that identity (an `ideal` certificate with cofactors −½, ½).

```console
$ gp --campaign demo claim distinct-q --system two-points.json --kind EMPTY --char0
claim distinct-q (key 758474246705632) filed: EMPTY at characteristic 0; open
$ gp --campaign demo submit distinct-q empty-q.json
held: distinct-q at characteristic 0; earned, unclaimed: 0 and every prime except {2}
```

Dividing by 2, the certificate reaches characteristic 0 and every odd prime, not 2.

### 4. A real claim

`sqrt2.json` is x² − 2 = 0 with x > 0; the receipt `sqrt2-real.json` names the root of w² − 2 in [1, 2].

```console
$ gp --campaign demo claim sqrt2 --system sqrt2.json --kind NONEMPTY --real
claim sqrt2 (key 514878146214670) filed: NONEMPTY at the field ℝ; open
$ gp --campaign demo submit sqrt2 sqrt2-real.json
held: sqrt2 at the field ℝ
```

### 5. A refusal, and its smallest fix

The same certificate, for every characteristic:

```console
$ gp --campaign demo claim distinct-all --system two-points.json --kind EMPTY --outside ""
claim distinct-all (key 2494852848739499) filed: EMPTY at characteristic 0 and every prime; open
$ gp --campaign demo submit distinct-all empty-q.json
refused: the certificate reaches 0 and every prime except {2}, which does not cover the requested characteristic 0 and every prime [rule: receipt: computed reach; scope: characteristic 0 and every prime]; smallest fix: narrow the claim to the computed reach, or certify the excluded characteristics separately (for example mod p)
```

Rightly so: in characteristic 2 the two equations coincide, and x = 1 is a point (step 9). A claim's scope is fixed at filing, so the fix is a new claim at the computed reach:

```console
$ gp --campaign demo claim distinct-odd --system two-points.json --kind EMPTY --outside 2
claim distinct-odd (key 355403490935505) filed: EMPTY at characteristic 0 and every prime except {2}; open
$ gp --campaign demo submit distinct-odd empty-q.json
held: distinct-odd at characteristic 0 and every prime except {2}
```

### 6. `status`, `frontier` and `explain`

```console
$ gp --campaign demo status
held     distinct-q                   EMPTY        characteristic 0; earned, unclaimed: 0 and every prime except {2}
held     sqrt2                        NONEMPTY     the field ℝ
refused  distinct-all                 EMPTY        characteristic 0 and every prime
held     distinct-odd                 EMPTY        characteristic 0 and every prime except {2}

Real and number-field claims (held claims only):
  has a point over ℝ with x^2 - 2 = 0, x > 0 (sqrt2)
$ gp --campaign demo frontier
distinct-all: refused: the certificate reaches 0 and every prime except {2}, ...
$ gp --campaign demo explain distinct-q
distinct-q: EMPTY at characteristic 0: held
  by ideal certificate (stored receipt a6cbc6d3c9e7, submitted file 3eb4beb2e655), reach 0 and every prime except {2}
```

A refused claim stays on the frontier until you withdraw it (GP 0.51):

```console
$ gp --campaign demo withdraw distinct-all --reason "superseded by distinct-odd"
withdrawn: distinct-all (key 2494852848739499): superseded by distinct-odd; was not held
  note: readers older than 0.51 will not see this withdrawal: an older gp skips the record and shows the claim, and what rests on it, as held again
```

A withdrawal is permanent and claim-level. On every fold both runners retract the claim's support and theorem warrants, so the claim, and every claim whose only derivations pass through it, stop being held; nothing else changes (`GPProfile.Withdraw`: W1 `withdraw_antitone`, W2 `withdraw_resolves`, W3 `withdraw_unholds`). `withdraw` prints what it no longer holds and any change in the goal verdict. It is refused for an unknown label, a claim already withdrawn, an empty reason, a `goal` or `spine` claim (withdraw the cover or the exclusion instead) and a legacy cover record, and, unless you pass `--cascade`, when other held claims would lose their hold (they are listed). The label stays taken: `submit` refuses it, so file the corrected claim under a new label. `status` shows a `withdrawn` row with its time and reason, and a claim resting on it reads `not held: rests on withdrawn …`; `frontier` leaves withdrawn claims out, and `tailings` lists them.

### 7. Receipts by reference

A held receipt is stored once, as canonical JSON in `receipts/<sha256>.json`:

```console
$ ls demo/receipts
196014a796395c76a1a0b36fdd5850861bcceee60b3e3c6a650b9ac1c8e0fd6d.json
a6cbc6d3c9e76b761855a0af45d01007fd4101541c944b4a9be56f31b7214d92.json
```

`distinct-q` and `distinct-odd` share the second. A support record stores its `receipt_ref` (path and SHA-256) and `receipt_sha256`, the hash of the file you submitted; `explain` prints both, as `stored receipt` (the name under `receipts/`) and `submitted file`. Every command checks each file against its hash before folding; an edited or missing file is refused.

### 8. Restating the statement

After an edit, every command refuses until `restate` records the change as a versioned ledger event:

```console
$ cp campaign-v2.json demo/campaign.json
$ gp --campaign demo status
refused: the campaign statement changed since it was bound (bound 39b5f17da0cd, now d88fb7348534) ...
$ gp --campaign demo restate --reason "the statement mentions the branch"
statement restated (version 2): 39b5f17da0cd -> d88fb7348534
```

### 9. Two branches and a merge

A branch is a copy of the campaign directory. `merge` lands the other branch's new records only if the merged ledger folds; it never writes the other branch.

```console
$ cp -r demo demo-b
$ gp --campaign demo-b claim meet-2 --system two-points.json --kind NONEMPTY --char 2
claim meet-2 (key 3686418560549559) filed: NONEMPTY at characteristic 2; open
$ gp --campaign demo-b submit meet-2 point-mod2.json
held: meet-2 at characteristic 2
$ gp --campaign demo claim x2p1-real --system x2p1.json --kind EMPTY --real
claim x2p1-real (key 1609986680838869) filed: EMPTY at the field ℝ; open
$ gp --campaign demo submit x2p1-real x2p1-sos.json
held: x2p1-real at the field ℝ
$ gp --campaign demo merge demo-b
merged 2 records (1 claims, 1 supports, 0 refusals); the merged log folds
```

`meet-2` is the point x = 1 in characteristic 2. `x2p1-real` holds by the sum of squares 1 + x² − (x² + 1) = 0.

The guard is the Kernel's `resolve` over the merged log, for the characteristic claims (`gp_ledger --guard`) and for the ℝ, ℚ, semireal and number-field claims (`gp_ledger3 --guard`). One key filed for two different claims is refused as `conflicting current bindings`; one claim held by a certificate on one branch and by a rule on the other, as `conflicting warrant contents`. Two different certificates for one claim give equal Kernel warrants, so `gp` refuses them itself (`... by different receipts`). Submit one receipt on both branches, then merge again.

A withdrawal on one branch beats a support filed on the other, in either merge order; `merge` lists the claims withdrawn on the other branch and any claim here it no longer holds. Raw `retract` and `supersede` records are refused.

## DECIDE goals

A campaign may ask one yes-or-no question for GP to decide ([design](A2-GOAL-STATEMENT-DESIGN.md)). For unit distances, Q(n, m) asks: do some n points in the plane have at least m unit distances? `decide-45.json` asks it for n = 4, m = 5:

```json
"goal": {"kind": "DECIDE", "name": "Q45", "statement": "some 4 points in the plane have at least 5 unit distances",
         "negation": "u(4) < 5", "udg": {"n": 4, "m": 5}}
```

`gp` reads `udg` (n and m); the other fields are display text. `init` files two Kernel claims over ℝ: `goal:Q45` (Q) and `goal:not-Q45` (not Q). An older ledger gets them at its first `claim`, `submit` or `cover`. You never submit to them: after each filing command `gp` offers the goal rules the ledger supports, and the Kernel fold decides each one:
- **realize** holds Q from a held `--udg GRAPH --kind NONEMPTY --real --goal yes` claim on n vertices with at least m edges;
- **spine** holds a cover's spine ("if the cover is complete, not Q") from one held `--udg … --kind EMPTY --real` claim per candidate graph;
- **cover_all** holds a cover whose candidates are every labelled graph on n vertices with at least m edges (at most 100000);
- **decide** holds not Q from a cover and its spine, both held.

`--udg` takes a graph6 string, a file holding one, or JSON `{"n": 4, "edges": [[0, 1], ...]}`. `gp` writes the graph's unit-distance system: the vertices, numbered from 0, are the points (x1, y1), …, (xn, yn), with one equation per edge and every two points distinct. The Lean encoder re-derives it (ENCODING-FRAME discharged), or the claim is refused. `--gauge` pins the first edge at (0, 0), (1, 0).

### Q(4, 5) holds: a rhombus

`rhombus.json` is two unit triangles sharing an edge: 4 vertices, 5 edges. `rhombus-point.json` places it exactly, with y = w/2 for the root w = √3 of w² − 3 in [1, 2].

```console
$ mkdir q45
$ cp decide-45.json q45/campaign.json
$ gp --campaign q45 init
ledger started for q45/campaign.json
goal claim goal:Q45 filed: Q45 (n = 4, m = 5) over ℝ; open until the Kernel holds it
goal claim goal:not-Q45 filed: not Q45 (n = 4, m = 5) over ℝ; open until the Kernel holds it
$ gp --campaign q45 claim rhombus --udg rhombus.json --kind NONEMPTY --real --goal yes
claim rhombus (key 1384652741023809) filed: NONEMPTY at the field ℝ [graph rhombus (4 vertices, 5 edges, sha256 53bc24bdcd9c); ENCODING-FRAME: equal to the Lean encoder's]; open
goal: goal:Q45 not held (rule realize from rhombus): rule realize needs held premises; not held: rhombus
$ gp --campaign q45 submit rhombus rhombus-point.json
held: rhombus at the field ℝ
held: goal:Q45 at the field ℝ (rule realize from rhombus)
$ gp --campaign q45 status
Goal: DECIDE Q45 := some 4 points in the plane have at least 5 unit distances
  Q45: held by the Kernel (goal:Q45: rule realize from rhombus; GPBinding.Real.realizeRuleOk_sound: udg_frame_iff, realize_sound)
  not Q45 (u(4) < 5): not held
  verdict: decided: Q45
...
```

Filing `--goal yes` already offered rule realize, refused while `rhombus` was open; the submit offered it again.

### Q(4, 6) fails: a cover

`gp cover LABEL --candidates FILE --n N --m M` files two claims: the cover `LABEL` (every n-point set with at least m unit distances contains a unit-distance copy of a candidate) and its spine `LABEL:spine`. A cover filed with `--premise` (`ENUM-COMPLETE`, `AMP-THM1`, `GP74-NON-UD`) rests on that premise and stays open, since a named premise never holds a claim. Here `k4-only.json` lists K4 alone:

```console
$ mkdir q46
$ cp decide-46.json q46/campaign.json
$ gp --campaign q46 init
...
$ gp --campaign q46 cover k4-enum --candidates k4-only.json --n 4 --m 6 --premise ENUM-COMPLETE
cover k4-enum filed: 1 candidate for n = 4, m = 6 [premise ENUM-COMPLETE: OPEN]; spine k4-enum:spine filed
$ gp --campaign q46 frontier

Goal: DECIDE Q46
  Q46: not held
  not Q46: open by cover k4-enum
  cover k4-enum: premise ENUM-COMPLETE: OPEN
  cover k4-enum: missing held exclusion over R for K4 (4 vertices, 6 edges, sha256 cc6c3fb49378)
  verdict: undecided
  goal frontier remains open
```

K4 has no unit-distance embedding: `k4-tree.json` is a case tree with one collision leaf. Its two rhombi force the points of vertices 0 and 1 to coincide, which the system excludes. Once K4's exclusion is held, the Kernel holds the spine; the cover is still open:

```console
$ gp --campaign q46 claim k4 --udg k4.json --kind EMPTY --real
claim k4 (key 2681920875241445) filed: EMPTY at the field ℝ [graph K4 (4 vertices, 6 edges, sha256 cc6c3fb49378); ENCODING-FRAME: equal to the Lean encoder's]; open
$ gp --campaign q46 submit k4 k4-tree.json
held: k4 at the field ℝ
held: k4-enum:spine at the field ℝ (rule spine from k4)
$ gp --campaign q46 status
Goal: DECIDE Q46 := some 4 points in the plane have at least 6 unit distances
  Q46: not held
  not Q46 (u(4) < 6): open; the Kernel holds spine k4-enum:spine (if cover k4-enum is complete then not Q46); the cover is open, resting on the named premises ENUM-COMPLETE
  verdict: undecided
...
```

K4 is the only graph on 4 vertices with 6 edges, so the list is exhaustive. Filed without a premise, it is held by the Kernel's own check, and rule decide follows:

```console
$ gp --campaign q46 cover k4-only --candidates k4-only.json --n 4 --m 6
cover k4-only filed: 1 candidate for n = 4, m = 6; exhaustive; spine k4-only:spine filed
held: k4-only at the field ℝ (the exhaustive list)
held: k4-only:spine at the field ℝ (rule spine from k4)
held: goal:not-Q46 at the field ℝ (rule decide from k4-only:spine and k4-only)
$ gp --campaign q46 frontier

Goal: DECIDE Q46
  Q46: not held
  not Q46: held by cover k4-only (Kernel: goal:not-Q46, rule decide; GPBinding.Real.decideRuleOk_sound)
  cover k4-enum: alternative cover for the goal
  cover k4-enum: premise ENUM-COMPLETE: OPEN
  verdict: decided: not Q46
frontier empty: every claim is held and the goal is decided
```

`explain k4-only` prints the cover's completeness, its spine, each candidate's exclusion and the theorems behind each rule. A held goal claim that rests on a claim with an OPEN named premise is shown "modulo" that premise, and the verdict stays undecided.

## From a held claim to a rope

For readers who do not trust GP:
1. **`gp emit-lean <label>`** (or `--all`) prints Lean warrants for held characteristic-scoped claims by `ideal` EMPTY certificates over ℚ on integer systems, integer points, proper coefficients, or bridges from those; otherwise it says why not. They state `Warranted …` in the binding's vocabulary (build them against `binding/`), not Mathlib's.
2. **State the result in Mathlib vocabulary** (verbatim from formal-conjectures where it has one) and prove it in its own Lake package `ropes/<id>/`.
3. **Work through [ROPE-CHECKLIST.md](ROPE-CHECKLIST.md):** Comparator acceptance, controls refused for their expected reasons, named hypotheses, `FIDELITY.md`, `MANIFEST`, `REPRODUCE` and the tier. [`ropes/r1a`](../ropes/r1a/README.md) is a delivered rope.

**When GP holds only fragments.** If the decisive statement is outside what GP can state (see Concepts), GP holds the polynomial pieces and the rope carries the rest in Lean. Say in `FIDELITY.md` which parts GP held and which only Lean checks. `emit-lean` covers neither `IN_IDEAL` claims nor mod-p certificates, so those pieces are restated in the rope.

```console
$ gp --campaign demo emit-lean distinct-q
import GPBinding.Binder.Registry
...
theorem w_distinct_q :
    Warranted ⟨["x"], [p0, p1], [], .empty⟩
      ⟨true, .cofinite [2]⟩ := by
...
end GPBinding.Campaign
```

## Logs

Keep two JSON Lines logs in the campaign ([schemas](../campaigns/schemas)):
- `cost-log.jsonl`: per task, wall time, agent turns, tokens, catches, false refusals and near misses;
- `friction-log.jsonl`: every refusal, verbatim, classified `useful` (stopped a real error), `false` (refused a sound claim) or `ergonomic` (right refusal, unhelpful message).

`python <repo>/tools/check-campaign-logs.py <campaign-dir>` checks every entry against its schema, and that every friction entry names a cost-log task.

## Compatibility: `gp-ledger/v1`

- **Version:** `gp --version` prints the release (`gp 0.51.0`). `init` records it as `gp_version`, beside `"schema": "gp-ledger/v1"` and the statement's SHA-256.
- **The ledger** is append-only JSON Lines, written only by `gp`; each record has an `op` (`init`, `claim`, `support`, `refused`, `cover`, `restate`, `merge`, and since 0.51 `withdraw`) and a time `at`.
- **Within v1,** records may gain optional fields, new ops may appear, and profiles may add statement kinds, certificates and rules.
- **Old ledgers keep folding:** supports with an inline receipt (before receipt references), ledgers without `restate` (the `init` hash binds), `init` records without `gp_version`, and claim keys from the older counter scheme. A ledger with no `withdraw` record gives the runners the same input as 0.50 and gets byte-identical output. Tests: `test_gp50_receipt_ref.py`, `test_gp50_merge_guard.py`, `test_gp50_outside_repo.py`, `test_gp50_withdraw.py`.
- **Withdrawal and older readers (0.51).** `withdraw` is a v1 extension. **A `gp` older than 0.51 skips `withdraw` records, so it shows a withdrawn claim, and every claim resting on it, as held again.** That is still sound (W1: anything held after a withdrawal was held before), but it silently reverses the owner's decision. A v1 ledger cannot make an older `gp` refuse, so read a ledger with withdrawals only with gp 0.51 or newer; `withdraw` repeats this warning each time. The next schema version will let a ledger name its minimum reader.
- **Not promised:** stable view text. `gp` skips unknown ops, so read a ledger with a `gp` at least as new as its writer. Every command except `init` checks the init record's `schema` and refuses one it does not read (this release reads `gp-ledger/v1`); `merge` checks the other branch's too.
- **Breaking changes** get a new schema id, `gp-ledger/v2`, in new ledgers' `init` record: a new required field, a changed meaning for a field or op, or a different hash or key scheme.

## Troubleshooting

- **"building the GP runners (one-time, several minutes)…"** on stderr: `gp` is building a runner (after a source change it says "rebuilding"). Run `lake build gp_ledger gp_ledger3` in `profile/` to watch. A failed build is refused with the target's name and the last lines of lake's output; rerun the build by hand for Lean's full message. Without the pinned toolchain the refusal says to install elan.
- **"the campaign statement changed since it was bound":** restore `campaign.json`, or `gp restate --reason …`. A merge needs both branches to bind the same statement.
- **"no ledger here"** (exit 2): run `gp init` beside `campaign.json`.
- **"decimals are not exact numbers":** write integers or fractions `"p/q"`.
- **"a polynomial text does not parse (…)":** the text named (`equations[i]`, `nonzero[i]`, `signs[i]`, `target`) has a character, variable or bracket the parser does not read. A long target can come from a file: `--target @FILE`. A ledger holding such a claim from before this check marks it `unparsed` in `status` (not held), and the rest of the ledger folds as usual.
- **"guard i (…) is the zero polynomial":** the guard expands to 0, so the claim's conditions hold nowhere. Drop it or write the condition you meant. A claim filed with one before this check still folds as before, but `submit` refuses new receipts for it; file the corrected claim under a new label.
- **Windows:** either slash works in paths. `campaign.json` is bound by its bytes, so a line-ending conversion makes every command refuse until you restore or restate. Output is UTF-8 (ℝ, ℚ, χ).
- **Memory and time:** every command replays every receipt (no cache); the example takes about a second a command. Never run `decide +kernel` over the Hex checkers: it exhausts memory.
- **A refusal you think wrong:** log it as `false`, report it, and see [KNOWN-CONSERVATISM.md](../KNOWN-CONSERVATISM.md).
