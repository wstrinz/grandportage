# Phase 2.5 report

Authority: [post-G2 handoff](../docs/GP-0.50-POST-G2-HANDOFF.md) §2, amended by [Addendum A](../docs/GP-0.50-POST-G2-ADDENDUM-A.md) §2. No 3a profile code has landed.

## 2.5a Package split and pin

The 22 `Kernel` modules are AdmissionProofs, Closure, ClosureCompleteness, ClosureOrderProofs, ClosureProofs, Conflict, ConflictProofs, ConflictSoundnessProofs, Cover, CoverProofs, Decoder, Entry, EventOrderProofs, Events, LifecycleProofs, Narrowing, NarrowingAdmissionProofs, NarrowingProofs, ResolveProofs, Runtime, RuntimeProofs and Semantics.

`Stub` has 12 modules; `Run` has 6, including Queries and QueryDecoder per Will. `tests/test_gp50_kernel_pin.py` enforces that `Kernel` imports only `Kernel`.

Kernel-only D8 budget: logic 382/500, decoder 156/400, statement 34/80.

`KERNEL-PIN.json` holds per-file SHA-256, the toolchain `v4.34.0-rc2` and the parent commit. `PROMOTIONS.md` is the log for later changes.

## 2.5b Profile split

The split follows the handoff:
- `ProfileOps` is in `Type`, executable and Mathlib-free.
- `Profile.{u}` adds `Ctx : Type u`, `mem`, `Holds`, `le_sound` and `contra_sound`.
- Executable checks take `ProfileOps`; theorems take `Profile`.
- `Overlap` has `Code` and `witness`, and its soundness gives `∃ c, mem c a ∧ mem c b`.
- Harness profiles use `u = 0` through a `CoeOut` coercion.

Side effect: two 188-line point-independence proofs became `rfl`.

No native output field was renamed. The overlap code is reported under the existing `overlap_witness` key. One internal execution-count key's spelling was normalized, with identical values.

## Acceptance evidence at the final pins

| Check | Result |
|---|---|
| `leanchecker` on every Kernel module | 22/22 |
| Axiom audit of every Kernel constant (not a curated list) | 1,054 constants; only `propext`, `Quot.sound`, `Classical.choice`; 680 axiom-free ([receipt](PHASE-2.5-KERNEL-AXIOMS.json)) |
| 79 kernel cases, fresh driver | 79/79 rows identical to the pre-bump run |
| 22 native receipts (`tools/compare-native-outputs.py`) | 9 identical, 13 differ only in toolchain paths/hashes or refactored-source hashes, 0 behavioural |
| Legacy replay | 459 cases unchanged; 67 protected artifacts intact |
| Full suite, fresh at rc2 with the pin | 386 passed, 1,130 subtests, 0 failed |

## 2.5c Context spike

The spike is in `binding/GPBinding/ContextSpike.lean` (147 lines, standard axioms):
- **Scope:** the §3.2 characteristic-set scope (`char0` plus a finite or cofinite prime set), with a decidable `le`.
- **Soundness:** `le_sound` is proved. So is `contra_sound` for EMPTY versus NONEMPTY of one integer system.

Both candidate contexts work:
- `Theory.field.ModelType` works through `FirstOrder.Ring.compatibleRingOfRing` in one direction and `FirstOrder.Field.fieldOfModelField` in the other.
- The friction: the way back rebuilds the field with `Field.ofMinimalAxioms`, which uses a unary `Nat.cast` and a choice-based inverse. Characteristic agreement is therefore a theorem about two different instances. It is proved (`roundTrip_natCast`, `roundTrip_ringChar`, `roundTrip_mem`).

**Choice:** `Ctx := FieldCtx` (a carrier in `Type` with a `Field` instance). Profile proofs then use Mathlib's own instances, while the `ModelType` link stays available as proved bridge theorems.

**Open:** a full structure equivalence with `ModelType` is not proved. Only the scope-relevant facts (characteristic, membership) are. If 3a needs the model-theory side for more than scope, that equivalence is the first follow-up.

## 2.5d Pin alignment

Kernel, stub, profile and binding all use Lean `v4.34.0-rc2`. Binding uses Mathlib `85e3a25e`.
- The Kernel built unchanged. Pin hashes match the pre-bump sources.
- Both ModelTheory files are present at the new pin. API drift in the files GP uses is trivial; the spike was written directly at the new pin.

## 2.5e Dependency layout

| Package | Depends on |
|---|---|
| `phase2/lean` (Kernel/Stub/Run) | nothing |
| `profile/` | Kernel; HexMvPoly and HexModArith v0.6.0 (with HexPoly, HexArith, HexBasic) |
| `binding/` | profile; Mathlib `85e3a25e`; HexMvPolyMathlib v0.6.0 |

`tests/test_gp50_profile_layout.py` checks four things:
- the profile manifest and sources have no Mathlib;
- shared Hex revisions agree with the binding;
- the binding requires the profile;
- all toolchains match.

The probe `gp_profile_layout` builds in 75 s and evaluates `xy − 1` over ℤ and `½xy − 1` over ℚ. `MvPoly 2 Rat` has decidable equality, so rational coefficients work without Mathlib.

## Convergence (A5), baseline

(a) The slice has 23 held claims, all over stub or harness profiles with synthetic statements. Each has a kernel-checked `Means` theorem, but none states mathematics, so the mathematical fraction is 0/23 and not yet meaningful.

(b) Tags ([data](PHASE-2.5-CONVERGENCE.json)):

| Tag | Count |
|---|---|
| CUSTODY | 13 |
| COVERAGE | 7 |
| REACH | 1 |
| EARNED | 0 |
| NONE | 2 |

The two NONE claims are idempotent redeclarations.

(c) The baseline is dominated by custody because the Phase 2 corpus was built to exercise lifecycle, so it says little yet about the pivot question. The first informative reading is the §3.6 reach slice: Hex should make (a) cheap there, and pivot condition 3 asks whether REACH and EARNED survive. AutoGeneralization targets `v4.33.0-rc1` and an older Mathlib, so §3.6a needs a port or a compatibility check first.

## Ratification ask

Ratify G2.5 so §3.6 may begin. Builder Markdown: 401 words before this report (target 2,000).
