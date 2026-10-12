# Phase 4 report (G4)

Authority: post-G2 handoff §4 and post-G3a handoff §5. Will closed out G4 on 2026-10-06 ("yep lets do C") as part of the step back that followed OpenAI's mathematics release. This report records the gate evidence. Details are in [DECISIONS.md](../DECISIONS.md) and [STATUS.md](../STATUS.md).

## What exists

**The census profile** (`census/`, Mathlib-free, on HexGraphIso v0.4.0 and the vendored LRAT-Catcher) is the second real profile on the Kernel.
- **Objects:** coloured graphs. Incidence structures are 2-coloured Levi graphs.
- **Predicates:** first-order, with counting quantifiers and action atoms. One theorem (`eval_iso`) makes every predicate invariant under isomorphism, including actions carried along.
- **Kinds:**
  - EXISTS, held by a witness;
  - NONE, held by LRAT or a checked cube cover against the CNF Lean emits, with model expansion proved;
  - EXHAUSTIVE and COUNT, held by listing with a lex-leader break and distinct HexGraphIso canonical forms;
  - COUNT under a visible catalog premise;
  - the V4 kinds for the DK slice ([design](../docs/DK-V4-DESIGN.md)).
- **Soundness:** `fold_held_meaning` holds through the Kernel's generic theorem, on standard axioms only. LRAT replay keeps its admitted native trust (`TCB.md`).

## Gate conditions

| Condition | Evidence | Met |
|---|---|---|
| Kernel pin unchanged | All 22 pinned files match `KERNEL-PIN.json`. The last Kernel change was Phase 2.5. No D9 promotions. | yes |
| `ProfileOps`/`Profile` split and `Ctx` used unchanged by a second profile | The census instantiates both with `Ctx := Nat`, without touching Kernel code | yes |
| Census traps refused | Every trap has a refusing control (`tests/test_gp50_census*.py`); see the list below | yes |
| DK slice reproduces | The n = 19 control holds outright; the six n = 23 cells hold under CELL-COMPLETE ([receipt](DK-V4-RECEIPT.json)) | yes, with premises |
| 3P ledger replays unchanged after Phase 4 | 1,887 of 1,887 supports held, 0 held without support, 1,881 of 1,881 frames equal | yes |

## The DK slice

- **n = 19 control: COUNT = 9, held by listing.** DK's normal-form point action is fixed, and the symmetry break uses relabellings that commute with it.
  - The proposer listed 3,840 labelled models.
  - Lean emitted a CNF of 2.0 M variables and 6.0 M clauses, which CaDiCaL refuted with a 592 MB LRAT proof.
  - GP checked the certificate in 329 s. The 9 types are DK's.
- **n = 23: six cell counts held under CELL-COMPLETE** (1361, 1286, 693, 669, 693, 669).
  - GP checked every member with its action, the line inventory and distinct canonical forms.
  - The premise names the two enumeration routes, and states that the b12 cells are not independent (derived by duality in a shared `join.py`).
- **Bridge premise V4-NORMAL-FORM:** DK's "admits some V4 action" equals "isomorphic to a normal-form member" (classification of V4-sets). It is standard and closable in principle, and stays outside the claims.
- **Fidelity:** GP's predicate agreed with DK's own fence code in differential tests: 2,000 n = 19 structures and all 32,226 labelled n = 23 (type, cell) pairs, with 0 mismatches.
- **Custody:** DK's enumerator, rerun by the builder, regenerated all 5,299 committed type files. The data stays in the private harvest; the receipt binds it by SHA-256.

## Traps refused

- A timeout read as UNSAT.
- "None up to n" read as "none".
- A truncated proof.
- A proof for another encoding.
- A witness that fails the predicate.
- A floating-point witness.
- A non-exhaustive cover.
- A wrong count, a duplicate class, or a missing class.
- For V4: a missed model (the CNF stays satisfiable), an invalid action, a non-centralising relabelling, and a wrong count.
- A model count is never read as a class count, so an unsound symmetry break has no path to a held claim.

## Open after G4

- **Premises:** V4-NORMAL-FORM, CELL-COMPLETE, and 3P's CATALOG-COMPLETE.
- **Kernel `closure`:** it is cubic. Rewriting it is a Kernel change and needs Will.
- **Lean-warrant coverage:** 31% on the 3P ledger, with map rules the main gap.
- **Direction:** a step back is under way. Will's call on 2026-10-06: close G4, freeze the narrow profiles (no extension without a new decision), and review overall direction in light of the OpenAI release, likely including some GP work on that corpus.

## Custody share

4 of 31 builder commits were custody-only (13%), under the 30% tripwire. 8 were governance (26%), and 19 were work. Window: 2026-10-04 to the G4 close (`3bd0bf0`). Rule (agreed 2026-10-07; `tools/custody-share.py`): the builder's non-merge commits only, campaign-agent commits excluded. A commit is custody-only when every path it changes is CI, a snapshot or publication manifest, a pin or a custody receipt. It is governance when every path is a record (decisions, status, TCB, docs, reports) or custody. Anything touching code, proofs, tests or tools is work.
