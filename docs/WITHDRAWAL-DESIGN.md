# Design: claim withdrawal (GP 0.51)

2026-10-13. **Approved by Will, 2026-10-13**, as designed: decisions 1–6 as recommended, `--cascade` required, and the older-reader hazard accepted with loud warnings (DECISIONS). It closes the LIMITS item "No withdrawal". Drafted by a planning agent; the builder checked the code citations and added the review note at the end. **No Kernel change is needed.**

## What exists today

**Kernel events.** The Kernel has `retract target` and `supersede target successor` (`phase2/lean/GP50/Events.lean:41-42`).
- `resolve` fails only when an id is both retracted and superseded.
- A retracted warrant is not `live`, so it gets no requirements.

**Already proved** (`LifecycleProofs.lean`, `EventOrderProofs.lean`):
- `retract_reachable_iff` and `retract_closure_iff`: after a warrant w is retracted, exactly the warrants with a derivation that avoids w stay reachable;
- `requirements_not_live`;
- `fold_eq_of_mem_iff` and `fold_perm`: the fold depends only on the set of events.

**Missing.** The Kernel has no claim retraction and no un-retract.

**Unused so far.**
- The profile files only `Simple` events.
- Lifecycle events reach only the merge guards.
- `gp merge` refuses them (`tools/gp.py`, "carries retraction or supersession records, which the profile does not apply yet").

## 1. What can be withdrawn

**A claim.** The profile files one support warrant per claim, with id = claim key, plus a theorem warrant at `2^60 + key`. Withdrawing claim K retracts both. This also covers withdrawing a warrant or a rule instance.

**Dependents.** Every dependent whose only derivations pass through K stops being held, and nothing else does (`retract_reachable_iff`).

**Covers.** Withdrawing a cover un-holds `goal n m false`, which rests on it. The spine stays held, because it is still a true implication.

**Refused: `goal` and `spine` claims.**
- Goal claims are the campaign statement, filed automatically.
- Spines are re-proposed by `goal_sync`.
- Withdraw the cover or the exclusion instead.

## 2. Kernel or not

Profile only:
- `Plan` and `Plan3` get `withdrawn : List Nat`. Both folds run over `ledger.events ++ withdrawEvents`, where each key k becomes `[.retract k, .retract (theoremWarrantId k)]`.
- The retracts stay out of `ledger.events`, so the existing `Simple` fast path and its proof are untouched.
- `gp.py` sends the withdrawn keys to both runners: 3a premises are copied into the 3b part, and retracting an absent id is harmless.
- Items gain `"withdrawn": true` only when it is true, so old ledgers give byte-identical runner output.

## 3. Soundness

**Already covered.** These theorems quantify over every event list, so held claims still mean their statements after any withdrawal:
- `Semantic.fold_held_meaning`;
- `GPBinding.Admission.fold_held_meaning`;
- `fold_held_meaning3`.

Order and merge are covered by `fold_eq_of_mem_iff`.

**New obligations** (profile, Mathlib-free, about 120 lines, added to the CI axiom audit):
- **W1 `withdraw_antitone`:** anything held after the retracts are added was held before. Withdrawal only un-holds.
- **W2 `withdraw_resolves`:** a log with no supersede events that resolves still resolves with retracts added, so a withdrawal never breaks a fold or a merge.
- **W3 `withdraw_unholds`:** a withdrawn key is not held.

## 4. Ledger format and compatibility

**Record:** `{"op":"withdraw","label","key","reason","at"}`. This is a `gp-ledger/v1` extension ("new ops may appear", USING-GP).

**Merge:**
- Records are joined by content.
- A withdrawal beats a support filed on the other branch, because the retract persists in the event set. Both merge orders give the same state.
- `merge` lists the claims withdrawn on the other branch, and any claim here that is no longer held.
- Raw `retract` and `supersede` ops stay refused.

**Restate:** independent of withdrawal. A claim with an `unread` matroid notice can still be withdrawn.

## 5. CLI

`gp withdraw LABEL --reason TEXT [--cascade]` folds before and after, and prints the difference:
```
withdrawn: X (key K): <reason>; was held at char 0
  no longer held: Y (rule k1a from X); not Q (decide from S, X)
  goal verdict: decided: not Q -> undecided
```

**Refusals:**
- an unknown label;
- a claim already withdrawn;
- an empty reason;
- a `goal` or `spine` claim;
- a legacy cover record;
- a withdrawal that would un-hold other held claims, unless `--cascade` is given (the claims are listed).

`submit` refuses a withdrawn label: "file the corrected claim under a new label". Labels stay taken.

**Views** (display only; whether a claim is held still comes from the fold):
- `status` shows a `withdrawn` row with its time and reason. A dependent reads "not held: rests on withdrawn X".
- `frontier` leaves withdrawn claims out.
- `explain` marks the withdrawn node.
- `tailings` gains a "withdrawn claim" kind.
- `goal_sync`'s proposals skip withdrawn claims.

## 6. Tests and controls

1. Withdraw a held claim, an open mis-filed claim, and a vacuous EMPTY claim. Each leaves the frontier and appears in tailings.
2. **Withdraw, then resubmit the same receipt:** refused. Control: a support record appended by hand is still not held.
3. **A withdrawn rule premise, in 3a and through the 3b copy:** the dependent is not held, and the withdrawal is refused without `--cascade`.
4. **A withdrawn cover under the decided Q(4,6) fixture:** the verdict becomes undecided, the spine stays held, and a new cover decides it again.
5. **Theorem warrant:** a claim with a binder record is no longer held. Control: retracting K alone leaves it held.
6. A withdrawn claim earns no widening.
7. **Merge:** a withdrawal on one branch and a support on the other give the same status in both orders. A raw `retract` is still refused.
8. Old fixture ledgers give byte-identical runner output.
9. W1–W3 pass the axiom audit.

## 7. Size and risk

**Size:** profile about 250 lines, binding none, `gp.py` about 250, tests about 300. Docs: LIMITS, USING-GP, GUARANTEES.

**Risk:** a missed channel (the 3b part, the theorem warrant, a guard) would silently leave a claim held. Tests 3 and 5 are the controls.

## Decisions for Will

1. **Claim-level, permanent withdrawal through Kernel `retract`, with no Kernel change.** Recommend: yes.
2. **Reversible support withdrawal** (the claim goes back to open under the same key) would need a v2 key scheme. Recommend: defer, since a better receipt already replaces a support.
3. **Require `--cascade`** when other held claims would lose their hold. Recommend: yes, because withdrawal is permanent.
4. **Refuse withdrawing `goal` and `spine` claims.** Recommend: yes.
5. **Ship `withdraw` as a v1 extension.** Recommend: yes, with the caveat in the review note below.
6. **Make W1–W3 required before the release.** Recommend: yes.

## Builder's review note

The citations check out (`Events.lean:41-42`; `retract_reachable_iff` at `LifecycleProofs.lean:21`; `fold_eq_of_mem_iff` at `EventOrderProofs.lean:315`; the merge refusal in `tools/gp.py`).

**The one weak spot is decision 5's compatibility.** gp 0.50.x skips unknown ops. Opened with an old `gp`, a ledger showing a withdrawal shows the withdrawn claim as held again. That is still sound (W1: the claim is true), but it reverses the owner's explicit decision, which is the kind of quiet overstatement GP exists to stop. A v1 ledger cannot make an old `gp` refuse, since the init record cannot change.

**Recommendation:** accept the hazard for 0.51 and state it loudly:
- in the release notes;
- in the USING-GP compatibility section;
- in the `withdraw` command's own output ("readers older than 0.51 will not see this withdrawal").

For the next schema version, add a "minimum reader" field to the init record, so a ledger can require a newer `gp`.
