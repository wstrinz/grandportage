import GPProfile.Withdraw
import GPProfile.Canonical

/-!
Build-time checks (`#guard`) of claim withdrawal (docs/WITHDRAWAL-DESIGN.md §6, tests 5 and 6, and the
3a half of test 3). The campaign runner `gp_ledger` mints no theorem warrants (it is given no binder
records), so the theorem-warrant channel is checked here, through `Plan.run` with a binder record.

Claim 1 (`x - 1 = 0` is NONEMPTY at characteristic 0, by the point `x = 1`) is held by its receipt and,
with a binder record for its statement and scope, also by its theorem warrant. Claim 2 (NOT_IN_IDEAL(1)
on the same system) rests on claim 1 by the bridge rule `witness`.
-/

namespace GPProfile.WithdrawTests
open GP50 GPProfile

private def x := ["x"]

private def p (t : String) : Sparse :=
  match parse x t with
  | .ok q => (canonical x.length q).getD q
  | .error _ => []

private def s1 : Stmt := ⟨x, [p "x - 1"], [], .nonempty⟩
private def s2 : Stmt := ⟨x, [p "x - 1"], [], .notInIdeal (oneP 1)⟩

private def base : Plan :=
  { items := [{ key := 1, stmt := s1, scope := Scope.char0Only, support := .receipt (.point .rat [1]) },
              { key := 2, stmt := s2, scope := Scope.char0Only, support := .rule .witness [1] }],
    requested := [1, 2] }

/-- A binder record for claim 1's exact statement and scope (data here; the binder issues real ones). -/
private def records : List BinderRecord := [⟨"WithdrawTests.claim1", stmtCanon s1, scopeCanon Scope.char0Only⟩]

private def heldRun (q : Plan) (rs : List BinderRecord) (k : Nat) : Bool :=
  match q.run rs with
  | .ok o => held o.state k
  | .error _ => false

private def widenedRun (q : Plan) : List Nat :=
  match q.run with
  | .ok o => o.widened.map (·.1)
  | .error _ => [0]

/-- `Plan.run`'s filing and theorem warrants, folded with `extra` events appended (the controls). -/
private def foldWith (q : Plan) (rs : List BinderRecord) (extra : List Event) : Except String RuntimeState := do
  let l ← fileAll q.items ({ records := rs } : Ledger)
  let l ← q.items.foldlM (fun l i => do pure (← l.mintTheorem i).1) l
  fold l.admission (l.events ++ extra)

private def heldIn (r : Except String RuntimeState) (k : Nat) : Bool :=
  match r with
  | .ok s => held s k
  | .error _ => false

-- Before withdrawal: both claims are held, and claim 1's theorem warrant is supported.
#guard heldRun base records 1 && heldRun base records 2
#guard match base.run records with
  | .ok o => o.state.supports.contains (theoremWarrantId 1) && o.theorems == [(1, "WithdrawTests.claim1")]
  | .error _ => false

-- Test 5: withdrawing claim 1 un-holds it although a theorem warrant was minted for it.
#guard !heldRun { base with withdrawn := [1] } records 1
-- Control: retracting the support warrant alone leaves claim 1 held by its theorem warrant, so withdrawal
-- must retract `theoremWarrantId 1` too. Its dependent rests on warrant 1 and is not held.
#guard heldIn (foldWith base records [.retract 1]) 1
#guard !heldIn (foldWith base records [.retract 1]) 2
#guard !heldIn (foldWith base records (withdrawEvents [1])) 1
-- Without a binder record there is no theorem warrant, and the support retract alone un-holds it.
#guard !heldIn (foldWith base [] [.retract 1]) 1

-- Test 3 (3a): the dependent of a withdrawn premise is not held; withdrawing the dependent alone leaves
-- the premise held.
#guard !heldRun { base with withdrawn := [1] } records 2
#guard !heldRun { base with withdrawn := [1] } [] 2
#guard heldRun { base with withdrawn := [2] } [] 1 && !heldRun { base with withdrawn := [2] } [] 2

-- Test 6: the point `x = 1` replays at every characteristic, so claim 1 earns a widening; withdrawn, none.
#guard widenedRun base == [1]
#guard widenedRun { base with withdrawn := [1] } == []

-- A withdrawn key no plan files is harmless (W2): the run succeeds and holds what it held.
#guard heldRun { base with withdrawn := [7] } records 1 && heldRun { base with withdrawn := [7] } records 2

end GPProfile.WithdrawTests
