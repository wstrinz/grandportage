import GPProfile.LaneP.Profile
import GPProfile.Real.Ledger3

/-!
Lane P bridges (GP 0.52 P2, design §3 `profile_replay`, tier 3): a P code whose definition is generated as
the literal 3a/3b meaning of a claim of another campaign. Mathlib-free; the meaning itself
(`GPBinding.LaneP.meaning3`) and `BridgeSound` are in the binding.

- The **literal** is the bridged claim's statement in the 3b surface (JSON text: `family`, the system, `kind`, the
  scope fields, `key`). `litOf` reads it with the 3b runner's own parsers.
- A **bridge** carries the P code, the literal and the 3a/3b part it is re-folded from: the bridged claim and the
  claims it rests on, in the 3b surface, with that campaign's withdrawals (`Plan3`).
- `bridgeOk` re-folds that part with `Plan3.run` (the Kernel fold under `admission3`) and accepts when the bridged
  claim is held and its clause's statement and scope are exactly the literal's.
- An accepted bridge is a binder-class record `bridge:<key>` for the code, with no premises, so the P admission
  holds a claim of the code by it (`bridgeRecord`). `fold_held_meaningP_bridged` is `fold_held_meaningP` over the
  theorem and receipt records plus the bridge records; its bridge hypothesis is discharged in the binding
  (`GPBinding.LaneP.fold_held_meaningP_bridge3`).
-/

namespace GPProfile.LaneP
open Lean GP50 GPProfile GPProfile.Families GPProfile.Real

/-- The bridged claim's key, statement and scope, read from the literal with the 3b runner's parsers. -/
def litOf (lit : String) : Except String (Nat × Stmt3 × Scope3) := do
  let j ← Json.parse lit
  let fam ← need (str? j "family") "no family"
  if fam == "alg" then
    let h ← surfaceHead (match j with | .obj kvs => Json.obj (kvs.erase "family") | x => x)
    return (h.key, .alg h.stmt, .alg h.scope)
  pure (← LedgerRun3.keyOf j, ← LedgerRun3.stmtOf fam j, ← LedgerRun3.scope3Of j)

structure Bridge where
  code : Nat
  lit : String
  plan : Plan3

/-- The re-folded 3a/3b part holds the literal's claim, with exactly the literal's statement and scope. -/
def bridgeOk (b : Bridge) : Bool :=
  match litOf b.lit, b.plan.run with
  | .ok (k, st, sc), .ok o =>
    held o.state k && o.ledger.clauses.any fun c =>
      c.key == k && (show Stmt3 from c.stmt) == st && (show Scope3 from c.scope) == sc
  | _, _ => false

def bridgeRecord (b : Bridge) : Record := ⟨s!"bridge:{b.code}", b.code, [], bridgeOk b⟩

/-- The generic bridge hypothesis: an accepted bridge's code holds. -/
def BridgesSoundP (interp : Nat → Prop) (bridges : List Bridge) : Prop :=
  ∀ b ∈ bridges, bridgeOk b = true → interp b.code

/-- What `Plan3.run` folded: its ledger's events and the withdrawals, under `admission3`. -/
theorem plan3_run_fold (p : Plan3) (o : Outcome3) (h : p.run = .ok o) :
    fold (admission3 o.ledger.clauses o.ledger.receipts o.ledger.rules)
      (o.ledger.events ++ withdrawEvents p.withdrawn) = .ok o.state := by
  unfold Plan3.run at h
  cases hf : fileAll3 p.items {} with
  | error e => simp [hf, bind, Except.bind] at h
  | ok l =>
    cases hs : fold l.admission (l.events ++ withdrawEvents p.withdrawn) with
    | error e => simp [hf, hs, bind, Except.bind] at h
    | ok s =>
      simp only [hf, hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hs

theorem records_bridges_sound (interp : Nat → Prop) (records : List Record) (bridges : List Bridge)
    (hrec : RecordsSoundP interp records) (hb : BridgesSoundP interp bridges) :
    RecordsSoundP interp (records ++ bridges.map bridgeRecord) := by
  intro r hr hok hprem
  rcases List.mem_append.mp hr with h | h
  · exact hrec r h hok hprem
  · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp h
    exact hb b hbm hok

/-- **Fold soundness with bridges** (design §4, generic part): under sound records and sound bridges, every
held claim's premises imply its statement. -/
theorem fold_held_meaningP_bridged (interp : Nat → Prop) (clauses : List Clause) (ident : Identity)
    (records : List Record) (bridges : List Bridge) (hrec : RecordsSoundP interp records)
    (hb : BridgesSoundP interp bridges) (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission clauses ident (records ++ bridges.map bridgeRecord)) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
      ∀ c ∈ clauses, c.key = claim → (∀ h ∈ c.scope, interp h) → interp c.stmt :=
  fold_held_meaningP interp clauses ident _ (records_bridges_sound interp records bridges hrec hb) events state
    claim folded heldClaim

end GPProfile.LaneP
