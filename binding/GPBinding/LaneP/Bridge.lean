import GPBinding.Real.AdmissionSound
import GPProfile.LaneP.Bridge

/-!
Lane P bridges, the binding part (GP 0.52 P2; `docs/private/LANEP-DESIGN.md` §3 `profile_replay`, §4).

A bridge code is generated (`gp register --bridge`) as `def X : Prop := meaning3 "<literal>"`: the literal 3a/3b
meaning of the bridged claim, `Semantic.Means profile3 stmt scope` of the statement and scope the literal parses
to (`GPProfile.LaneP.litOf`, the 3b runner's own parsers). The generated file proves `BridgeSound X "<literal>"`
by `Iff.rfl`, and the P binder re-checks it in the kernel.

- `bridgeOk_meaning`: an accepted bridge's literal meaning holds. The P runner's `bridgeOk` re-folds the 3a/3b
  part with `Plan3.run`; `fold_held_meaning3` gives the held clause its meaning, and the clause's statement and
  scope are the literal's.
- `fold_held_meaningP_bridge3`: Lane P's fold soundness with bridges. For every interpretation of the codes under
  which the binder's records hold and every bridge code is its literal meaning, every held claim's premises imply
  its statement.
-/

namespace GPBinding.LaneP
open GP50 GPProfile.LaneP GPProfile.Real GPBinding.Real

/-- The literal 3a/3b meaning: what `fold_held_meaning3` gives a held claim of this statement and scope. -/
def meaning3 (lit : String) : Prop :=
  match litOf lit with
  | .ok (_, st, sc) => Semantic.Means profile3 st sc
  | .error _ => False

/-- A bridge code means exactly its literal. In generated code this is `Iff.rfl`. -/
def BridgeSound (X : Prop) (lit : String) : Prop := X ↔ meaning3 lit

theorem bridgeOk_meaning (b : Bridge) (h : bridgeOk b = true) : meaning3 b.lit := by
  unfold bridgeOk at h
  cases hl : litOf b.lit with
  | error e => simp [hl] at h
  | ok v =>
    obtain ⟨k, st, sc⟩ := v
    cases hr : b.plan.run with
    | error e => simp [hl, hr] at h
    | ok o =>
      simp only [hl, hr, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
      obtain ⟨hheld, c, hc, ⟨hk, hs⟩, hsc⟩ := h
      have hs' : (c.stmt : Stmt3) = st := (beq_iff_eq (α := Stmt3)).mp hs
      have hsc' : (c.scope : Scope3) = sc := (beq_iff_eq (α := Scope3)).mp hsc
      have hm := (fold_held_meaning3 _ _ _ _ _ k (plan3_run_fold b.plan o hr) hheld).2 c hc hk
      unfold meaning3
      rw [hl]
      show Semantic.Means profile3 st sc
      exact hs' ▸ hsc' ▸ hm

theorem bridges_sound (interp : Nat → Prop) (bridges : List Bridge)
    (hb : ∀ b ∈ bridges, BridgeSound (interp b.code) b.lit) : BridgesSoundP interp bridges :=
  fun b hm ok => (hb b hm).mpr (bridgeOk_meaning b ok)

/-- **Fold soundness for Lane P with bridges** (design §4): given `RecordsSoundP` and `BridgeSound` for every
bridge, every held claim's premises imply its statement. -/
theorem fold_held_meaningP_bridge3 (interp : Nat → Prop) (clauses : List Clause) (ident : Identity)
    (records : List Record) (bridges : List Bridge) (hrec : RecordsSoundP interp records)
    (hb : ∀ b ∈ bridges, BridgeSound (interp b.code) b.lit) (events : List Event) (state : RuntimeState)
    (claim : Nat) (folded : fold (admission clauses ident (records ++ bridges.map bridgeRecord)) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
      ∀ c ∈ clauses, c.key = claim → (∀ h ∈ c.scope, interp h) → interp c.stmt :=
  fold_held_meaningP_bridged interp clauses ident records bridges hrec (bridges_sound interp bridges hb) events
    state claim folded heldClaim

end GPBinding.LaneP
