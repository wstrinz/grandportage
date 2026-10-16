import GP50.NarrowingAdmissionProofs

/-!
Lane P (GP 0.52, P1; `docs/private/LANEP-DESIGN.md` §2–4): a Lean-proposition profile with
premises as scope, on the unchanged Kernel. Mathlib-free.

- **Statements** are registered codes (`Stmt := Nat`): a code names a `def X : Prop` of a campaign
  package, its negation, or a prose text. What a code means is a parameter `interp : Nat → Prop`.
- **Scopes** are lists of premise codes. `le a b` is `b ⊆ a`: adding premises narrows, so weakening
  is ordinary Kernel narrowing. `contra` is `false`.
- **Meaning:** `Means s S ↔ ((∀ h ∈ S, interp h) → interp s)` (`means_iff`).
- **Theorem warrants** are accepted against a binder record: the binder added
  `P₁ → … → Pₙ → S := T` to the Lean kernel without elaborating anything (`RecordsSoundP` is the
  trusted hypothesis, the class of `gp-binder/v2`).
- **Discharge** is a profile rule: from `(s, S ∪ {h})` and `(h, T)` with `T ⊆ S`, conclude `(s, S)`.
  Its soundness is the cut rule (`dischargeOk_sound`).

`fold_held_meaningP` gives every held claim its meaning for every `interp`, through the Kernel's
generic `Semantic.fold_held_meaning`.
-/

namespace GPProfile.LaneP
open GP50

/-- `a ⊆ b` on code lists. -/
def sub (a b : List Nat) : Bool := a.all b.contains

theorem sub_sound {a b : List Nat} (h : sub a b = true) : ∀ x ∈ a, x ∈ b := by
  intro x hx
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h x hx)

abbrev ops : Semantic.ProfileOps where
  Stmt := Nat
  Scope := List Nat
  same a b := a == b
  same_sound a b h := by simpa using h
  le a b := sub b a
  contra _ _ := false

/-- The semantic profile for an interpretation of codes: one context, premises as hypotheses. -/
abbrev profileP (interp : Nat → Prop) : Semantic.Profile where
  toProfileOps := ops
  Ctx := Unit
  mem _ S := ∀ h ∈ (show List Nat from S), interp h
  Holds s _ := interp (show Nat from s)
  le_sound a b _ hle hmem := fun h hb => hmem h (sub_sound hle h hb)
  contra_sound _ _ _ h := by cases h

theorem means_iff (interp : Nat → Prop) (s : Nat) (S : List Nat) :
    Semantic.Means (profileP interp) s S ↔ ((∀ h ∈ S, interp h) → interp s) :=
  ⟨fun h hs => h () hs, fun h _ hs => h hs⟩

abbrev Clause := Semantic.Clause ops

/-! ## Theorem warrants -/

/-- A binder record: the theorem `declaration`, whose type the binder built as
`P₁ → … → Pₙ → S` from the registered codes `premises` and `stmt` and added to the Lean kernel.
`ok` is the binder's verdict: the kernel accepted the declaration and the theorem's axioms are the
standard three. -/
structure Record where
  declaration : String
  stmt : Nat
  premises : List Nat
  ok : Bool
  deriving Repr, DecidableEq

/-- The binder trust assumption (the class of `gp-binder/v2`): an accepted record's type holds under
`interp`, the meaning of the registered codes. -/
def RecordsSoundP (interp : Nat → Prop) (records : List Record) : Prop :=
  ∀ r ∈ records, r.ok = true → (∀ h ∈ r.premises, interp h) → interp r.stmt

/-- Statement identity (design §1): each code's registered closure hash and environment stamp, and the
current bind's. A code is fresh when both exist and agree; otherwise its claims are unbound. -/
structure Identity where
  registered : List (Nat × String × String)
  current : List (Nat × String × String)
  deriving Repr

def Identity.fresh (i : Identity) (code : Nat) : Bool :=
  match i.registered.lookup code, i.current.lookup code with
  | some a, some b => a == b
  | _, _ => false

/-- A theorem warrant is accepted against a record for its bound clause: the same declaration and
statement code, premises within the clause's scope, and every code involved fresh. -/
def acceptsProof (clauses : List Clause) (ident : Identity) (records : List Record) (w : Warrant)
    (decl : String) : Bool :=
  match Semantic.boundClause ops clauses w with
  | none => false
  | some c => records.any fun r =>
      r.ok && r.declaration == decl && r.stmt == c.stmt && sub r.premises c.scope &&
        (r.stmt :: r.premises).all ident.fresh

/-! ## The discharge rule -/

/-- `(s, S₁)` with `h ∈ S₁ ⊆ S ∪ {h}`, and `(h, T)` with `T ⊆ S`, conclude `(s, S)`. Codes and statement
hashes are compared exactly; a different statement for `h` is a code mismatch. -/
def dischargeOk (c c1 c2 : Clause) : Bool :=
  c1.stmt == c.stmt && c1.binding.statementHash == c.binding.statementHash &&
    c1.binding.modelHash == c.binding.modelHash && c2.binding.modelHash == c.binding.modelHash &&
    c1.scope.contains c2.stmt && sub c1.scope (c2.stmt :: c.scope) && sub c2.scope c.scope

theorem dischargeOk_sound (interp : Nat → Prop) {c c1 c2 : Clause} (h : dischargeOk c c1 c2 = true)
    (m1 : Semantic.Means (profileP interp) c1.stmt c1.scope)
    (m2 : Semantic.Means (profileP interp) c2.stmt c2.scope) :
    Semantic.Means (profileP interp) c.stmt c.scope := by
  simp only [dischargeOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, -⟩, -⟩, -⟩, -⟩, h1⟩, h2⟩ := h
  rw [means_iff] at m1 m2 ⊢
  intro hS
  have hh : interp c2.stmt := m2 fun x hx => hS x (sub_sound h2 x hx)
  have : interp c1.stmt := m1 fun x hx => by
    rcases List.mem_cons.mp (sub_sound h1 x hx) with rfl | hx'
    · exact hh
    · exact hS x hx'
  exact hs ▸ this

def acceptsRule (clauses : List Clause) (w : Warrant) (premises : List Warrant) (side : String) : Bool :=
  side == "discharge" &&
    match premises with
    | [p1, p2] =>
      match Semantic.boundClause ops clauses w, Semantic.boundClause ops clauses p1,
          Semantic.boundClause ops clauses p2 with
      | some c, some c1, some c2 => dischargeOk c c1 c2
      | _, _, _ => false
    | _ => false

/-- Theorem warrants, the discharge rule and narrowing; no receipts in P1. -/
def baseAdmission (clauses : List Clause) (ident : Identity) (records : List Record) : Admission :=
  { Admission.refuseAll with proof := acceptsProof clauses ident records, rule := acceptsRule clauses }

def admission (clauses : List Clause) (ident : Identity) (records : List Record) : Admission :=
  Semantic.withNarrowing ops clauses (baseAdmission clauses ident records)

/-! ## Soundness -/

theorem bound_meaning (interp : Nat → Prop) (clauses : List Clause) (w : Warrant) (c : Clause)
    (found : Semantic.boundClause ops clauses w = some c)
    (means : Semantic.Means (profileP interp) c.stmt c.scope) :
    Semantic.ClaimMeaning (profileP interp) clauses w.claim := by
  rcases Semantic.boundClause_registered (profileP interp) clauses w c found with ⟨unique, present, key⟩
  refine ⟨⟨c, present, key⟩, fun c' hc' hkey' => ?_⟩
  have := key_unique_of_nodup clauses (·.key) unique c' c hc' present (hkey'.trans key.symm)
  exact this ▸ means

theorem acceptsProof_meaning (interp : Nat → Prop) (clauses : List Clause) (ident : Identity)
    (records : List Record) (hrec : RecordsSoundP interp records) (w : Warrant) (decl : String)
    (accepted : acceptsProof clauses ident records w decl = true) :
    Semantic.ClaimMeaning (profileP interp) clauses w.claim := by
  unfold acceptsProof at accepted
  cases found : Semantic.boundClause ops clauses w with
  | none => simp [found] at accepted
  | some c =>
    simp only [found, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at accepted
    obtain ⟨r, hr, ⟨⟨⟨⟨hok, -⟩, hstmt⟩, hsub⟩, -⟩⟩ := accepted
    refine bound_meaning interp clauses w c found ((means_iff interp _ _).mpr fun hS => ?_)
    rw [← hstmt]
    exact hrec r hr hok fun h hh => hS h (sub_sound hsub h hh)

theorem acceptsRule_meaning (interp : Nat → Prop) (clauses : List Clause) (w : Warrant)
    (premises : List Warrant) (side : String) (accepted : acceptsRule clauses w premises side = true)
    (supported : ∀ p ∈ premises, Semantic.ClaimMeaning (profileP interp) clauses p.claim) :
    Semantic.ClaimMeaning (profileP interp) clauses w.claim := by
  unfold acceptsRule at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨-, accepted⟩ := accepted
  match premises, accepted, supported with
  | [p1, p2], accepted, supported =>
    cases f : Semantic.boundClause ops clauses w with
    | none => simp [f] at accepted
    | some c =>
      cases f1 : Semantic.boundClause ops clauses p1 with
      | none => simp [f, f1] at accepted
      | some c1 =>
        cases f2 : Semantic.boundClause ops clauses p2 with
        | none => simp [f, f1, f2] at accepted
        | some c2 =>
          simp only [f, f1, f2] at accepted
          have r1 := Semantic.boundClause_registered (profileP interp) clauses p1 c1 f1
          have r2 := Semantic.boundClause_registered (profileP interp) clauses p2 c2 f2
          have m1 := (supported p1 (by simp)).2 c1 r1.2.1 r1.2.2
          have m2 := (supported p2 (by simp)).2 c2 r2.2.1 r2.2.2
          exact bound_meaning interp clauses w c f (dischargeOk_sound interp accepted m1 m2)

theorem base_validator_soundP (interp : Nat → Prop) (clauses : List Clause) (ident : Identity)
    (records : List Record) (hrec : RecordsSoundP interp records) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    Semantic.BaseValidatorSound (profileP interp) clauses (baseAdmission clauses ident records) snapshot := by
  constructor
  · intro _ _ _ accepted; cases accepted
  · intro w member decl accepted
    exact ⟨w, member, rfl, acceptsProof_meaning interp clauses ident records hrec w decl accepted⟩
  · intro w present premises side accepted members supported
    refine ⟨w, present, rfl, acceptsRule_meaning interp clauses w premises side accepted fun p hp => ?_⟩
    exact Semantic.warrant_meaning_claim (profileP interp) clauses snapshot unique p (members p hp)
      (supported p hp)

/-- **Fold soundness for Lane P** (design §4, generic part): for every interpretation of the codes
under which the binder's records hold, every held claim's premises imply its statement. -/
theorem fold_held_meaningP (interp : Nat → Prop) (clauses : List Clause) (ident : Identity)
    (records : List Record) (hrec : RecordsSoundP interp records) (events : List Event)
    (state : RuntimeState) (claim : Nat)
    (folded : fold (admission clauses ident records) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
      ∀ c ∈ clauses, c.key = claim → (∀ h ∈ c.scope, interp h) → interp c.stmt := by
  have unique : (state.snapshot.warrants.map (·.id)).Nodup := by
    unfold fold at folded
    cases resolved : resolve events with
    | error message => simp [resolved] at folded
    | ok snapshot =>
      rw [resolved] at folded
      have stateEq : evaluate (admission clauses ident records) snapshot = state := Except.ok.inj folded
      subst state
      exact resolve_warrant_ids_nodup events snapshot resolved
  have h := Semantic.fold_held_meaning (profileP interp) clauses _ events state claim
    (base_validator_soundP interp clauses ident records hrec state.snapshot unique) folded heldClaim
  exact ⟨h.1, fun c hc hk => (means_iff interp _ _).mp (h.2 c hc hk)⟩

end GPProfile.LaneP
