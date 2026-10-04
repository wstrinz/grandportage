import GP50.CoverAdmissionProofs
namespace GP50.CoveredSpan.Controls

example (rows : List ScopedSpan.Row) (receipts : List Span.Receipt) (rules : List Rule)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission rows receipts rules) events = .ok state)
    (heldClaim : held state claim = true) :
    Semantic.ClaimMeaning ScopedSpan.profile (rows.map ScopedSpan.semantic) claim :=
  fold_held_meaning rows receipts rules events state claim success heldClaim

example (rows : List ScopedSpan.Row) (receipts : List Span.Receipt) (rules : List Rule)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission rows receipts rules) events = .ok state)
    (heldClaim : held state claim = true) : ∃ row ∈ rows, row.algebra.key = claim := by
  rcases (fold_held_meaning rows receipts rules events state claim success heldClaim).1 with
    ⟨clause, present, key⟩
  rcases List.mem_map.mp present with ⟨row, rowPresent, rfl⟩
  exact ⟨row, rowPresent, key⟩

example (rows : List ScopedSpan.Row) (receipts : List Span.Receipt) (rules : List Rule)
    (events : List Event) (state : RuntimeState) (claim : Nat) (row : ScopedSpan.Row)
    (success : fold (admission rows receipts rules) events = .ok state)
    (heldClaim : held state claim = true) (registered : row ∈ rows) (key : row.algebra.key = claim) :
    Semantic.Means ScopedSpan.profile (ScopedSpan.semantic row).stmt row.scope :=
  (fold_held_meaning rows receipts rules events state claim success heldClaim).2
    (ScopedSpan.semantic row) (List.mem_map.mpr ⟨row, registered, rfl⟩) key

example (rows : List ScopedSpan.Row) (premises : List Warrant)
    (branches : List (Semantic.Clause ScopedSpan.profile))
    (mapped : premises.mapM (Semantic.boundClause ScopedSpan.profile
      (rows.map ScopedSpan.semantic)) = some branches)
    (truth : ∀ premise ∈ premises,
      Semantic.ClaimMeaning ScopedSpan.profile (rows.map ScopedSpan.semantic) premise.claim) :
    ∀ branch ∈ branches, Semantic.Means ScopedSpan.profile branch.stmt branch.scope :=
  Semantic.boundClauses_mapM_means _ _ _ _ mapped truth

example (rows : List ScopedSpan.Row) (rules : List Rule)
    (dest : Warrant) (premises : List Warrant) (name : String)
    (accepted : accepts rows rules dest premises name = true)
    (truth : ∀ premise ∈ premises,
      Semantic.ClaimMeaning ScopedSpan.profile (rows.map ScopedSpan.semantic) premise.claim) :
    Semantic.ClaimMeaning ScopedSpan.profile (rows.map ScopedSpan.semantic) dest.claim :=
  accepts_claim_meaning rows rules dest premises name accepted truth

example (rows : List ScopedSpan.Row) (receipts : List Span.Receipt) (rules : List Rule)
    (events : List Event) (snapshot : Snapshot) (resolved : resolve events = .ok snapshot) :
    Semantic.BaseValidatorSound ScopedSpan.profile (rows.map ScopedSpan.semantic)
      (baseAdmission rows receipts rules) snapshot :=
  base_validator_sound rows receipts rules snapshot (resolve_warrant_ids_nodup events snapshot resolved)

example (rows : List ScopedSpan.Row) (receipts : List Span.Receipt) (rules : List Rule)
    (events : List Event) (state : RuntimeState)
    (success : fold (admission rows receipts rules) events = .ok state) :
    (state.snapshot.warrants.map (·.id)).Nodup :=
  fold_warrant_ids_nodup rows receipts rules events state success

-- Actual cover authorization binds the exact rule name, destination and ordered premise claim list.
example (rows : List ScopedSpan.Row) (rules : List Rule) (dest : Warrant)
    (premises : List Warrant) (name : String)
    (accepted : accepts rows rules dest premises name = true) :
    ∃ rule ∈ rules, rule.name = name ∧ rule.destination = dest.claim ∧
      rule.branches = premises.map (·.claim) := by
  have gates : ((rules.map (·.name)).eraseDups.length == rules.length) = true ∧
      rules.any (fun rule => rule.name == name && rule.destination == dest.claim &&
        rule.branches == premises.map (·.claim)) = true ∧
      Semantic.acceptsCover ScopedSpan.profile coverage (rows.map ScopedSpan.semantic) dest premises = true := by
    simpa only [accepts, Bool.and_eq_true, and_assoc] using accepted
  rcases List.any_eq_true.mp gates.2.1 with ⟨rule, present, checks⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at checks
  exact ⟨rule, present, checks.1.1, checks.1.2, checks.2⟩

example (rows : List ScopedSpan.Row) (rule : Rule) (dest : Warrant)
    (premises : List Warrant) (name : String) :
    accepts rows [rule,rule] dest premises name = false := by
  simp [accepts, List.eraseDups_cons]

-- Unregistered cover rules and absent receipts cannot bootstrap narrowing/cover cycles.
example (rows : List ScopedSpan.Row) (snapshot : Snapshot) (claim : Nat) :
    held (evaluate (admission rows [] []) snapshot) claim = false := by
  have sound : ValidatorSound (admission rows [] []) snapshot (fun _ => False) := by
    constructor
    · intro w member name accepted
      simp [admission, Semantic.withNarrowing, baseAdmission, Span.admission, Span.accepts] at accepted
    · intros; contradiction
    · intro w member premises name accepted members supported
      simp [admission, Semantic.withNarrowing, baseAdmission, accepts] at accepted
    · intros; contradiction
  cases bit : held (evaluate (admission rows [] []) snapshot) claim with
  | false => rfl
  | true =>
    have impossible := evaluate_held_truth_composition (admission rows [] []) snapshot
      (fun _ => False) (fun _ => False) sound (by intros; assumption) claim bit
    exact impossible.elim

end GP50.CoveredSpan.Controls
