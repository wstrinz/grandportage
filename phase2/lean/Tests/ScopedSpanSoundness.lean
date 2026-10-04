import GP50.ScopedSpanProofs
namespace GP50.ScopedSpan.SoundnessControls

example (rows : List Row) (receipts : List Span.Receipt) (snapshot : Snapshot) :
    Semantic.BaseValidatorSound profile (rows.map semantic)
      (Span.admission (rows.map (·.algebra)) receipts) snapshot :=
  base_validator_sound rows receipts snapshot

example (rows : List Row) (receipts : List Span.Receipt) (w : Warrant) (name : String)
    (accepted : Span.accepts (rows.map (·.algebra)) receipts w name = true) :
    Semantic.ClaimMeaning profile (rows.map semantic) w.claim :=
  accepts_claim_meaning rows receipts w name accepted

example (rows : List Row) (receipts : List Span.Receipt) (w : Warrant) (name : String)
    (accepted : Span.accepts (rows.map (·.algebra)) receipts w name = true) :
    ((rows.map semantic).map (·.key)).Nodup := by
  have unique := (Span.wellFormed_nodup (rows.map (·.algebra)) receipts
    (Span.accepts_exact_identity (rows.map (·.algebra)) receipts w name accepted).1).1
  simpa only [List.map_map, Function.comp_def, semantic] using unique

-- The concrete fold conclusion has no validator-soundness or uniqueness hypothesis.
example (rows : List Row) (receipts : List Span.Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission rows receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    Semantic.ClaimMeaning profile (rows.map semantic) claim :=
  fold_held_meaning rows receipts events state claim success heldClaim

example (rows : List Row) (receipts : List Span.Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission rows receipts) events = .ok state)
    (heldClaim : held state claim = true) : ∃ row ∈ rows, row.algebra.key = claim :=
  (fold_held_row_meaning rows receipts events state claim success heldClaim).1

example (rows : List Row) (receipts : List Span.Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat) (row : Row)
    (success : fold (admission rows receipts) events = .ok state)
    (heldClaim : held state claim = true) (registered : row ∈ rows) (key : row.algebra.key = claim) :
    Semantic.Means profile (semantic row).stmt row.scope :=
  (fold_held_row_meaning rows receipts events state claim success heldClaim).2 row registered key

-- An explicitly named context in scope supplies a formal identity, not a geometric claim.
example (rows : List Row) (receipts : List Span.Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat) (row : Row) (ctx : Nat)
    (success : fold (admission rows receipts) events = .ok state)
    (heldClaim : held state claim = true) (registered : row ∈ rows)
    (key : row.algebra.key = claim) (inScope : ctx ∈ row.scope) : Span.FormalSpan row.algebra :=
  ((fold_held_row_meaning rows receipts events state claim success heldClaim).2 row registered key)
    ctx inScope

example (row : Row) (identity : Span.FormalSpan row.algebra) :
    Semantic.Means profile (semantic row).stmt (semantic row).scope :=
  formalSpan_means row identity

-- Empty scope Means is vacuous and supplies no named-context existence witness.
example (row : Row) :
    Semantic.Means profile (semantic {row with scope := []}).stmt [] := by
  intro ctx present
  exact (List.not_mem_nil present).elim

example (receipts : List Span.Receipt) (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission [] receipts) events = .ok state) :
    held state claim = false := by
  cases bit : held state claim with
  | false => rfl
  | true =>
    rcases (fold_held_row_meaning [] receipts events state claim success bit).1 with
      ⟨row, present, _⟩
    simp at present

-- Without receipts, actual scoped admission has no roots and narrowing cannot bootstrap.
example (rows : List Row) (snapshot : Snapshot) (claim : Nat) :
    held (evaluate (admission rows []) snapshot) claim = false := by
  have sound : ValidatorSound (admission rows []) snapshot (fun _ => False) := by
    constructor
    · intro w member name accepted
      simp [admission, Semantic.withNarrowing, Span.admission, Span.accepts] at accepted
    · intros; contradiction
    · intros; contradiction
    · intros; contradiction
  cases bit : held (evaluate (admission rows []) snapshot) claim with
  | false => rfl
  | true =>
    have impossible := evaluate_held_truth_composition (admission rows []) snapshot
      (fun _ => False) (fun _ => False) sound (by intros; assumption) claim bit
    exact impossible.elim

end GP50.ScopedSpan.SoundnessControls
