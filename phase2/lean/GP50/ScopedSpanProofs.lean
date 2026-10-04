import GP50.ScopedSpan
import GP50.NarrowingAdmissionProofs
namespace GP50.ScopedSpan

-- Holds is exactly the specified formal Rat identity, on named Nat test contexts.
theorem formalSpan_means (row : Row) (identity : Span.FormalSpan row.algebra) :
    Semantic.Means profile (semantic row).stmt (semantic row).scope := by
  intro ctx present
  exact identity

theorem accepts_claim_meaning (rows : List Row) (receipts : List Span.Receipt)
    (w : Warrant) (name : String)
    (accepted : Span.accepts (rows.map (·.algebra)) receipts w name = true) :
    Semantic.ClaimMeaning profile (rows.map semantic) w.claim := by
  constructor
  · rcases (Span.accepts_exact_identity (rows.map (·.algebra)) receipts w name accepted).2 with
      ⟨chosen, present, key, _⟩
    rcases List.mem_map.mp present with ⟨row, rowPresent, rowEq⟩
    refine ⟨semantic row, List.mem_map.mpr ⟨row, rowPresent, rfl⟩, ?_⟩
    change row.algebra.key = w.claim
    rw [rowEq]
    exact key
  · intro clause present key
    rcases List.mem_map.mp present with ⟨row, rowPresent, rfl⟩
    apply formalSpan_means
    exact Span.accepts_unique_clause_meaning (rows.map (·.algebra)) receipts w name accepted
      row.algebra (List.mem_map.mpr ⟨row, rowPresent, rfl⟩) key

theorem base_validator_sound (rows : List Row) (receipts : List Span.Receipt)
    (snapshot : Snapshot) :
    Semantic.BaseValidatorSound profile (rows.map semantic)
      (Span.admission (rows.map (·.algebra)) receipts) snapshot := by
  constructor
  · intro w member name accepted
    exact ⟨w, member, rfl, accepts_claim_meaning rows receipts w name accepted⟩
  · intros; contradiction
  · intros; contradiction

theorem fold_held_meaning (rows : List Row) (receipts : List Span.Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission rows receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    Semantic.ClaimMeaning profile (rows.map semantic) claim := by
  have result := Semantic.fold_held_meaning profile (rows.map semantic)
    (Span.admission (rows.map Row.algebra) receipts) events state claim
    (base_validator_sound rows receipts state.snapshot)
  apply result
  · exact folded
  · exact heldClaim

theorem fold_held_row_meaning (rows : List Row) (receipts : List Span.Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission rows receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ row ∈ rows, row.algebra.key = claim) ∧
    (∀ row ∈ rows, row.algebra.key = claim →
      Semantic.Means profile (semantic row).stmt row.scope) := by
  have meaning := fold_held_meaning rows receipts events state claim folded heldClaim
  constructor
  · rcases meaning.1 with ⟨clause, present, key⟩
    rcases List.mem_map.mp present with ⟨row, rowPresent, rfl⟩
    exact ⟨row, rowPresent, key⟩
  · intro row present key
    exact meaning.2 (semantic row) (List.mem_map.mpr ⟨row, present, rfl⟩) key

#print axioms formalSpan_means
#print axioms accepts_claim_meaning
#print axioms base_validator_sound
#print axioms fold_held_meaning
#print axioms fold_held_row_meaning
end GP50.ScopedSpan
