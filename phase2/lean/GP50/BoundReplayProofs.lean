import GP50.BoundReplay
import GP50.PolyStubProofs
import GP50.ResolveProofs
namespace GP50.Span
open PolyStub

-- Native formal Rat coefficient identities; byte/digest binding is an adapter contract.
def ReceiptIdentity (clause : Clause) (receipt : Receipt) : Prop :=
  clause.generators.length = receipt.cofactors.length ∧
    ∀ exponent, ((clause.generators.zip receipt.cofactors).map fun (generator,cofactor) =>
      coefficient (multiply generator cofactor) exponent).sum = coefficient clause.target exponent

def FormalSpan (clause : Clause) : Prop :=
  ∃ cofactors : List Polynomial, clause.generators.length = cofactors.length ∧
    ∀ exponent, ((clause.generators.zip cofactors).map fun (generator,cofactor) =>
      coefficient (multiply generator cofactor) exponent).sum = coefficient clause.target exponent

theorem wellFormed_nodup (clauses : List Clause) (receipts : List Receipt)
    (valid : wellFormed clauses receipts = true) :
    (clauses.map (·.key)).Nodup ∧ (receipts.map (·.name)).Nodup := by
  have lengths : (clauses.map (·.key)).eraseDups.length = clauses.length ∧
      (receipts.map (·.name)).eraseDups.length = receipts.length := by
    simpa only [wellFormed, Bool.and_eq_true, beq_iff_eq] using valid
  constructor
  · apply nodup_of_eraseDups_length_eq
    simpa only [List.length_map] using lengths.1
  · apply nodup_of_eraseDups_length_eq
    simpa only [List.length_map] using lengths.2

theorem accepts_exact_identity (clauses : List Clause) (receipts : List Receipt)
    (warrant : Warrant) (name : String)
    (accepted : accepts clauses receipts warrant name = true) :
    wellFormed clauses receipts = true ∧
      ∃ clause ∈ clauses, clause.key = warrant.claim ∧ clause.version = warrant.version ∧
        clause.binding = warrant.binding ∧
        ∃ receipt ∈ receipts, receipt.name = name ∧ receipt.claim = clause.key ∧
          receipt.version = clause.version ∧ receipt.binding = clause.binding ∧
          ReceiptIdentity clause receipt := by
  have checks : wellFormed clauses receipts = true ∧
      ∃ clause ∈ clauses, clause.key = warrant.claim ∧ clause.version = warrant.version ∧
        clause.binding = warrant.binding ∧
        ∃ receipt ∈ receipts, receipt.name = name ∧ receipt.claim = clause.key ∧
          receipt.version = clause.version ∧ receipt.binding = clause.binding ∧
          replay clause.generators receipt.cofactors clause.target = true := by
    simpa only [accepts, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
      decide_eq_true_eq, and_assoc] using accepted
  rcases checks with ⟨valid, clause, clausePresent, claimEq, versionEq, bindingEq,
    receipt, receiptPresent, nameEq, receiptClaim, receiptVersion, receiptBinding, replayed⟩
  exact ⟨valid, clause, clausePresent, claimEq, versionEq, bindingEq,
    receipt, receiptPresent, nameEq, receiptClaim, receiptVersion, receiptBinding,
    replay_coefficient_sum clause.generators receipt.cofactors clause.target replayed⟩

theorem accepts_unique_clause_meaning (clauses : List Clause) (receipts : List Receipt)
    (warrant : Warrant) (name : String)
    (accepted : accepts clauses receipts warrant name = true) :
    ∀ clause ∈ clauses, clause.key = warrant.claim → FormalSpan clause := by
  rcases accepts_exact_identity clauses receipts warrant name accepted with
    ⟨valid, chosen, chosenPresent, claimEq, versionEq, bindingEq,
      receipt, receiptPresent, nameEq, receiptClaim, receiptVersion, receiptBinding, identity⟩
  intro clause present sameKey
  have sameClause := key_unique_of_nodup clauses (·.key)
    (wellFormed_nodup clauses receipts valid).1 clause chosen present chosenPresent
    (sameKey.trans claimEq.symm)
  subst clause
  exact ⟨receipt.cofactors, identity⟩

#print axioms wellFormed_nodup
#print axioms key_unique_of_nodup
#print axioms accepts_exact_identity
#print axioms accepts_unique_clause_meaning
end GP50.Span
