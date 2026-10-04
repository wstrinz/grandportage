import GP50.Runtime
import GP50.PolyStub
namespace GP50.Span
open PolyStub
-- The configured statement carries actual polynomial data; hashes are custody
-- identities checked against it under the adapter's byte-binding contract.
structure Clause where
  key : Nat
  version : Nat
  binding : Binding
  generators : List Polynomial
  target : Polynomial
  deriving Repr, BEq, DecidableEq
structure Receipt where
  name : String
  claim : Nat
  version : Nat
  binding : Binding
  cofactors : List Polynomial
  deriving Repr, BEq, DecidableEq

def wellFormed (clauses : List Clause) (receipts : List Receipt) : Bool :=
  (clauses.map (·.key)).eraseDups.length == clauses.length &&
    (receipts.map (·.name)).eraseDups.length == receipts.length

def accepts (clauses : List Clause) (receipts : List Receipt)
    (warrant : Warrant) (name : String) : Bool :=
  wellFormed clauses receipts &&
    clauses.any fun clause => clause.key == warrant.claim &&
      clause.version == warrant.version && decide (clause.binding = warrant.binding) &&
      receipts.any fun receipt => receipt.name == name && receipt.claim == clause.key &&
        receipt.version == clause.version && decide (receipt.binding = clause.binding) &&
        replay clause.generators receipt.cofactors clause.target

def admission (clauses : List Clause) (receipts : List Receipt) : Admission :=
  { Admission.refuseAll with receipt := accepts clauses receipts }
end GP50.Span
