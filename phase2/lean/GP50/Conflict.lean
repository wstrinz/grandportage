import GP50.Narrowing
namespace GP50.Semantic
universe u

-- An overlap checker returns profile-chosen executable evidence, never a success flag.
structure OverlapOps (p : ProfileOps) where
  Code : Type
  witness : p.Scope → p.Scope → Option Code
-- A witness without its soundness proof cannot be registered.
structure Overlap (p : Profile.{u}) extends OverlapOps p.toProfileOps where
  sound : ∀ a b k, witness a b = some k → ∃ c, p.mem c a ∧ p.mem c b
instance (p : Profile.{u}) : CoeOut (Overlap p) (OverlapOps p.toProfileOps) := ⟨Overlap.toOverlapOps⟩

structure ConflictFinding (p : ProfileOps) (overlap : OverlapOps p) where
  leftSupport : Nat
  rightSupport : Nat
  leftClaim : Nat
  rightClaim : Nat
  witness : Option overlap.Code

def assessConflict (p : ProfileOps) (overlap : OverlapOps p)
    (a b : Clause p) (left right : Nat) : Option (ConflictFinding p overlap) :=
  if p.contra a.stmt b.stmt then
    some ⟨left, right, a.key, b.key, overlap.witness a.scope b.scope⟩
  else none

def conflictFindings (p : ProfileOps) (overlap : OverlapOps p)
    (clauses : List (Clause p)) (state : RuntimeState) : List (ConflictFinding p overlap) :=
  state.snapshot.warrants.flatMap fun a => state.snapshot.warrants.filterMap fun b =>
    if a.id < b.id && state.supports.contains a.id && state.supports.contains b.id then
      match boundClause p clauses a, boundClause p clauses b with
      | some ac, some bc => assessConflict p overlap ac bc a.id b.id
      | _, _ => none
    else none

structure ReleaseReview (p : ProfileOps) (overlap : OverlapOps p) where
  state : RuntimeState
  findings : List (ConflictFinding p overlap)

def ReleaseReview.allowed (review : ReleaseReview p overlap) : Bool :=
  !(review.findings.any fun finding => finding.witness.isSome)

def reviewRelease (p : ProfileOps) (overlap : OverlapOps p)
    (clauses : List (Clause p)) (state : RuntimeState) : ReleaseReview p overlap :=
  ⟨state, conflictFindings p overlap clauses state⟩
end GP50.Semantic
