import GP50.Narrowing
namespace GP50.Semantic
universe u

-- Executable coverage check; certifies membership coverage, never branch truth or existence.
structure CoverOps (p : ProfileOps) where
  covers : p.Scope → List p.Scope → Bool
structure Coverage (p : Profile.{u}) extends CoverOps p.toProfileOps where
  sound : ∀ destination branches ctx, covers destination branches = true →
    p.mem ctx destination → ∃ branch ∈ branches, p.mem ctx branch
instance (p : Profile.{u}) : CoeOut (Coverage p) (CoverOps p.toProfileOps) := ⟨Coverage.toCoverOps⟩

def checkCover (p : ProfileOps) (coverage : CoverOps p)
    (destination : Clause p) (branches : List (Clause p)) : Bool :=
  branches.all (fun branch => p.same destination.stmt branch.stmt &&
    (destination.binding.statementHash == branch.binding.statementHash &&
     destination.binding.modelHash == branch.binding.modelHash &&
     destination.binding.inputHashes == branch.binding.inputHashes &&
     destination.binding.kernelVersion == branch.binding.kernelVersion)) &&
  coverage.covers destination.scope (branches.map (·.scope))

-- All premises are bound here; support for their IDs remains Runtime's obligation.
def acceptsCover (p : ProfileOps) (coverage : CoverOps p) (clauses : List (Clause p))
    (destination : Warrant) (premises : List Warrant) : Bool :=
  match boundClause p clauses destination, premises.mapM (boundClause p clauses) with
  | some dest, some branches => checkCover p coverage dest branches
  | _, _ => false

end GP50.Semantic
