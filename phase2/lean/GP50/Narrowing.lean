import GP50.Semantics
import GP50.Runtime
namespace GP50.Semantic
def boundClause (p : ProfileOps) (clauses : List (Clause p)) (w : Warrant) : Option (Clause p) :=
  if (clauses.map (·.key)).eraseDups.length != clauses.length then none else
    clauses.find? fun c => c.key == w.claim && c.version == w.version && c.binding == w.binding

def checkNarrow (p : ProfileOps) (dest source : Clause p) : Bool :=
  p.same dest.stmt source.stmt && (p.le dest.scope source.scope &&
    (dest.binding.statementHash == source.binding.statementHash &&
     dest.binding.modelHash == source.binding.modelHash &&
     dest.binding.inputHashes == source.binding.inputHashes &&
     dest.binding.kernelVersion == source.binding.kernelVersion))

-- Runtime dependency closure, rather than this local check, requires source support.
def acceptsNarrow (p : ProfileOps) (clauses : List (Clause p)) (dest source : Warrant) : Bool :=
  match boundClause p clauses dest, boundClause p clauses source with
  | some a, some b => checkNarrow p a b
  | _, _ => false

def withNarrowing (p : ProfileOps) (clauses : List (Clause p)) (base : Admission) : Admission :=
  {base with narrow := acceptsNarrow p clauses}
end GP50.Semantic
