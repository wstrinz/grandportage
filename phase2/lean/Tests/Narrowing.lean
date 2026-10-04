import GP50.NarrowingProofs
import GP50.BoundReplayProofs
namespace NarrowingControls
open GP50
private def binding : Binding :=
  {statementHash := "object-A-span-x", scopeHash := "wide", modelHash := "Q[x]",
   inputHashes := ["x"], authority := "test-stub", authorityVersion := 1, kernelVersion := 1}
private def profile : Semantic.Profile where
  Stmt := String × (List PolyStub.Polynomial × PolyStub.Polynomial)
  Scope := List Nat
  Ctx := Nat
  same a b := decide (a = b)
  same_sound := by intro a b h; exact of_decide_eq_true h
  mem c s := c ∈ s
  le a b := a.all (b.contains)
  le_sound := by
    intro a b c accepted present
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp accepted) c present)
  Holds statement _ := Span.FormalSpan
    {key := 0, version := 1, binding, generators := statement.2.1, target := statement.2.2}
  contra _ _ := false
  contra_sound := by intros; contradiction
private def source : Semantic.Clause profile :=
  {key := 1, version := 1, binding, stmt := ("A", ([[(1,1)]], [(1,1)])), scope := [1,2]}
private def dest : Semantic.Clause profile :=
  {source with key := 2, scope := [1], binding := {binding with scopeHash := "tight"}}
private def sourceW : Warrant :=
  {id := 10, claim := 1, version := 1, binding, evidence := .receipt "root"}
private def destW (clause : Semantic.Clause profile) : Warrant :=
  {id := 11, claim := clause.key, version := clause.version, binding := clause.binding, evidence := .narrow 10}
private def base : Admission := Span.admission
  [{key := 1, version := 1, binding, generators := [[(1,1)]], target := [(1,1)]}]
  [{name := "root", claim := 1, version := 1, binding, cofactors := [[(0,1)]]}]
private def events (clause : Semantic.Clause profile) (w : Warrant := sourceW) : List Event :=
  [.current {claim := 1, version := 1, binding},
   .current {claim := clause.key, version := clause.version, binding := clause.binding},
   .warrant w, .warrant (destW clause)]
private def claims (registry : List (Semantic.Clause profile)) (log : List Event) : List Nat :=
  match fold (Semantic.withNarrowing profile registry base) log with
  | .error _ => [] | .ok state => state.claims
private def check (count : IO.Ref Nat) (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError s!"FAILED: {label}")
  count.modify (· + 1)
def main : IO Unit := do
  let count ← IO.mkRef 0
  let ensure := check count
  ensure "actual rational root supports exact-statement narrowing"
    (claims [source,dest] (events dest) == [1,2])
  for (label, changed) in
    [("selected object", {dest with stmt := ("B", dest.stmt.2)}),
     ("target", {dest with stmt := ("A", (dest.stmt.2.1, [(2,1)]))}),
     ("scope expansion", {dest with scope := [1,2,3]}),
     ("statement hash", {dest with binding := {dest.binding with statementHash := "other"}}),
     ("model", {dest with binding := {dest.binding with modelHash := "other"}}),
     ("inputs", {dest with binding := {dest.binding with inputHashes := ["other"]}}),
     ("epoch", {dest with binding := {dest.binding with kernelVersion := 2}})] do
    ensure label (claims [source,changed] (events changed) == [1])
  ensure "empty scope still needs actual source support"
    (claims [source,{dest with scope := []}] (events {dest with scope := []}) == [1,2])
  ensure "failed source cannot support narrowing"
    (claims [source,dest] (events dest {sourceW with evidence := .attempt .failed}) == [])
  ensure "retracted source cannot support narrowing"
    (claims [source,dest] (events dest ++ [.retract 10]) == [])
  ensure "duplicate clause identities disable narrowing"
    (claims [source,source,dest] (events dest) == [1])
  ensure "missing destination registration disables narrowing"
    (claims [source] (events dest) == [1])
  ensure "a stale exact statement binding is refused"
    (!Semantic.acceptsNarrow profile [source,dest]
      {destW dest with version := 2} sourceW)
  IO.println s!"Narrowing: {← count.get} component controls passed; explicit finite scopes on formal Rat span stub."
end NarrowingControls

def main : IO Unit := NarrowingControls.main
