import GP50.CoverProofs
import GP50.ScopedSpan
namespace CoverControls
open GP50 GP50.Semantic

private def finiteCoverage : Coverage ScopedSpan.profile where
  covers destination branches := destination.all fun ctx => branches.any fun branch => branch.contains ctx
  sound := by
    intro destination branches ctx accepted present
    have covered := (List.all_eq_true.mp accepted) ctx present
    rcases List.any_eq_true.mp covered with ⟨branch, branchPresent, inBranch⟩
    exact ⟨branch, branchPresent, List.contains_iff_mem.mp inBranch⟩

private def binding (key : Nat) : Binding :=
  ⟨"object-A-x", s!"scope-{key}", "Q[x]", ["x"], "span-test-stub", 1, 1⟩
private def row (key : Nat) (scope : List Nat) : ScopedSpan.Row :=
  ⟨⟨key, 1, binding key, [[(1,1)]], [(1,1)]⟩, "A", scope⟩
private def destination : ScopedSpan.Row := row 1 [1,2]
private def left : ScopedSpan.Row := row 2 [1]
private def right : ScopedSpan.Row := row 3 [2]
private def rows : List ScopedSpan.Row := [destination,left,right]
private def branchReceipt (r : ScopedSpan.Row) : Span.Receipt :=
  ⟨s!"root-{r.algebra.key}", r.algebra.key, 1, r.algebra.binding, [[(0,1)]]⟩
private def receipts : List Span.Receipt := [branchReceipt left, branchReceipt right]
private def branchW (r : ScopedSpan.Row) (id : Nat) : Warrant :=
  ⟨id, r.algebra.key, 1, r.algebra.binding, .receipt s!"root-{r.algebra.key}"⟩
private def destW (r : ScopedSpan.Row := destination) (deps : List Nat := [20,30]) : Warrant :=
  ⟨10, r.algebra.key, 1, r.algebra.binding, .derived deps "cover-test-seam"⟩
private def wire (ws : List Warrant) : List Event :=
  ws.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩, .warrant w]

-- Explicit runtime rule TEST SEAM. This is not production rule routing or a corpus pass.
private def ruleTestSeam (registry : List ScopedSpan.Row) (roots : List Span.Receipt) : Admission :=
  {Span.admission (registry.map ScopedSpan.Row.algebra) roots with
    rule := fun w premises tag => tag == "cover-test-seam" &&
      acceptsCover ScopedSpan.profile finiteCoverage (registry.map ScopedSpan.semantic) w premises}
private def stateMatches (registry : List ScopedSpan.Row) (roots : List Span.Receipt)
    (events : List Event) (claims supports : List Nat) : Bool :=
  match GP50.fold (ruleTestSeam registry roots) events with
  | .error _ => false
  | .ok state => state.claims == claims && canonicalIds state.supports == supports
private def checked (dest : ScopedSpan.Row) (branches : List ScopedSpan.Row) : Bool :=
  checkCover ScopedSpan.profile finiteCoverage (ScopedSpan.semantic dest)
    (branches.map ScopedSpan.semantic)
private def check (counter : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {label}")
  counter.modify (· + 1)
  IO.println s!"PASS: {label}"

-- The actual finite-list checker carries a proved contract, not a success flag.
example (destination : List Nat) (branches : List (List Nat)) (ctx : Nat)
    (accepted : finiteCoverage.covers destination branches = true) (present : ctx ∈ destination) :
    ∃ branch ∈ branches, ctx ∈ branch :=
  finiteCoverage.sound destination branches ctx accepted present

example (dest : Clause ScopedSpan.profile) (branches : List (Clause ScopedSpan.profile))
    (accepted : checkCover ScopedSpan.profile finiteCoverage dest branches = true)
    (truth : ∀ branch ∈ branches, Means ScopedSpan.profile branch.stmt branch.scope) :
    Means ScopedSpan.profile dest.stmt dest.scope :=
  checked_cover_sound ScopedSpan.profile finiteCoverage dest branches accepted truth

example (ctx : Nat) : ¬ScopedSpan.profile.mem ctx ([] : List Nat) := by
  simp [ScopedSpan.profile]

def main : IO Unit := do
  let counter ← IO.mkRef 0
  let ensure := check counter
  let lw := branchW left 20
  let rw := branchW right 30
  let dw := destW
  let events := wire [dw,lw,rw]
  ensure "actual finite coverage complete" (checked destination [left,right])
  ensure "missing context makes finite cover incomplete" (!checked destination [left])
  ensure "overlapping duplicate branch scopes preserve coverage"
    (checked destination [left,right,left])
  ensure "empty branch list cannot cover inhabited destination" (!checked destination [])
  ensure "branch scope may extend beyond destination" (checked destination [row 2 [1,2,3]])
  ensure "empty branch cannot cover inhabited destination" (!checked destination [row 2 []])
  ensure "finite coverage detects an unlisted destination context"
    (!checked (row 1 [1,2,3]) [left,right])
  ensure "coverage branch order is immaterial" (checked destination [right,left])
  ensure "actual bound premise clauses pass acceptsCover"
    (acceptsCover ScopedSpan.profile finiteCoverage (rows.map ScopedSpan.semantic) dw [lw,rw])
  ensure "test seam both actual Rat branch roots support cover"
    (stateMatches rows receipts events [1,2,3] [10,20,30])
  ensure "test seam incomplete cover never becomes held"
    (stateMatches rows receipts (wire [destW destination [20],lw,rw]) [2,3] [20,30])
  ensure "coverage alone cannot replace refused branch receipt"
    (stateMatches rows [branchReceipt left] events [2] [20])
  ensure "physical missing branch warrant prevents rule"
    (stateMatches rows receipts (wire [dw,lw]) [2] [20])
  ensure "failed branch attempt never becomes support"
    (stateMatches rows receipts (wire [dw,lw,{rw with evidence := .attempt .failed}]) [2] [20])
  ensure "branch retraction invalidates cover destination"
    (stateMatches rows receipts (events ++ [.retract 30]) [2] [20])
  ensure "independent same-claim support cannot replace exact retracted branch ID"
    (stateMatches rows receipts (events ++ wire [branchW right 31] ++ [.retract 30]) [2,3] [20,31])
  ensure "test seam tag is exact"
    (stateMatches rows receipts (wire [{dw with evidence := .derived [20,30] "unknown"},lw,rw]) [2,3] [20,30])
  ensure "one-root cycle cannot bootstrap its unsupported branch"
    (stateMatches rows receipts (wire [dw,{lw with evidence := .derived [10] "cover-test-seam"},rw])
      [3] [30])
  ensure "no-root cover cycle cannot bootstrap authority"
    (stateMatches rows [] (wire [dw,{lw with evidence := .derived [10] "cover-test-seam"},
      {rw with evidence := .derived [10] "cover-test-seam"}]) [] [])
  ensure "test seam event reversal preserves support"
    (stateMatches rows receipts events.reverse [1,2,3] [10,20,30])
  ensure "test seam exact duplicate events preserve support"
    (stateMatches rows receipts (events ++ events) [1,2,3] [10,20,30])
  for (label, changed) in
      [("selected object", {right with object := "B"}),
       ("actual target/generator polynomials", {right with algebra := {right.algebra with
         generators := [[(2,1)]], target := [(2,1)]}}),
       ("actual generator encoding", {right with algebra := {right.algebra with
         generators := [[(1,1),(2,0)]]}}),
       ("statement identity", {right with algebra := {right.algebra with
         binding := {right.algebra.binding with statementHash := "other"}}}),
       ("selected model identity", {right with algebra := {right.algebra with
         binding := {right.algebra.binding with modelHash := "other"}}}),
       ("input identities", {right with algebra := {right.algebra with
         binding := {right.algebra.binding with inputHashes := ["other"]}}}),
       ("kernel epoch", {right with algebra := {right.algebra with
         binding := {right.algebra.binding with kernelVersion := 2}}})] do
    ensure s!"actual checkCover rejects {label}" (!checked destination [left,changed])
    ensure s!"test seam rejects {label} despite independently replayed branch roots"
      (stateMatches [destination,left,changed] [branchReceipt left,branchReceipt changed]
        (wire [dw,lw,branchW changed 30]) [2,3] [20,30])
  ensure "missing destination registration refuses acceptsCover"
    (!acceptsCover ScopedSpan.profile finiteCoverage ([left,right].map ScopedSpan.semantic) dw [lw,rw])
  ensure "missing branch registration refuses acceptsCover"
    (!acceptsCover ScopedSpan.profile finiteCoverage ([destination,left].map ScopedSpan.semantic) dw [lw,rw])
  ensure "duplicate clause keys disable acceptsCover"
    (!acceptsCover ScopedSpan.profile finiteCoverage ((rows ++ [left]).map ScopedSpan.semantic) dw [lw,rw])
  ensure "stale destination binding/version refused"
    (!acceptsCover ScopedSpan.profile finiteCoverage (rows.map ScopedSpan.semantic) {dw with version := 2} [lw,rw])
  ensure "stale source binding/version refused"
    (!acceptsCover ScopedSpan.profile finiteCoverage (rows.map ScopedSpan.semantic) dw [lw,{rw with version := 2}])
  ensure "coverage of empty scope needs no branch"
    (checked {destination with scope := []} [])
  let empty := {destination with scope := [], algebra := {destination.algebra with
    generators := [], target := [(0,1)]}}
  ensure "empty-scope test seam holds vacuous Means without a Rat receipt"
    (stateMatches [empty] [] (wire [destW empty []]) [1] [10])
  ensure "inhabited destination with no branches has no support"
    (stateMatches [destination] [] (wire [destW destination []]) [] [])
  IO.println s!"Cover: {← counter.get} native controls passed; explicit finite contexts and labeled runtime rule test seam."
#print axioms finiteCoverage
end CoverControls
def main : IO Unit := CoverControls.main
