import GP50.Cover
import GP50.ScopedSpan
namespace GP50.CoveredSpan
def coverage : Semantic.Coverage ScopedSpan.profile where
  covers destination branches := destination.all fun ctx => branches.any (·.contains ctx)
  sound := by
    intro destination branches ctx accepted present
    rcases List.any_eq_true.mp ((List.all_eq_true.mp accepted) ctx present) with
      ⟨branch, registered, member⟩
    exact ⟨branch, registered, List.contains_iff_mem.mp member⟩
structure Rule where
  name : String
  destination : Nat
  branches : List Nat
def accepts (rows : List ScopedSpan.Row) (rules : List Rule)
    (w : Warrant) (premises : List Warrant) (name : String) : Bool :=
  (rules.map (·.name)).eraseDups.length == rules.length &&
  rules.any (fun rule => rule.name == name && rule.destination == w.claim &&
    rule.branches == premises.map (·.claim)) &&
  Semantic.acceptsCover ScopedSpan.profile coverage (rows.map ScopedSpan.semantic) w premises
def baseAdmission (rows : List ScopedSpan.Row) (receipts : List Span.Receipt)
    (rules : List Rule) : Admission :=
  {Span.admission (rows.map (·.algebra)) receipts with rule := accepts rows rules}
def admission (rows : List ScopedSpan.Row) (receipts : List Span.Receipt)
    (rules : List Rule) : Admission :=
  Semantic.withNarrowing ScopedSpan.profile (rows.map ScopedSpan.semantic)
    (baseAdmission rows receipts rules)
end GP50.CoveredSpan
