import GP50.Narrowing
import GP50.BoundReplayProofs
namespace GP50.ScopedSpan
-- Named test contexts restrict formal Rat identities; they are not fields or geometric regions.
def profile : Semantic.Profile where
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
  Holds statement _ := ∃ cofactors : List PolyStub.Polynomial,
    statement.2.1.length = cofactors.length ∧ ∀ exponent,
      ((statement.2.1.zip cofactors).map fun (g,q) =>
        PolyStub.coefficient (PolyStub.multiply g q) exponent).sum =
          PolyStub.coefficient statement.2.2 exponent
  contra _ _ := false
  contra_sound := by intros; contradiction

structure Row where
  algebra : Span.Clause
  object : String
  scope : List Nat

def semantic (row : Row) : Semantic.Clause profile :=
  ⟨row.algebra.key, row.algebra.version, row.algebra.binding,
    (row.object, (row.algebra.generators, row.algebra.target)), row.scope⟩

def admission (rows : List Row) (receipts : List Span.Receipt) : Admission :=
  Semantic.withNarrowing profile (rows.map semantic)
    (Span.admission (rows.map (·.algebra)) receipts)
end GP50.ScopedSpan
