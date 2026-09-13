import GrandPortage.ExpressionTransport
namespace GrandPortage.SemanticLoss
open CertificateInterpreter
/-- The equivalence kernel of an observer; not a set of unlicensed claims. -/
def Kernel {A B : Type} (observe : A → B) (a b : A) : Prop := observe a = observe b
/-- Two states distinguished before a map but identified by its target observer. -/
def Collapsed {A B O P : Type} (f : A → B) (before : A → O) (after : B → P)
    (a b : A) : Prop := ¬ Kernel before a b ∧ Kernel (fun x => after (f x)) a b
/-- For the integer-to-Gaussian map and exact-value observers, no pair collapses. -/
theorem integer_gaussian_kernel (a b : Int) :
    Kernel integerToGaussian.map a b ↔ a = b := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    cases h
    rfl

theorem integer_gaussian_no_loss (a b : Int) :
    ¬ Collapsed integerToGaussian.map id id a b := by
  intro h
  exact h.1 ((integer_gaussian_kernel a b).mp h.2)
end GrandPortage.SemanticLoss
