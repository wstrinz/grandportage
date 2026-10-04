import GP50.Events
namespace GP50.Semantic
universe u

-- Executable, Mathlib-free profile operations. Kernel executables take only these.
structure ProfileOps where
  Stmt : Type
  Scope : Type
  same : Stmt → Stmt → Bool
  same_sound : ∀ a b, same a b = true → a = b
  le : Scope → Scope → Bool
  contra : Stmt → Stmt → Bool

-- Semantic profile: contexts are models in any universe (post-G2 handoff §1.3).
structure Profile extends ProfileOps where
  Ctx : Type u
  mem : Ctx → Scope → Prop
  Holds : Stmt → Ctx → Prop
  le_sound : ∀ a b c, le a b = true → mem c a → mem c b
  contra_sound : ∀ a b c, contra a b = true → Holds a c → Holds b c → False

instance : CoeOut Profile.{u} ProfileOps := ⟨Profile.toProfileOps⟩

def Means (p : Profile.{u}) (stmt : p.Stmt) (scope : p.Scope) : Prop :=
  ∀ c, p.mem c scope → p.Holds stmt c

-- Statement data includes selected objects; scope restriction cannot alter it.
structure Clause (p : ProfileOps) where
  key : Nat
  version : Nat
  binding : Binding
  stmt : p.Stmt
  scope : p.Scope
end GP50.Semantic
