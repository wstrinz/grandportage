-- Phase1: a typed proof obligation, not an implemented fold or proved theorem.
-- No Mathlib, no sorry, and no axiom declaring a fold sound.
structure Profile where
  Ctx : Type
  Scope : Type
  Stmt : Type
  Receipt : Type
  mem : Ctx → Scope → Prop
  le : Scope → Scope → Bool
  le_sound : ∀ a b c, le a b = true → mem c a → mem c b
  Holds : Stmt → Ctx → Prop
  contra : Stmt → Stmt → Bool
  contra_sound : ∀ a b c, contra a b = true → Holds a c → Holds b c → False
def Means (P : Profile) (stmt : P.Stmt) (scope : P.Scope) : Prop :=
  ∀ c, P.mem c scope → P.Holds stmt c
structure Claim (P : Profile) where
  stmt : P.Stmt
  scope : P.Scope
structure Binding where
  statementHash : String
  scopeHash : String
  modelHash : String
  inputs : List String
  authorityVersionHash : String
structure Checker (P : Profile) where
  id : Nat
  version : String
  valid : P.Stmt → P.Receipt → Binding → Bool
  reach : P.Receipt → P.Scope
def CheckerSound (P : Profile) (k : Checker P) : Prop :=
  ∀ stmt receipt binding, k.valid stmt receipt binding = true →
    Means P stmt (k.reach receipt)
structure Rule (P : Profile) where
  id : Nat
  version : String
  premises : List (Claim P)
  conclusion : Claim P
  sideValid : P.Receipt → Binding → Bool
def RuleSound (P : Profile) (r : Rule P) : Prop :=
  ∀ receipt binding, r.sideValid receipt binding = true →
    (∀ premise ∈ r.premises, Means P premise.stmt premise.scope) →
    Means P r.conclusion.stmt r.conclusion.scope
structure Log (P : Profile) where
  admittedCheckers : List (Checker P)
  admittedRules : List (Rule P)
  -- Typed event schema/decoder, identities and closure domain remain proposed.
  eventBytes : List String
structure ImplementationSlot (P : Profile) where
  State : Type
  fold : Log P → State
  held : State → Claim P → Bool
-- Instantiate ONLY with the actual Phase2 executable fold and held predicate.
-- An arbitrary slot need not satisfy this goal; we do not prove it for all slots.
def heldSoundStatement (P : Profile) (impl : ImplementationSlot P) (log : Log P) : Prop :=
  (∀ k ∈ log.admittedCheckers, CheckerSound P k) →
  (∀ r ∈ log.admittedRules, RuleSound P r) →
  ∀ cl, impl.held (impl.fold log) cl = true → Means P cl.stmt cl.scope
-- K2's universal-scope implication is already independent of statement polarity.
theorem weakening_sound (P : Profile) (stmt : P.Stmt) (a b : P.Scope)
    (h : P.le a b = true) (hb : Means P stmt b) : Means P stmt a := by
  intro c hc
  exact hb c (P.le_sound a b c h hc)
#check heldSoundStatement
#print axioms weakening_sound
