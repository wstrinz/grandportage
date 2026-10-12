import Std.Sat.AIG.CNF
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.LawfulOperator

/-!
Propositional expressions and their circuit (M4 §3, the encoding route).

A census predicate grounds to a `PExpr` over edge and colour atoms (`GPCensus.Encode`). `compile`
builds Lean core's and-inverter graph from it, and `compile_denote` proves the circuit computes the
expression. Core's `AIG.toCNF` and its theorem `toCNF_equisat` then give the CNF whose LRAT
refutation GP checks, so the formula a solver refutes is the one Lean emitted.
-/

namespace GPCensus
open Std.Sat Std.Sat.AIG

inductive PExpr where
  | atom (v : Nat)
  | const (b : Bool)
  | not (e : PExpr)
  | and (x y : PExpr)
  | or (x y : PExpr)
  deriving Repr, Inhabited

def PExpr.eval (a : Nat → Bool) : PExpr → Bool
  | .atom v => a v
  | .const b => b
  | .not e => !e.eval a
  | .and x y => x.eval a && y.eval a
  | .or x y => x.eval a || y.eval a

theorem isPrefix_trans {d₁ d₂ d₃ : Array (Decl Nat)} (h₁ : IsPrefix d₁ d₂) (h₂ : IsPrefix d₂ d₃) :
    IsPrefix d₁ d₃ :=
  ⟨Nat.le_trans h₁.size_le h₂.size_le, fun idx h => by
    rw [h₂.idx_eq idx (Nat.lt_of_lt_of_le h h₁.size_le), h₁.idx_eq idx h]⟩

/-- The circuit of an expression, extending `aig`. -/
def compile (aig : AIG Nat) : PExpr → ExtendingEntrypoint aig
  | .atom v => ⟨aig.mkAtomCached v, LawfulOperator.le_size (f := mkAtomCached) aig v⟩
  | .const b => ⟨⟨aig, aig.mkConstCached b⟩, Nat.le_refl _⟩
  | .not e =>
    match compile aig e with
    | ⟨⟨aig₁, r⟩, h₁⟩ =>
      ⟨aig₁.mkNotCached r, Nat.le_trans h₁ (LawfulOperator.le_size (f := mkNotCached) aig₁ r)⟩
  | .and x y =>
    match compile aig x with
    | ⟨⟨aig₁, r₁⟩, h₁⟩ =>
      match compile aig₁ y with
      | ⟨⟨aig₂, r₂⟩, h₂⟩ =>
        let input : BinaryInput aig₂ := ⟨r₁.cast h₂, r₂⟩
        ⟨aig₂.mkAndCached input,
          Nat.le_trans (Nat.le_trans h₁ h₂) (LawfulOperator.le_size (f := mkAndCached) aig₂ input)⟩
  | .or x y =>
    match compile aig x with
    | ⟨⟨aig₁, r₁⟩, h₁⟩ =>
      match compile aig₁ y with
      | ⟨⟨aig₂, r₂⟩, h₂⟩ =>
        let input : BinaryInput aig₂ := ⟨r₁.cast h₂, r₂⟩
        ⟨aig₂.mkOrCached input,
          Nat.le_trans (Nat.le_trans h₁ h₂) (LawfulOperator.le_size (f := mkOrCached) aig₂ input)⟩

theorem compile_isPrefix (aig : AIG Nat) (e : PExpr) :
    IsPrefix aig.decls (compile aig e).val.aig.decls := by
  induction e generalizing aig with
  | atom v => exact LawfulOperator.isPrefix_aig (f := mkAtomCached) aig v
  | const b => exact IsPrefix.rfl
  | not e ih =>
    simp only [compile]
    exact isPrefix_trans (ih aig) (LawfulOperator.isPrefix_aig (f := mkNotCached) _ _)
  | and x y ihx ihy =>
    simp only [compile]
    exact isPrefix_trans (isPrefix_trans (ihx aig) (ihy _)) (LawfulOperator.isPrefix_aig (f := mkAndCached) _ _)
  | or x y ihx ihy =>
    simp only [compile]
    exact isPrefix_trans (isPrefix_trans (ihx aig) (ihy _)) (LawfulOperator.isPrefix_aig (f := mkOrCached) _ _)

/-- A reference survives extension of its graph by a prefix-preserving step. -/
theorem denote_cast_of_isPrefix {aig₁ aig₂ : AIG Nat} (r : Ref aig₁) (h : aig₁.decls.size ≤ aig₂.decls.size)
    (hp : IsPrefix aig₁.decls aig₂.decls) (assign : Nat → Bool) :
    ⟦aig₂, r.cast h, assign⟧ = ⟦⟨aig₁, r⟩, assign⟧ :=
  denote.eq_of_isPrefix ⟨aig₁, r⟩ aig₂ hp

theorem compile_denote (aig : AIG Nat) (e : PExpr) (assign : Nat → Bool) :
    ⟦(compile aig e).val, assign⟧ = e.eval assign := by
  induction e generalizing aig with
  | atom v => simp [compile, PExpr.eval, denote_mkAtom]
  | const b => simp [compile, PExpr.eval]
  | not e ih =>
    simp only [compile]
    rw [denote_mkNotCached, PExpr.eval, ← ih aig]
  | and x y ihx ihy =>
    simp only [compile]
    rw [denote_mkAndCached, denote_cast_of_isPrefix _ _ (compile_isPrefix _ y), PExpr.eval, ← ihx aig,
      ← ihy (compile aig x).val.aig]
  | or x y ihx ihy =>
    simp only [compile]
    rw [denote_mkOrCached, denote_cast_of_isPrefix _ _ (compile_isPrefix _ y), PExpr.eval, ← ihx aig,
      ← ihy (compile aig x).val.aig]

/-- The CNF of an expression: core's Tseitin translation of its circuit. -/
def PExpr.toCNF (e : PExpr) : CNF Nat := AIG.toCNF (compile AIG.empty e).val

/-- An unsatisfiable CNF means the expression is false under every assignment. -/
theorem PExpr.eval_false_of_unsat {e : PExpr} (h : e.toCNF.Unsat) (assign : Nat → Bool) :
    e.eval assign = false := by
  have hu := (AIG.toCNF_equisat _).mp h assign
  rwa [compile_denote] at hu

end GPCensus
