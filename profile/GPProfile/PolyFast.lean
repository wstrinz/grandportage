import HexMvPoly

/-!
Compiled twins for the Hex arithmetic the checkers run (ud22 performance, 2026-10-10). Each is an
`@[csimp]` theorem `@f = @f'`: code compiled after this module runs `f'`, while every definition,
statement and proof still names `f`. Nothing here is trusted beyond the equality it proves.

- `Mono.lex` compares exponent vectors as lists (`List.compareLex` on `toList`), allocating two lists
  on every comparison in the term maps; `monoLexFast` compares the arrays in place.
- `Mono.mul` builds its sum through `List.ofFn`; `monoMulFast` adds the arrays elementwise. Hex's
  compiled `MvPoly.mul` calls `Mono.mul` directly, so the twin reaches it through a twin of the `Mul`
  instance, whose product is `MvPoly.mul` with `monoMulFast` (`mul_inst_eq_fast`).
-/

namespace GPProfile
open Hex

/-- `Mono.lex`, comparing the exponent arrays without building lists. -/
def monoLexFast {n : Nat} (a b : Mono n) : Ordering := a.toArray.compareLex compare b.toArray

@[csimp] theorem mono_lex_eq_fast : @Mono.lex = @monoLexFast := by
  funext n a b
  simp only [Mono.lex, monoLexFast, Array.compareLex_eq_compareLex_toList]
  rfl

/-- `Mono.mul`, adding the exponent arrays elementwise. -/
def monoMulFast {n : Nat} (a b : Mono n) : Mono n := Vector.zipWith (· + ·) a b

@[csimp] theorem mono_mul_eq_fast : @Mono.mul = @monoMulFast := by
  funext n a b
  apply Vector.ext
  intro i hi
  simp [Mono.mul, monoMulFast, Hex.Vector.ofFn'_eq_ofFn]

universe u

/-- `MvPoly.mul` with `monoMulFast`: the same fold, term for term. -/
def mvMulFast {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] [Add R] [Mul R] [Zero R] [BEq R] [LawfulBEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc mp cp => q.foldTerms (fun acc mq cq => acc.addMonomial (monoMulFast mp mq) (cp * cq)) acc) 0

theorem mvMulFast_eq {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] [Add R] [Mul R] [Zero R] [BEq R] [LawfulBEq R] (p q : MvPoly n R cmp) :
    mvMulFast p q = MvPoly.mul p q := by
  simp only [mvMulFast, MvPoly.mul, ← mono_mul_eq_fast]

/-- Hex's `Mul` instance, multiplying by `mvMulFast`. -/
@[reducible] def instMulFast {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] [Add R] [Mul R] [Zero R] [BEq R] [LawfulBEq R] : Mul (MvPoly n R cmp) :=
  ⟨mvMulFast⟩

@[csimp] theorem mul_inst_eq_fast : @MvPoly.instMulOfAddOfLawfulBEq = @instMulFast := by
  funext n R cmp _ _ _ _ _ _ _
  simp only [MvPoly.instMulOfAddOfLawfulBEq, instMulFast]
  congr
  funext p q
  exact (mvMulFast_eq p q).symm

end GPProfile
