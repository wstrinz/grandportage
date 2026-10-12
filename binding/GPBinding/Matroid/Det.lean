import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Module.Pi

/-!
3×3 determinants for the frame theorem (ENCODING-FRAME): the encoder's expansion, how it changes
under a linear map and under scaling, and the Cramer map that sends a basis to the standard frame.
-/

namespace GPBinding.Matroid

variable {K : Type*} [Field K]

/-- The determinant of three column vectors, in the encoder's expansion. -/
def det3 (u v w : Fin 3 → K) : K :=
  u 0 * (v 1 * w 2 - w 1 * v 2) - v 0 * (u 1 * w 2 - w 1 * u 2) + w 0 * (u 1 * v 2 - v 1 * u 2)

def dot (r y : Fin 3 → K) : K := r 0 * y 0 + r 1 * y 1 + r 2 * y 2

/-- The linear map with rows `r₀, r₁, r₂`. -/
def apply3 (r₀ r₁ r₂ y : Fin 3 → K) : Fin 3 → K := ![dot r₀ y, dot r₁ y, dot r₂ y]

theorem det3_apply3 (r₀ r₁ r₂ y₁ y₂ y₃ : Fin 3 → K) :
    det3 (apply3 r₀ r₁ r₂ y₁) (apply3 r₀ r₁ r₂ y₂) (apply3 r₀ r₁ r₂ y₃) = det3 r₀ r₁ r₂ * det3 y₁ y₂ y₃ := by
  simp only [det3, apply3, dot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem det3_smul (a b c : K) (u v w : Fin 3 → K) :
    det3 (a • u) (b • v) (c • w) = a * b * c * det3 u v w := by
  simp only [det3, Pi.smul_apply, smul_eq_mul]
  ring

/-- The cross product: `dot (cross v w) y = det3 y v w`. -/
def cross (v w : Fin 3 → K) : Fin 3 → K := ![v 1 * w 2 - w 1 * v 2, w 0 * v 2 - v 0 * w 2, v 0 * w 1 - w 0 * v 1]

theorem dot_cross (v w y : Fin 3 → K) : dot (cross v w) y = det3 y v w := by
  simp only [dot, cross, det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem det3_cross (v₀ v₁ v₂ : Fin 3 → K) :
    det3 (cross v₁ v₂) (cross v₂ v₀) (cross v₀ v₁) = det3 v₀ v₁ v₂ ^ 2 := by
  simp only [det3, cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The Cramer map of a basis: `y ↦ (det3 y v₁ v₂, det3 v₀ y v₂, det3 v₀ v₁ y)`. -/
def cramer (v₀ v₁ v₂ : Fin 3 → K) (y : Fin 3 → K) : Fin 3 → K :=
  apply3 (cross v₁ v₂) (cross v₂ v₀) (cross v₀ v₁) y

theorem cramer_apply (v₀ v₁ v₂ y : Fin 3 → K) :
    cramer v₀ v₁ v₂ y = ![det3 y v₁ v₂, det3 v₀ y v₂, det3 v₀ v₁ y] := by
  simp only [cramer, apply3, dot_cross]
  congr 2
  · simp only [det3]; ring
  · congr 1; simp only [det3]; ring

theorem det3_cramer (v₀ v₁ v₂ y₁ y₂ y₃ : Fin 3 → K) :
    det3 (cramer v₀ v₁ v₂ y₁) (cramer v₀ v₁ v₂ y₂) (cramer v₀ v₁ v₂ y₃) =
      det3 v₀ v₁ v₂ ^ 2 * det3 y₁ y₂ y₃ := by
  rw [cramer, cramer, cramer, det3_apply3, det3_cross]

/-- Swapping two columns negates the determinant; zero-ness is invariant under permutations. -/
theorem det3_swap12 (u v w : Fin 3 → K) : det3 v u w = - det3 u v w := by simp only [det3]; ring
theorem det3_swap23 (u v w : Fin 3 → K) : det3 u w v = - det3 u v w := by simp only [det3]; ring
theorem det3_rot (u v w : Fin 3 → K) : det3 v w u = det3 u v w := by simp only [det3]; ring

theorem det3_self12 (u w : Fin 3 → K) : det3 u u w = 0 := by simp only [det3]; ring
theorem det3_self13 (u v : Fin 3 → K) : det3 u v u = 0 := by simp only [det3]; ring
theorem det3_self23 (u v : Fin 3 → K) : det3 u v v = 0 := by simp only [det3]; ring

end GPBinding.Matroid
