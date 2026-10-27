import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Split-complex numbers and their idempotent decomposition

The readable name `SplitComplex` specializes Mathlib's quadratic algebra to
`j² = 1`. Its arithmetic, module and algebra structures are inherited. The
indefinite quadratic norm is not a metric norm. The independent coordinate
maps to `ℝ × ℝ` give the nontrivial idempotent decomposition.
-/

namespace Algebra

abbrev SplitComplex := QuadraticAlgebra ℝ 1 0

namespace SplitComplex

open scoped QuadraticAlgebra

/-- The distinguished split generator. -/
def j : SplitComplex := ⟨0, 1⟩

@[coe] def ofReal (r : ℝ) : SplitComplex := ⟨r, 0⟩
instance : Coe ℝ SplitComplex := ⟨ofReal⟩

@[simp] theorem j_sq : j * j = 1 := by ext <;> simp [j]
theorem j_ne_one : j ≠ 1 := by intro h; have := congrArg QuadraticAlgebra.re h; simp [j] at this
theorem j_ne_neg_one : j ≠ -1 := by intro h; have := congrArg QuadraticAlgebra.re h; simp [j] at this

/-- The authored coordinate formula for the indefinite norm. -/
def norm (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

theorem norm_eq_quadratic_norm (z : SplitComplex) : norm z = QuadraticAlgebra.norm z := by
  simp [norm, QuadraticAlgebra.norm_def, pow_two]

theorem norm_mul (z w : SplitComplex) : norm (z * w) = norm z * norm w := by
  simp only [norm_eq_quadratic_norm, map_mul]

/-- Conjugation retains its coordinate formula and agrees with the standard involution. -/
def conj (z : SplitComplex) : SplitComplex := ⟨z.re, -z.im⟩

@[simp] theorem conj_eq_star (z : SplitComplex) : conj z = star z := by ext <;> simp [conj]

theorem isUnit_iff_norm_ne_zero (z : SplitComplex) : IsUnit z ↔ norm z ≠ 0 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, ← norm_eq_quadratic_norm, isUnit_iff_ne_zero]

theorem norm_j_negative : norm j < 0 := by norm_num [norm, j]

theorem mul_conj (z : SplitComplex) : z * conj z = norm z := by
  change z * conj z = algebraMap ℝ SplitComplex (norm z)
  rw [conj_eq_star, norm_eq_quadratic_norm]
  exact (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm

noncomputable def idempotentPos : SplitComplex := ⟨1/2, 1/2⟩
noncomputable def idempotentNeg : SplitComplex := ⟨1/2, -1/2⟩

theorem idempotentPos_sq : idempotentPos * idempotentPos = idempotentPos := by
  ext <;> norm_num [idempotentPos]

theorem idempotentNeg_sq : idempotentNeg * idempotentNeg = idempotentNeg := by
  ext <;> norm_num [idempotentNeg]

theorem idempotent_orthogonal : idempotentPos * idempotentNeg = 0 := by
  ext <;> norm_num [idempotentPos, idempotentNeg]

theorem idempotent_sum : idempotentPos + idempotentNeg = 1 := by
  ext <;> norm_num [idempotentPos, idempotentNeg]

theorem zero_divisor_example : (1 + j) * (1 - j) = 0 := by ext <;> simp [j]

theorem has_zero_divisors : ∃ a b : SplitComplex, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  refine ⟨1 + j, 1 - j, ?_, ?_, zero_divisor_example⟩
  all_goals intro h; have := congrArg QuadraticAlgebra.re h; simp [j] at this

/-- Idempotent coordinates, rather than the raw pair `(re, im)`. -/
noncomputable def toRealProd : SplitComplex →+* ℝ × ℝ where
  toFun z := (z.re + z.im, z.re - z.im)
  map_one' := by simp
  map_mul' z w := by ext <;> simp <;> ring
  map_zero' := by simp
  map_add' z w := by ext <;> simp <;> ring

/-- Reconstruct a split-complex number from its idempotent coordinates. -/
private noncomputable def fromRealCoordinates (p : ℝ × ℝ) : SplitComplex :=
  ⟨(p.1 + p.2) / 2, (p.1 - p.2) / 2⟩

noncomputable def equivRealProd : SplitComplex ≃+* ℝ × ℝ where
  toFun := toRealProd
  invFun := fromRealCoordinates
  left_inv z := by ext <;> simp [toRealProd, fromRealCoordinates]
  right_inv p := by ext <;> simp [toRealProd, fromRealCoordinates] <;> ring
  map_mul' := toRealProd.map_mul'
  map_add' := toRealProd.map_add'

noncomputable def ofRealProd : ℝ × ℝ →+* SplitComplex := equivRealProd.symm.toRingHom

/-- The two authored idempotents are the two product-coordinate projectors. -/
theorem idempotent_coordinates :
    equivRealProd idempotentPos = (1, 0) ∧ equivRealProd idempotentNeg = (0, 1) := by
  constructor <;> ext <;> norm_num [equivRealProd, toRealProd, idempotentPos, idempotentNeg]

end SplitComplex
end Algebra
