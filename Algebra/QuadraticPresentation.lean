import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Quadratic presentations of two-dimensional unital algebras

An actual basis `(1, e)` determines the coefficients of `e * e` and a
bijective algebra homomorphism from Mathlib's `QuadraticAlgebra`. A basis
containing the unit is then constructed from dimension two: the scalar line
has dimension one, so a nonscalar second vector exists and completes it.

The representation theorem assumes a field of scalars and an associative
unital algebra, without assuming that its multiplication is commutative. It
works in every characteristic. The parameters depend on the selected basis;
uniqueness and completing the square are separate classification questions.
The construction is mathematical and noncomputable, not an algorithm for
discovering an algebra's basis from an external presentation.
-/

set_option autoImplicit false

namespace Algebra.QuadraticPresentation

open Module
open scoped BigOperators

section GeneratorChange

variable {R : Type*} [CommRing R]

/-- Coefficients of the relation for `β = u + vω`. -/
def shiftedConstant (a b u v : R) : R := v ^ 2 * a - u ^ 2 - u * v * b

def shiftedLinear (b u v : R) : R := 2 * u + v * b

/-- An affine equivalence with explicit coefficient equalities. Keeping the
endpoints explicit preserves executable coordinate projections under transport. -/
def affineEquiv (a b c d u : R) (v : Rˣ)
    (constant : c = shiftedConstant a b u v) (linear : d = shiftedLinear b u v) :
    QuadraticAlgebra R c d ≃ₐ[R] QuadraticAlgebra R a b where
  toFun z := ⟨z.re + u * z.im, (v : R) * z.im⟩
  invFun z := ⟨z.re - u * (↑(v⁻¹) : R) * z.im, (↑(v⁻¹) : R) * z.im⟩
  left_inv z := by ext <;> simp [← mul_assoc]
  right_inv z := by ext <;> simp [← mul_assoc]
  map_mul' z w := by
    ext
    · change z.re * w.re + c * z.im * w.im +
        u * (z.re * w.im + z.im * w.re + d * z.im * w.im) =
        (z.re + u * z.im) * (w.re + u * w.im) + a * ((v : R) * z.im) * ((v : R) * w.im)
      generalize z.re = x, z.im = y, w.re = r, w.im = s
      rw [constant, linear]
      unfold shiftedConstant shiftedLinear
      ring
    · change (v : R) * (z.re * w.im + z.im * w.re + d * z.im * w.im) =
        (z.re + u * z.im) * ((v : R) * w.im) + ((v : R) * z.im) * (w.re + u * w.im) +
          b * ((v : R) * z.im) * ((v : R) * w.im)
      generalize z.re = x, z.im = y, w.re = r, w.im = s
      rw [linear]
      unfold shiftedLinear
      ring
  map_add' z w := by ext <;> simp [mul_add, add_assoc, add_left_comm]
  commutes' r := by ext <;> simp

/-- Invertible generator change `β = u + vω`, from its new presentation to the old one. -/
def changeGenerator (a b u : R) (v : Rˣ) :
    QuadraticAlgebra R (shiftedConstant a b u v) (shiftedLinear b u v) ≃ₐ[R]
      QuadraticAlgebra R a b := affineEquiv a b _ _ u v rfl rfl

@[simp] theorem changeGenerator_re (a b u : R) (v : Rˣ) (z) :
    (changeGenerator a b u v z).re = z.re + u * z.im := rfl

@[simp] theorem changeGenerator_im (a b u : R) (v : Rˣ) (z) :
    (changeGenerator a b u v z).im = (v : R) * z.im := rfl

/-- Trace and norm are observations of the algebraic value, not of its coordinates. -/
theorem changeGenerator_observations (a b u : R) (v : Rˣ) (z) :
    QuadraticAlgebra.trace (changeGenerator a b u v z) = QuadraticAlgebra.trace z ∧
      QuadraticAlgebra.norm (changeGenerator a b u v z) = QuadraticAlgebra.norm z := by
  constructor
  · change 2 * (z.re + u * z.im) + b * ((v : R) * z.im) =
      2 * z.re + shiftedLinear b u v * z.im
    unfold shiftedLinear
    ring
  · change (z.re + u * z.im) * (z.re + u * z.im) +
      b * (z.re + u * z.im) * ((v : R) * z.im) - a * ((v : R) * z.im) * ((v : R) * z.im) =
        z.re * z.re + shiftedLinear b u v * z.re * z.im - shiftedConstant a b u v * z.im * z.im
    unfold shiftedConstant shiftedLinear
    ring

theorem shifted_discriminant (a b u v : R) :
    shiftedLinear b u v ^ 2 + 4 * shiftedConstant a b u v = v ^ 2 * (b ^ 2 + 4 * a) := by
  unfold shiftedLinear shiftedConstant
  ring

end GeneratorChange

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]

/-- The constant coordinate of the square of the second basis vector. -/
noncomputable def squareConstant (basis : Basis (Fin 2) R A) : R :=
  basis.repr (basis 1 * basis 1) 0

/-- The linear coordinate of the square of the second basis vector. -/
noncomputable def squareLinear (basis : Basis (Fin 2) R A) : R :=
  basis.repr (basis 1 * basis 1) 1

theorem basis_coordinates (basis : Basis (Fin 2) R A) (unit : basis 0 = 1) (value : A) :
    basis.repr value 0 • (1 : A) + basis.repr value 1 • basis 1 = value := by
  simpa only [Fin.sum_univ_two, unit] using basis.sum_repr value

/-- The defining quadratic relation is obtained from basis coordinates. -/
theorem square_relation (basis : Basis (Fin 2) R A) (unit : basis 0 = 1) :
    basis 1 * basis 1 = squareConstant basis • (1 : A) + squareLinear basis • basis 1 :=
  (basis_coordinates basis unit (basis 1 * basis 1)).symm

/-- The universal property supplies the algebra map; its target is the
original algebra, not an independently assumed coordinate multiplication. -/
noncomputable def realize (basis : Basis (Fin 2) R A) (unit : basis 0 = 1) :
    QuadraticAlgebra R (squareConstant basis) (squareLinear basis) →ₐ[R] A :=
  QuadraticAlgebra.lift ⟨basis 1, square_relation basis unit⟩

theorem realize_apply (basis : Basis (Fin 2) R A) (unit : basis 0 = 1)
    (value : QuadraticAlgebra R (squareConstant basis) (squareLinear basis)) :
    realize basis unit value = value.re • (1 : A) + value.im • basis 1 := rfl

@[simp] theorem realize_repr_zero (basis : Basis (Fin 2) R A) (unit : basis 0 = 1)
    (value : QuadraticAlgebra R (squareConstant basis) (squareLinear basis)) :
    basis.repr (realize basis unit value) 0 = value.re := by
  rw [realize_apply, ← unit]
  simp

@[simp] theorem realize_repr_one (basis : Basis (Fin 2) R A) (unit : basis 0 = 1)
    (value : QuadraticAlgebra R (squareConstant basis) (squareLinear basis)) :
    basis.repr (realize basis unit value) 1 = value.im := by
  rw [realize_apply, ← unit]
  simp

theorem realize_injective (basis : Basis (Fin 2) R A) (unit : basis 0 = 1) :
    Function.Injective (realize basis unit) := by
  intro first second equal
  apply QuadraticAlgebra.ext
  · simpa using congrArg (fun value => basis.repr value 0) equal
  · simpa using congrArg (fun value => basis.repr value 1) equal

theorem realize_surjective (basis : Basis (Fin 2) R A) (unit : basis 0 = 1) :
    Function.Surjective (realize basis unit) := by
  intro value
  exact ⟨⟨basis.repr value 0, basis.repr value 1⟩, basis_coordinates basis unit value⟩

/-- A normalized actual basis gives an algebra equivalence with its quadratic
coordinate presentation. Both algebra operations are preserved by `lift`. -/
noncomputable def ofBasis (basis : Basis (Fin 2) R A) (unit : basis 0 = 1) :
    A ≃ₐ[R] QuadraticAlgebra R (squareConstant basis) (squareLinear basis) :=
  (AlgEquiv.ofBijective (realize basis unit)
    ⟨realize_injective basis unit, realize_surjective basis unit⟩).symm

theorem ofBasis_symm_apply (basis : Basis (Fin 2) R A) (unit : basis 0 = 1)
    (value : QuadraticAlgebra R (squareConstant basis) (squareLinear basis)) :
    (ofBasis basis unit).symm value = value.re • (1 : A) + value.im • basis 1 := rfl

theorem ofBasis_apply (basis : Basis (Fin 2) R A) (unit : basis 0 = 1) (value : A) :
    ofBasis basis unit value = ⟨basis.repr value 0, basis.repr value 1⟩ := by
  apply (ofBasis basis unit).symm.injective
  rw [AlgEquiv.symm_apply_apply, ofBasis_symm_apply]
  exact (basis_coordinates basis unit value).symm

/-! ## Constructing a unit basis from dimension two -/

variable (R A) in
theorem exists_nonscalar (dimension : Module.finrank R A = 2) :
    ∃ generator : A, generator ∉ (R ∙ (1 : A)) := by
  classical
  let : Nontrivial A := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank R A)
  have scalar_dimension : Module.finrank R (R ∙ (1 : A)) = 1 :=
    finrank_span_singleton one_ne_zero
  by_contra! allScalar
  have scalarLine : (R ∙ (1 : A)) = ⊤ := Submodule.eq_top_iff'.mpr allScalar
  rw [scalarLine, finrank_top, dimension] at scalar_dimension
  norm_num at scalar_dimension

/-- Any nonscalar element completes the unit to a basis in dimension two. -/
noncomputable def basisOfNonscalar (dimension : Module.finrank R A = 2)
    (generator : A) (nonscalar : generator ∉ (R ∙ (1 : A))) : Basis (Fin 2) R A := by
  classical
  let : FiniteDimensional R A := FiniteDimensional.of_finrank_eq_succ dimension
  let : Nontrivial A := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank R A)
  apply basisOfLinearIndependentOfCardEqFinrank' ![(1 : A), generator]
  · apply (LinearIndependent.pair_iff' one_ne_zero).mpr
    intro coefficient equal
    exact nonscalar (Submodule.mem_span_singleton.mpr ⟨coefficient, equal⟩)
  · simpa using dimension.symm

@[simp] theorem basisOfNonscalar_zero (dimension : Module.finrank R A = 2)
    (generator : A) (nonscalar : generator ∉ (R ∙ (1 : A))) :
    basisOfNonscalar dimension generator nonscalar 0 = 1 := by
  simp [basisOfNonscalar]

@[simp] theorem basisOfNonscalar_one (dimension : Module.finrank R A = 2)
    (generator : A) (nonscalar : generator ∉ (R ∙ (1 : A))) :
    basisOfNonscalar dimension generator nonscalar 1 = generator := by
  simp [basisOfNonscalar]

variable (R A) in
theorem exists_basis_one (dimension : Module.finrank R A = 2) :
    ∃ basis : Basis (Fin 2) R A, basis 0 = 1 := by
  obtain ⟨generator, nonscalar⟩ := exists_nonscalar R A dimension
  exact ⟨basisOfNonscalar dimension generator nonscalar, basisOfNonscalar_zero ..⟩

variable (R A) in
/-- Every two-dimensional unital associative algebra over a field has a
quadratic presentation, in all characteristics. Dimension two itself implies
the required finite-dimensionality; it is not assumed as extra data. -/
theorem exists_equiv_quadratic (dimension : Module.finrank R A = 2) :
    ∃ a b : R, Nonempty (A ≃ₐ[R] QuadraticAlgebra R a b) := by
  obtain ⟨basis, unit⟩ := exists_basis_one R A dimension
  exact ⟨squareConstant basis, squareLinear basis, ⟨ofBasis basis unit⟩⟩

theorem dimension_of_equiv {a b : R} (presentation : A ≃ₐ[R] QuadraticAlgebra R a b) :
    Module.finrank R A = 2 :=
  presentation.toLinearEquiv.finrank_eq.trans (QuadraticAlgebra.finrank_eq_two a b)

variable (R A) in
/-- Dimension two is also necessary, not merely a convenient sufficient hypothesis. -/
theorem exists_equiv_quadratic_iff :
    (∃ a b : R, Nonempty (A ≃ₐ[R] QuadraticAlgebra R a b)) ↔ Module.finrank R A = 2 := by
  constructor
  · rintro ⟨a, b, ⟨presentation⟩⟩
    exact dimension_of_equiv presentation
  · exact exists_equiv_quadratic R A

/-- Commutativity is a consequence of dimension two, rather than an assumption
on the original algebra. -/
theorem mul_comm_of_finrank_two (dimension : Module.finrank R A = 2) (first second : A) :
    first * second = second * first := by
  obtain ⟨a, b, ⟨presentation⟩⟩ := exists_equiv_quadratic R A dimension
  apply presentation.injective
  simp only [map_mul, mul_comm]

/-- A scalar choice of second vector cannot serve as the required generator. -/
theorem scalar_generator_not_independent [Nontrivial A] (coefficient : R) :
    ¬ LinearIndependent R ![(1 : A), algebraMap R A coefficient] := by
  intro independent
  have excludes := (LinearIndependent.pair_iff' (K := R) one_ne_zero).mp independent coefficient
  exact excludes (Algebra.algebraMap_eq_smul_one coefficient).symm

namespace Controls

/-- The scalar field itself has dimension one, so it has no such presentation. -/
theorem field_not_quadratic :
    ¬ ∃ a b : R, Nonempty (R ≃ₐ[R] QuadraticAlgebra R a b) := by
  rw [exists_equiv_quadratic_iff]
  simp

/-- A split algebra gives a concrete non-scalar choice and a nontrivial
quadratic presentation; its second generator is the idempotent `(0, 1)`. -/
theorem product_idempotent_nonscalar : ((0, 1) : R × R) ∉ (R ∙ (1 : R × R)) := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨coefficient, equal⟩
  have first : coefficient = 0 := by simpa using congrArg Prod.fst equal
  have second : coefficient = 1 := by simpa using congrArg Prod.snd equal
  exact zero_ne_one (first.symm.trans second)

noncomputable def productUnitBasis : Basis (Fin 2) R (R × R) :=
  basisOfNonscalar (by simp) (0, 1) product_idempotent_nonscalar

theorem product_basis_relation :
    squareConstant (productUnitBasis (R := R)) = 0 ∧
      squareLinear (productUnitBasis (R := R)) = 1 := by
  have generator : productUnitBasis (R := R) 1 = (0, 1) := basisOfNonscalar_one ..
  have idempotent : productUnitBasis (R := R) 1 * productUnitBasis (R := R) 1 =
      productUnitBasis (R := R) 1 := by rw [generator]; simp
  simp [squareConstant, squareLinear, idempotent]

theorem product_has_quadratic_presentation :
    Nonempty ((R × R) ≃ₐ[R] QuadraticAlgebra R 0 1) := by
  have representation := ofBasis (productUnitBasis (R := R)) (basisOfNonscalar_zero ..)
  rw [product_basis_relation.1, product_basis_relation.2] at representation
  exact ⟨representation⟩

end Controls

end Algebra.QuadraticPresentation
