import Mathlib.Algebra.QuadraticAlgebra.Basic
import Algebra.QuadraticPresentation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree


/-!
# Quadratic coordinates and a polynomial quotient presentation

Mathlib's `QuadraticAlgebra R a b` stores the coefficients of `1` and `ω`, with
`ω * ω = a + b * ω`.  This file constructs an algebra equivalence with the
existing `AdjoinRoot (X ^ 2 - C b * X - C a)` quotient over every commutative ring.
It uses the two existing universal properties, rather than introducing another
quotient carrier.

The equivalence preserves scalars and sends `ω` to the adjoined root.  Its inverse
evaluates polynomial classes at the coordinate generator.  A coordinate pair
corresponds exactly to its linear polynomial representative, and Mathlib's
monic remainder operation recovers the same coefficients.  A factor map exists
uniquely precisely when the proposed image satisfies the quadratic relation.

Over a field this composes with the independent two-dimensional classification:
a unital associative algebra admits such a quotient presentation exactly when
its dimension is two, with no restriction on characteristic.
-/

set_option autoImplicit false
noncomputable section
namespace Algebra.QuadraticPolynomialPresentation
open Polynomial
open scoped QuadraticAlgebra
variable {R : Type*} [CommRing R]

def definingPolynomial (a b : R) : R[X] := X ^ 2 - C b * X - C a

/-- Polynomial annihilation is exactly the coordinate multiplication relation. -/
theorem aeval_definingPolynomial_iff {A : Type*} [CommRing A] [Algebra R A]
    (a b : R) (value : A) :
    aeval value (definingPolynomial a b) = 0 ↔ value * value = a • 1 + b • value := by
  simp only [definingPolynomial, map_sub, aeval_X, map_mul, aeval_C,
    Algebra.smul_def, mul_one, pow_two]
  constructor <;> intro relation <;> linear_combination relation

theorem root_relation (a b : R) :
    AdjoinRoot.root (definingPolynomial a b) * AdjoinRoot.root (definingPolynomial a b) =
      a • 1 + b • AdjoinRoot.root (definingPolynomial a b) := by
  apply (aeval_definingPolynomial_iff a b _).1
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem omega_isRoot (a b : R) :
    aeval (QuadraticAlgebra.omega : QuadraticAlgebra R a b) (definingPolynomial a b) = 0 :=
  (aeval_definingPolynomial_iff a b _).2 QuadraticAlgebra.omega_mul_omega_eq_add

/-- The coordinate universal property sends the generator to the quotient root. -/
def toAdjoinRoot (a b : R) : QuadraticAlgebra R a b →ₐ[R]
    AdjoinRoot (definingPolynomial a b) :=
  QuadraticAlgebra.lift ⟨AdjoinRoot.root (definingPolynomial a b), root_relation a b⟩

@[simp] theorem toAdjoinRoot_omega (a b : R) :
    toAdjoinRoot a b (QuadraticAlgebra.omega : QuadraticAlgebra R a b) =
      AdjoinRoot.root (definingPolynomial a b) := by
  simp [toAdjoinRoot, QuadraticAlgebra.lift]

/-- The quotient universal property evaluates its root at the coordinate generator. -/
def fromAdjoinRoot (a b : R) : AdjoinRoot (definingPolynomial a b) →ₐ[R]
    QuadraticAlgebra R a b :=
  AdjoinRoot.liftAlgHom (definingPolynomial a b)
    (Algebra.ofId R (QuadraticAlgebra R a b)) QuadraticAlgebra.omega (omega_isRoot a b)

@[simp] theorem fromAdjoinRoot_root (a b : R) :
    fromAdjoinRoot a b (AdjoinRoot.root (definingPolynomial a b)) =
      (QuadraticAlgebra.omega : QuadraticAlgebra R a b) := by
  exact AdjoinRoot.liftAlgHom_root (definingPolynomial a b)
    (Algebra.ofId R (QuadraticAlgebra R a b)) QuadraticAlgebra.omega (omega_isRoot a b)

theorem to_comp_from (a b : R) :
    (toAdjoinRoot a b).comp (fromAdjoinRoot a b) = AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext
  simp

theorem from_comp_to (a b : R) :
    (fromAdjoinRoot a b).comp (toAdjoinRoot a b) = AlgHom.id R _ := by
  apply QuadraticAlgebra.algHom_ext
  simp

/-- The independently constructed algebra maps are inverse. -/
def equivAdjoinRoot (a b : R) : QuadraticAlgebra R a b ≃ₐ[R]
    AdjoinRoot (definingPolynomial a b) :=
  AlgEquiv.ofAlgHom (toAdjoinRoot a b) (fromAdjoinRoot a b)
    (to_comp_from a b) (from_comp_to a b)

@[simp] theorem equivAdjoinRoot_omega (a b : R) :
    equivAdjoinRoot a b (QuadraticAlgebra.omega : QuadraticAlgebra R a b) =
      AdjoinRoot.root (definingPolynomial a b) := toAdjoinRoot_omega a b

@[simp] theorem equivAdjoinRoot_symm_root (a b : R) :
    (equivAdjoinRoot a b).symm (AdjoinRoot.root (definingPolynomial a b)) =
      (QuadraticAlgebra.omega : QuadraticAlgebra R a b) := fromAdjoinRoot_root a b


@[simp] theorem equivAdjoinRoot_algebraMap (a b value : R) :
    equivAdjoinRoot a b (algebraMap R (QuadraticAlgebra R a b) value) =
      algebraMap R (AdjoinRoot (definingPolynomial a b)) value :=
  (equivAdjoinRoot a b).commutes value

/-- The degree-at-most-one representative attached to a coordinate pair. -/
def representative {a b : R} (value : QuadraticAlgebra R a b) : R[X] :=
  C value.re + C value.im * X

theorem equivAdjoinRoot_eq_mk (a b : R) (value : QuadraticAlgebra R a b) :
    equivAdjoinRoot a b value = AdjoinRoot.mk (definingPolynomial a b) (representative value) := by
  simp [equivAdjoinRoot, toAdjoinRoot, QuadraticAlgebra.lift, representative,
    Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem definingPolynomial_monic (a b : R) : (definingPolynomial a b).Monic := by
  have shape : definingPolynomial a b = X ^ 2 - (C b * X + C a) := by
    unfold definingPolynomial; ring
  rw [shape]
  apply monic_X_pow_sub
  compute_degree
  norm_num

theorem definingPolynomial_degree [Nontrivial R] (a b : R) :
    (definingPolynomial a b).degree = 2 := by
  unfold definingPolynomial
  compute_degree!

theorem representative_modByMonic (a b : R) (value : QuadraticAlgebra R a b) :
    representative value %ₘ definingPolynomial a b = representative value := by
  nontriviality R
  apply (modByMonic_eq_self_iff (definingPolynomial_monic a b)).2
  rw [definingPolynomial_degree]
  unfold representative
  compute_degree
  norm_num

theorem modByMonicHom_equiv (a b : R) (value : QuadraticAlgebra R a b) :
    AdjoinRoot.modByMonicHom (definingPolynomial_monic a b) (equivAdjoinRoot a b value) =
      representative value := by
  rw [equivAdjoinRoot_eq_mk, AdjoinRoot.modByMonicHom_mk, representative_modByMonic]

/-- Reducing any polynomial modulo the defining relation agrees with its
coordinate interpretation. -/
theorem modByMonic_eq_representative (a b : R) (polynomial : R[X]) :
    polynomial %ₘ definingPolynomial a b =
      representative ((equivAdjoinRoot a b).symm (AdjoinRoot.mk (definingPolynomial a b) polynomial)) := by
  have compatible := modByMonicHom_equiv a b
    ((equivAdjoinRoot a b).symm (AdjoinRoot.mk (definingPolynomial a b) polynomial))
  simpa only [AlgEquiv.apply_symm_apply, AdjoinRoot.modByMonicHom_mk] using compatible

theorem mapped_root_relation {A : Type*} [CommRing A] [Algebra R A]
    (a b : R) (factor : AdjoinRoot (definingPolynomial a b) →ₐ[R] A) :
    factor (AdjoinRoot.root (definingPolynomial a b)) *
        factor (AdjoinRoot.root (definingPolynomial a b)) =
      a • 1 + b • factor (AdjoinRoot.root (definingPolynomial a b)) := by
  simpa only [map_mul, map_add, map_smul, map_one] using congrArg factor (root_relation a b)

/-- An arbitrary proposed generator image defines a factor map exactly when
it satisfies the stated relation; agreement on that image determines the map. -/
theorem existsUnique_factor_iff {A : Type*} [CommRing A] [Algebra R A]
    (a b : R) (value : A) :
    (∃! factor : AdjoinRoot (definingPolynomial a b) →ₐ[R] A,
      factor (AdjoinRoot.root (definingPolynomial a b)) = value) ↔
      value * value = a • 1 + b • value := by
  constructor
  · rintro ⟨factor, image, _⟩
    simpa only [image] using mapped_root_relation a b factor
  · intro relation
    refine ⟨AdjoinRoot.liftAlgHom (definingPolynomial a b) (Algebra.ofId R A) value
      ((aeval_definingPolynomial_iff a b value).2 relation), ?_, ?_⟩
    · exact AdjoinRoot.liftAlgHom_root (definingPolynomial a b) (Algebra.ofId R A) value _
    · intro factor image
      apply AdjoinRoot.algHom_ext
      exact image.trans (AdjoinRoot.liftAlgHom_root (definingPolynomial a b)
        (Algebra.ofId R A) value ((aeval_definingPolynomial_iff a b value).2 relation)).symm


theorem fromAdjoinRoot_mk (a b : R) (polynomial : R[X]) :
    fromAdjoinRoot a b (AdjoinRoot.mk (definingPolynomial a b) polynomial) =
      aeval (QuadraticAlgebra.omega : QuadraticAlgebra R a b) polynomial := by
  exact AdjoinRoot.liftAlgHom_mk (definingPolynomial a b)
    (Algebra.ofId R (QuadraticAlgebra R a b)) QuadraticAlgebra.omega (omega_isRoot a b) polynomial

theorem aeval_omega_eq_zero_iff (a b : R) (polynomial : R[X]) :
    aeval (QuadraticAlgebra.omega : QuadraticAlgebra R a b) polynomial = 0 ↔
      definingPolynomial a b ∣ polynomial := by
  rw [← fromAdjoinRoot_mk]
  change (equivAdjoinRoot a b).symm (AdjoinRoot.mk (definingPolynomial a b) polynomial) = 0 ↔ _
  rw [← map_zero (equivAdjoinRoot a b).symm, (equivAdjoinRoot a b).symm.injective.eq_iff]
  exact AdjoinRoot.mk_eq_zero

theorem coordinate_remainder_constant (a b : R) (polynomial : R[X]) :
    ((equivAdjoinRoot a b).symm (AdjoinRoot.mk (definingPolynomial a b) polynomial)).re =
      (polynomial %ₘ definingPolynomial a b).coeff 0 := by
  have equality := congrArg (fun p : R[X] => p.coeff 0)
    (modByMonic_eq_representative a b polynomial)
  simpa [representative] using equality.symm

theorem coordinate_remainder_linear (a b : R) (polynomial : R[X]) :
    ((equivAdjoinRoot a b).symm (AdjoinRoot.mk (definingPolynomial a b) polynomial)).im =
      (polynomial %ₘ definingPolynomial a b).coeff 1 := by
  have equality := congrArg (fun p : R[X] => p.coeff 1)
    (modByMonic_eq_representative a b polynomial)
  simpa [representative] using equality.symm

/-- The coordinate classification composes with the polynomial quotient presentation. -/
theorem exists_equiv_adjoinRoot (K A : Type*) [Field K] [Ring A] [Algebra K A]
    (dimension : Module.finrank K A = 2) :
    ∃ a b : K, Nonempty (A ≃ₐ[K] AdjoinRoot (definingPolynomial a b)) := by
  obtain ⟨a, b, ⟨coordinates⟩⟩ :=
    Algebra.QuadraticPresentation.exists_equiv_quadratic K A dimension
  exact ⟨a, b, ⟨coordinates.trans (equivAdjoinRoot a b)⟩⟩


/-- A quadratic monic quotient presentation exists exactly in dimension two. -/
theorem exists_equiv_adjoinRoot_iff (K A : Type*) [Field K] [Ring A] [Algebra K A] :
    (∃ a b : K, Nonempty (A ≃ₐ[K] AdjoinRoot (definingPolynomial a b))) ↔
      Module.finrank K A = 2 := by
  constructor
  · rintro ⟨a, b, ⟨presentation⟩⟩
    exact Algebra.QuadraticPresentation.dimension_of_equiv
      (presentation.trans (equivAdjoinRoot a b).symm)
  · exact exists_equiv_adjoinRoot K A

/-- Polynomial evaluation commutes with a genuine affine generator change. -/
theorem changeGenerator_aeval (a b u : R) (v : Rˣ) (p : R[X]) :
    QuadraticPresentation.changeGenerator a b u v (aeval QuadraticAlgebra.omega p) =
      aeval (QuadraticPresentation.changeGenerator a b u v QuadraticAlgebra.omega) p :=
  (aeval_algHom_apply (QuadraticPresentation.changeGenerator a b u v) _ p).symm

namespace Controls

/-- Cubic reduction retains an actual nonzero linear component. -/
theorem cubic_coordinates :
    (equivAdjoinRoot (2 : ℤ) 3).symm
      ((AdjoinRoot.root (definingPolynomial (2 : ℤ) 3)) ^ 3) =
      (⟨6, 11⟩ : QuadraticAlgebra ℤ 2 3) := by
  rw [map_pow, equivAdjoinRoot_symm_root]
  ext <;> norm_num [pow_succ, pow_two, QuadraticAlgebra.omega]


theorem cubic_remainder :
    (X ^ 3 : ℤ[X]) %ₘ definingPolynomial (2 : ℤ) 3 = C 6 + C 11 * X := by
  rw [modByMonic_eq_representative]
  rw [show AdjoinRoot.mk (definingPolynomial (2 : ℤ) 3) (X ^ 3) =
      (AdjoinRoot.root (definingPolynomial (2 : ℤ) 3)) ^ 3 by rw [map_pow, AdjoinRoot.mk_X]]
  rw [cubic_coordinates]
  rfl

/-- A non-root cannot be used as the generator image of an algebra map. -/
theorem bad_root_has_no_factor :
    ¬ ∃ factor : AdjoinRoot (definingPolynomial (2 : ℤ) 3) →ₐ[ℤ] ℤ,
      factor (AdjoinRoot.root (definingPolynomial (2 : ℤ) 3)) = 1 := by
  rintro ⟨factor, image⟩
  have relation := mapped_root_relation (2 : ℤ) 3 factor
  rw [image] at relation
  norm_num at relation

end Controls

end Algebra.QuadraticPolynomialPresentation
