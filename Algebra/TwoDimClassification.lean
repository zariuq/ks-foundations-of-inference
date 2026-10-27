/-
# Classification of 2-Dimensional Unital Real Algebras

This module proves the classical classification theorem:

**Theorem**: Every 2-dimensional unital associative algebra over ℝ is isomorphic to exactly one of:
- Complex numbers ℂ (where i² = -1)
- Dual numbers ℝ[ε] (where ε² = 0)
- Split-complex numbers ℝ[j] (where j² = +1)

The proof uses the "completing the square" technique:
1. Any 2D unital algebra has a basis {1, e} with e² = a + be for some a, b ∈ ℝ
2. Define e' = e - b/2, then (e')² = a + b²/4 =: μ
3. The sign of μ determines the algebra:
   - μ < 0: Complex (rescale to get i with i² = -1)
   - μ = 0: Dual (already have ε² = 0)
   - μ > 0: Split-complex (rescale to get j with j² = +1)

Key insight for K&S: The bilinearProduct parameterized by μ continuously covers all three cases,
but there are only 3 isomorphism classes - the classification is discrete, not continuous!

The normalized parameter μ depends on the chosen generator. Its sign, rather
than its numerical value, determines the real algebra isomorphism class.
The general basis construction and polynomial quotient presentation use the
shared quadratic presentation modules; no extra algebra carrier is defined.

## References

- Skilling & Knuth (2018), "The Symmetrical Foundation of Measure, Probability, and Quantum Theories"
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.DualNumber
import Algebra.SplitComplex
import Algebra.QuadraticPolynomialPresentation
import Mathlib.Tactic

namespace Algebra.TwoDimClassification

open SplitComplex
open scoped QuadraticAlgebra

/-! ## The μ-Parameterized Product

Following K&S, we define the bilinear product parameterized by μ ∈ ℝ:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + μ·u₂v₂, u₁v₂ + u₂v₁)

This gives:
- μ = -1: Complex multiplication
- μ = 0: Dual number multiplication
- μ = +1: Split-complex multiplication
-/

/-- The normalized family is the canonical quadratic algebra with no linear
term. Ring, module and real algebra structures all come from Mathlib. -/
abbrev MuAlgebra (μ : ℝ) := QuadraticAlgebra ℝ μ 0

namespace MuAlgebra

variable (μ : ℝ)

/-- The normalized product has no linear coefficient. -/
@[simp] theorem mul_im (z w : MuAlgebra μ) :
    (z * w).im = z.re * w.im + z.im * w.re := by simp

end MuAlgebra

/-! ## Isomorphisms to Concrete Algebras

We now show that:
- MuAlgebra (-1) ≃ ℂ
- MuAlgebra 1 ≃ SplitComplex
-/

/-- MuAlgebra (-1) is isomorphic to ℂ. -/
noncomputable def muAlgebraNegOneEquivComplex : MuAlgebra (-1) ≃+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  invFun c := ⟨c.re, c.im⟩
  left_inv := fun z => by ext <;> rfl
  right_inv := fun c => by
    apply Complex.ext
    · simp
    · simp
  map_mul' := fun z w => by
    apply Complex.ext
    · simp only [QuadraticAlgebra.re_mul, Complex.mul_re]; ring
    · simp only [MuAlgebra.mul_im, Complex.mul_im]
  map_add' := fun z w => by
    apply Complex.ext <;> simp

/-! ## The Classification Theorem

Now we prove the main classification result.
-/

/-- The three isomorphism classes of 2D unital real algebras. -/
inductive TwoDimAlgebraClass
  | complex      -- i² = -1
  | dual         -- ε² = 0
  | splitComplex -- j² = +1
deriving DecidableEq, Repr

/-- Classification by the sign of μ. -/
noncomputable def classifyByMu (μ : ℝ) : TwoDimAlgebraClass :=
  if μ < 0 then TwoDimAlgebraClass.complex
  else if μ = 0 then TwoDimAlgebraClass.dual
  else TwoDimAlgebraClass.splitComplex

/-! ## The Completing-the-Square Parameter

The key algebraic insight: Given e² = a + be, defining e' = e - b/2 gives (e')² = μ·1
where μ = a + b²/4. Rescaling the new generator changes μ; its sign classifies
the resulting real algebra.
-/

/-- The normalized square parameter. Its numerical value is not invariant
under a further rescaling of the generator. -/
noncomputable def normalizedSquareParameter (a b : ℝ) : ℝ := a + b^2 / 4

/-! ## Independent coordinate multiplication -/

/-- K&S bilinearProduct matches MuAlgebra multiplication. -/
theorem ks_bilinearProduct_eq_muAlgebra (μ : ℝ) (z w : MuAlgebra μ) :
    z * w = ⟨z.re * w.re + μ * z.im * w.im, z.re * w.im + z.im * w.re⟩ := by
  ext <;> simp

/-- The three-way classification is complete: every μ falls into exactly one class. -/
theorem classification_trichotomy (μ : ℝ) :
    (μ < 0 ∧ classifyByMu μ = TwoDimAlgebraClass.complex) ∨
    (μ = 0 ∧ classifyByMu μ = TwoDimAlgebraClass.dual) ∨
    (0 < μ ∧ classifyByMu μ = TwoDimAlgebraClass.splitComplex) := by
  rcases lt_trichotomy μ 0 with h | h | h
  · left; exact ⟨h, by simp [classifyByMu, h]⟩
  · right; left; exact ⟨h, by simp [classifyByMu, h]⟩
  · right; right; exact ⟨h, by simp [classifyByMu, not_lt.mpr (le_of_lt h), ne_of_gt h]⟩

/-! ## Connection to K&S Bilinear Product

The K&S bilinearProduct is exactly MuAlgebra multiplication viewed on ℝ × ℝ.
-/

/-- The general bilinear product form (matching K&S definition in SymmetricalFoundation). -/
def bilinearProductDef (μ : ℝ) (u v : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 * v.1 + μ * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- MuAlgebra multiplication matches bilinearProductDef. -/
theorem muAlgebra_eq_bilinearProductDef (μ : ℝ) (z w : MuAlgebra μ) :
    let prod := z * w
    (prod.re, prod.im) = bilinearProductDef μ (z.re, z.im) (w.re, w.im) := by
  simp only [bilinearProductDef, QuadraticAlgebra.re_mul, MuAlgebra.mul_im]

/-! ## The conjugate norm

Positive definiteness singles out negative parameters within this algebraic
family. It does not establish a physical selection principle.
-/

/-- The consumed conjugate API reuses the canonical quadratic involution. -/
def MuAlgebra.conj {μ : ℝ} (z : MuAlgebra μ) : MuAlgebra μ := star z

@[simp] lemma MuAlgebra.conj_re {μ : ℝ} (z : MuAlgebra μ) : z.conj.re = z.re := by
  simp [conj]
@[simp] lemma MuAlgebra.conj_im {μ : ℝ} (z : MuAlgebra μ) : z.conj.im = -z.im := rfl

/-- The consumed conjugate-norm API is Mathlib's quadratic norm. -/
def MuAlgebra.conjNorm {μ : ℝ} (z : MuAlgebra μ) : ℝ := QuadraticAlgebra.norm z

/-- Its coordinate formula in the normalized family. -/
theorem MuAlgebra.conjNorm_def {μ : ℝ} (z : MuAlgebra μ) :
    z.conjNorm = z.re ^ 2 - μ * z.im ^ 2 := by
  simp [conjNorm, QuadraticAlgebra.norm_def, pow_two, mul_assoc]

/-- The product identity is inherited from the standard norm and involution. -/
theorem MuAlgebra.mul_conj_eq_norm {μ : ℝ} (z : MuAlgebra μ) :
    z * z.conj = ⟨z.conjNorm, 0⟩ := by
  change z * star z = algebraMap ℝ (MuAlgebra μ) (QuadraticAlgebra.norm z)
  exact (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm

/-- For μ < 0, the conjugate norm is positive definite:
    N(z) ≥ 0, and N(z) = 0 iff z = 0. -/
theorem MuAlgebra.conjNorm_nonneg {μ : ℝ} (hμ : μ < 0) (z : MuAlgebra μ) :
    0 ≤ z.conjNorm := by
  simp only [MuAlgebra.conjNorm_def]
  have h : 0 ≤ -μ * z.im^2 := by nlinarith [sq_nonneg z.im]
  linarith [sq_nonneg z.re]

theorem MuAlgebra.conjNorm_eq_zero_iff {μ : ℝ} (hμ : μ < 0) (z : MuAlgebra μ) :
    z.conjNorm = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [MuAlgebra.conjNorm_def] at h
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by simpa [hre, mul_eq_zero, ne_of_lt hμ] using h
    ext <;> assumption
  · rintro rfl
    simp [MuAlgebra.conjNorm_def]

/-- For μ > 0 (split-complex), the conjugate norm can be negative. -/
theorem MuAlgebra.conjNorm_can_be_negative {μ : ℝ} (hμ : 0 < μ) :
    ∃ z : MuAlgebra μ, z.conjNorm < 0 := by
  use ⟨0, 1⟩
  simp [MuAlgebra.conjNorm_def]
  linarith

/-- For μ = 0 (dual), the conjugate norm ignores the imaginary part. -/
theorem MuAlgebra.conjNorm_zero_mu (z : MuAlgebra 0) : z.conjNorm = z.re^2 := by
  simp [MuAlgebra.conjNorm_def]

/-- Only negative μ gives a positive-definite conjugate norm in this family.
The algebraic implication does not establish a physical selection principle. -/
theorem selection_theorem :
    ∀ μ : ℝ, (∀ z : MuAlgebra μ, 0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) ↔ μ < 0 := by
  intro μ
  constructor
  · intro h
    have tested := h ⟨0, 1⟩
    have nonzero : (⟨0, 1⟩ : MuAlgebra μ) ≠ 0 := by
      intro equal
      have := congrArg QuadraticAlgebra.im equal
      norm_num at this
    have nonpositive : μ ≤ 0 := by simpa [MuAlgebra.conjNorm_def] using tested.1
    have unequal : μ ≠ 0 := by
      intro zero
      exact nonzero (tested.2 (by simp [MuAlgebra.conjNorm_def, zero]))
    exact lt_of_le_of_ne nonpositive unequal
  · intro hμ z
    exact ⟨MuAlgebra.conjNorm_nonneg hμ z, (MuAlgebra.conjNorm_eq_zero_iff hμ z).mp⟩

/-- Multiplicativity is the standard quadratic norm's multiplication law. -/
theorem MuAlgebra.conjNorm_mul {μ : ℝ} (z w : MuAlgebra μ) :
    (z * w).conjNorm = z.conjNorm * w.conjNorm :=
  (QuadraticAlgebra.norm : MuAlgebra μ →* ℝ).map_mul z w

/-! ## General relations and classification -/

/-- The general coordinate family reuses the standard quadratic algebra;
its defining relation is `ω² = a + bω`. -/
abbrev GeneralBilinearAlgebra (a b : ℝ) := QuadraticAlgebra ℝ a b

/-- Completing the square is the inverse affine shift `ω ↦ ω - b/2`. -/
noncomputable def completingSquareAlgEquiv (a b : ℝ) :
    GeneralBilinearAlgebra a b ≃ₐ[ℝ] MuAlgebra (normalizedSquareParameter a b) :=
  (QuadraticPresentation.affineEquiv a b (normalizedSquareParameter a b) 0 (-(b / 2)) 1
    (by simp [QuadraticPresentation.shiftedConstant, normalizedSquareParameter]; ring)
    (by simp [QuadraticPresentation.shiftedLinear]; ring)).symm

@[simp] theorem completingSquareAlgEquiv_re (a b : ℝ) (z : QuadraticAlgebra ℝ a b) :
    (completingSquareAlgEquiv a b z).re = z.re + b * z.im / 2 := by
  change z.re - -(b / 2) * (1 : ℝ) * z.im = z.re + b * z.im / 2
  ring

@[simp] theorem completingSquareAlgEquiv_im (a b : ℝ) (z : QuadraticAlgebra ℝ a b) :
    (completingSquareAlgEquiv a b z).im = z.im := by
  change (1 : ℝ) * z.im = z.im
  exact one_mul _

/-- The shifted old generator becomes the normalized generator, rather than
merely satisfying a squaring identity in an already normalized algebra. -/
theorem completingSquareAlgEquiv_shift (a b : ℝ) :
    completingSquareAlgEquiv a b
        (QuadraticAlgebra.omega - algebraMap ℝ (QuadraticAlgebra ℝ a b) (b / 2)) =
      (QuadraticAlgebra.omega : MuAlgebra (normalizedSquareParameter a b)) := by
  ext <;> simp

/-! ## Real algebra equivalences and distinct standard forms -/

/-- The existing complex comparison preserves the real algebra structure. -/
noncomputable def muAlgebraNegOneAlgEquivComplex : MuAlgebra (-1) ≃ₐ[ℝ] ℂ where
  __ := muAlgebraNegOneEquivComplex
  commutes' r := by
    apply Complex.ext <;> simp [muAlgebraNegOneEquivComplex]

/-- The missing standard form uses Mathlib's dual numbers, with their
nonzero square-zero generator, rather than only a zero parameter label. -/
noncomputable def muAlgebraZeroAlgEquivDual : MuAlgebra 0 ≃ₐ[ℝ] DualNumber ℝ where
  toFun z := (z.re, z.im)
  invFun z := ⟨z.fst, z.snd⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl
  map_mul' z w := by
    apply TrivSqZeroExt.ext
    · change z.re * w.re + 0 * z.im * w.im = z.re * w.re
      ring
    · change z.re * w.im + z.im * w.re + 0 * z.im * w.im =
        z.re * w.im + z.im * w.re
      ring
  map_add' z w := by apply TrivSqZeroExt.ext <;> rfl
  commutes' r := by rw [QuadraticAlgebra.algebraMap_eq]; rfl

/-- One rescaling construction covers both nonzero sign branches. -/
noncomputable def muAlgebraRescaleAlgOfRatio (μ μ' : ℝ) (ratio : 0 < μ / μ') :
    MuAlgebra μ ≃ₐ[ℝ] MuAlgebra μ' := by
  have targetNonzero : μ' ≠ 0 := by rintro rfl; simp at ratio
  let v : ℝˣ := Units.mk0 (Real.sqrt (μ / μ')) (ne_of_gt (Real.sqrt_pos.2 ratio))
  apply QuadraticPresentation.affineEquiv μ' 0 μ 0 0 v
  · dsimp [QuadraticPresentation.shiftedConstant, v]
    rw [Real.sq_sqrt ratio.le]
    simp [div_mul_cancel₀ μ targetNonzero]
  · simp [QuadraticPresentation.shiftedLinear]

noncomputable def muAlgebraRescaleAlg (μ μ' : ℝ) (hμ : 0 < μ) (hμ' : 0 < μ') :
    MuAlgebra μ ≃ₐ[ℝ] MuAlgebra μ' := muAlgebraRescaleAlgOfRatio μ μ' (div_pos hμ hμ')

noncomputable def muAlgebraRescaleNegAlg (μ μ' : ℝ) (hμ : μ < 0) (hμ' : μ' < 0) :
    MuAlgebra μ ≃ₐ[ℝ] MuAlgebra μ' :=
  muAlgebraRescaleAlgOfRatio μ μ' (div_pos_of_neg_of_neg hμ hμ')

/-- All three branches now carry an actual equivalence of real algebras. -/
theorem mu_algebra_real_classification (μ : ℝ) :
    (μ < 0 ∧ Nonempty (MuAlgebra μ ≃ₐ[ℝ] ℂ)) ∨
      (μ = 0 ∧ Nonempty (MuAlgebra μ ≃ₐ[ℝ] DualNumber ℝ)) ∨
      (0 < μ ∧ Nonempty (MuAlgebra μ ≃ₐ[ℝ] SplitComplex)) := by
  rcases lt_trichotomy μ 0 with negative | zero | positive
  · exact Or.inl ⟨negative, ⟨(muAlgebraRescaleNegAlg μ (-1) negative
      neg_one_lt_zero).trans muAlgebraNegOneAlgEquivComplex⟩⟩
  · subst μ
    exact Or.inr (Or.inl ⟨rfl, ⟨muAlgebraZeroAlgEquivDual⟩⟩)
  · exact Or.inr (Or.inr ⟨positive, ⟨muAlgebraRescaleAlg μ 1 positive one_pos⟩⟩)

/-- Split-complex numbers have no nonzero square-zero element, although
they do have nonzero zero divisors. -/
theorem split_square_eq_zero_iff (z : SplitComplex) : z * z = 0 ↔ z = 0 := by
  constructor
  · intro square
    have realPart := congrArg QuadraticAlgebra.re square
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_zero] at realPart
    have realZero : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have imaginaryZero : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    ext <;> assumption
  · rintro rfl
    exact zero_mul _

theorem dual_eps_ne_zero : (DualNumber.eps : DualNumber ℝ) ≠ 0 := by
  intro equal
  have := congrArg TrivSqZeroExt.snd equal
  simp at this

/-- Complex numbers cannot supply the dual numbers' nonzero nilpotent. -/
theorem complex_not_equiv_dual : ¬ Nonempty (ℂ ≃ₐ[ℝ] DualNumber ℝ) := by
  rintro ⟨equiv⟩
  have square : equiv.symm DualNumber.eps * equiv.symm DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have vanishes : equiv.symm DualNumber.eps = 0 := mul_self_eq_zero.mp square
  apply dual_eps_ne_zero
  apply equiv.symm.injective
  simpa using vanishes

/-- A nonzero nilpotent also separates dual from split-complex numbers. -/
theorem dual_not_equiv_split : ¬ Nonempty (DualNumber ℝ ≃ₐ[ℝ] SplitComplex) := by
  rintro ⟨equiv⟩
  have square : equiv DualNumber.eps * equiv DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have vanishes := (split_square_eq_zero_iff _).mp square
  apply dual_eps_ne_zero
  apply equiv.injective
  simpa using vanishes

/-- Nonzero zero divisors separate split-complex from complex numbers. -/
theorem split_not_equiv_complex : ¬ Nonempty (SplitComplex ≃ₐ[ℝ] ℂ) := by
  rintro ⟨equiv⟩
  obtain ⟨first, second, firstNonzero, secondNonzero, product⟩ :=
    SplitComplex.has_zero_divisors
  have mapped : equiv first * equiv second = 0 := by rw [← map_mul, product, map_zero]
  rcases mul_eq_zero.mp mapped with firstZero | secondZero
  · exact firstNonzero (equiv.injective (by simpa using firstZero))
  · exact secondNonzero (equiv.injective (by simpa using secondZero))

/-- A uniform carrier for the three standard real algebras. -/
def standardForm : TwoDimAlgebraClass → Type
  | .complex => ℂ
  | .dual => DualNumber ℝ
  | .splitComplex => SplitComplex

noncomputable instance standardFormCommRing (kind : TwoDimAlgebraClass) :
    CommRing (standardForm kind) := by
  cases kind <;> dsimp [standardForm] <;> infer_instance

noncomputable instance standardFormAlgebra (kind : TwoDimAlgebraClass) :
    Algebra ℝ (standardForm kind) := by
  cases kind <;> dsimp [standardForm] <;> infer_instance

/-- An isomorphism cannot identify distinct entries of the classification. -/
theorem standardForm_class_eq {first second : TwoDimAlgebraClass}
    (equivalent : Nonempty (standardForm first ≃ₐ[ℝ] standardForm second)) :
    first = second := by
  cases first <;> cases second
  · rfl
  · exact (complex_not_equiv_dual equivalent).elim
  · exact (split_not_equiv_complex (equivalent.map AlgEquiv.symm)).elim
  · exact (complex_not_equiv_dual (equivalent.map AlgEquiv.symm)).elim
  · rfl
  · exact (dual_not_equiv_split equivalent).elim
  · exact (split_not_equiv_complex equivalent).elim
  · exact (dual_not_equiv_split (equivalent.map AlgEquiv.symm)).elim
  · rfl

/-- Every normalized parameter has its sign-selected standard real algebra. -/
noncomputable def muAlgebraAlgEquivStandard (μ : ℝ) :
    MuAlgebra μ ≃ₐ[ℝ] standardForm (classifyByMu μ) := by
  by_cases negative : μ < 0
  · rw [show classifyByMu μ = .complex by simp [classifyByMu, negative]]
    exact (muAlgebraRescaleNegAlg μ (-1) negative neg_one_lt_zero).trans
      muAlgebraNegOneAlgEquivComplex
  · by_cases zero : μ = 0
    · subst μ
      rw [show classifyByMu 0 = .dual by simp [classifyByMu]]
      exact muAlgebraZeroAlgEquivDual
    · rw [show classifyByMu μ = .splitComplex by simp [classifyByMu, negative, zero]]
      exact muAlgebraRescaleAlg μ 1 (lt_of_le_of_ne (le_of_not_gt negative) (Ne.symm zero)) one_pos

/-- The same classification applies to the actual polynomial quotient, via
its independently proved quadratic-coordinate equivalence. -/
noncomputable def adjoinRootAlgEquivStandard (a b : ℝ) :
    AdjoinRoot (QuadraticPolynomialPresentation.definingPolynomial a b) ≃ₐ[ℝ]
      standardForm (classifyByMu (normalizedSquareParameter a b)) :=
  (QuadraticPolynomialPresentation.equivAdjoinRoot a b).symm.trans
    ((completingSquareAlgEquiv a b).trans (muAlgebraAlgEquivStandard (normalizedSquareParameter a b)))

/-- The sign class is the complete invariant for normalized parameters. -/
theorem mu_algebra_equiv_iff (μ μ' : ℝ) :
    Nonempty (MuAlgebra μ ≃ₐ[ℝ] MuAlgebra μ') ↔ classifyByMu μ = classifyByMu μ' := by
  constructor
  · rintro ⟨equiv⟩
    exact standardForm_class_eq ⟨(muAlgebraAlgEquivStandard μ).symm.trans
      (equiv.trans (muAlgebraAlgEquivStandard μ'))⟩
  · intro equal
    exact ⟨(muAlgebraAlgEquivStandard μ).trans
      ((AlgEquiv.cast equal).trans (muAlgebraAlgEquivStandard μ').symm)⟩

/-- Negative control for numerical invariance: two different positive
parameters present isomorphic real algebras. -/
theorem parameter_value_not_invariant :
    (2 : ℝ) ≠ 1 ∧ Nonempty (MuAlgebra 2 ≃ₐ[ℝ] MuAlgebra 1) := by
  exact ⟨by norm_num, ⟨muAlgebraRescaleAlg 2 1 (by norm_num) one_pos⟩⟩

/-- Every unital associative real algebra of dimension two has exactly one
of the three standard forms. Commutativity is a consequence, not a premise. -/
theorem two_dimensional_classification (A : Type*) [Ring A] [Algebra ℝ A]
    (dimension : Module.finrank ℝ A = 2) :
    ∃! kind : TwoDimAlgebraClass, Nonempty (A ≃ₐ[ℝ] standardForm kind) := by
  obtain ⟨a, b, ⟨presentation⟩⟩ :=
    QuadraticPresentation.exists_equiv_quadratic ℝ A dimension
  let μ := normalizedSquareParameter a b
  let normalized : A ≃ₐ[ℝ] MuAlgebra μ := presentation.trans (completingSquareAlgEquiv a b)
  let comparison : A ≃ₐ[ℝ] standardForm (classifyByMu μ) :=
    normalized.trans (muAlgebraAlgEquivStandard μ)
  refine ⟨classifyByMu μ, ⟨comparison⟩, ?_⟩
  intro other ⟨equiv⟩
  exact standardForm_class_eq ⟨equiv.symm.trans comparison⟩

end Algebra.TwoDimClassification
