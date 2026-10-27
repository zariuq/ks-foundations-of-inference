/-
# Algebraic components of the symmetrical-foundation proposal

The additive representation gives a sum rule. Exponential differences telescope
for any supplied function; without event semantics and bounds they are positive
ratios, not automatically conditional probabilities.

The pair algebra has three discriminant classes. Conjugate norms multiply in
all classes; positivity with a definite zero selects the complex class. The
chosen norm-square readout satisfies interference and mean-phase identities.
These identities do not prove uniqueness among all alternative readouts.
`quantumAmplitude` is an explicit choice, not a derived physical postulate.

Reference: Skilling and Knuth (2018), Annalen der Physik, 1800057.
-/

import KnuthSkilling.Additive.Main
import Algebra.TwoDimClassification
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace KnuthSkilling.SymmetricalFoundation

open Complex Real MeasureTheory
open KnuthSkilling.Additive

section Probability

/-- The FOI representation theorem directly gives the sum rule for measures.
This is Equation (6) of the Symmetrical Foundation paper. -/
theorem sumRule_from_FOI (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∃ Θ : α → ℝ, ∀ x y : α, Θ (KSSemigroupBase.op x y) = Θ x + Θ y := by
  obtain ⟨Θ, _, hΘ_add⟩ := HasRepresentationTheorem.exists_representation (α := α)
  exact ⟨Θ, hΘ_add⟩

/-- Proportions are ratios of the additive representation.
This corresponds to Equation (12): p(dest ∘ source) = p(dest) / p(source)

In the exponential form (where measure = exp(Θ)), this becomes:
  p(A|B) = exp(Θ(A)) / exp(Θ(B)) = exp(Θ(A) - Θ(B))
-/
noncomputable def proportionRepresentation (α : Type*) [KSSemigroupBase α]
    (Θ : α → ℝ) (source dest : α) : ℝ :=
  Real.exp (Θ dest - Θ source)

/-- The product rule: proportions chain multiplicatively.
This is Equation (10): p(UV ∘ VW) = p(UV) · p(VW)

In terms of the additive representation:
  exp(Θ(U) - Θ(W)) = exp(Θ(U) - Θ(V)) · exp(Θ(V) - Θ(W))
-/
theorem productRule (α : Type*) [KSSemigroupBase α]
    (Θ : α → ℝ) (u v w : α) :
    proportionRepresentation α Θ w u =
    proportionRepresentation α Θ v u * proportionRepresentation α Θ w v := by
  simp only [proportionRepresentation]
  rw [← Real.exp_add]
  congr 1
  ring

end Probability

section PairPostulate

/-- The three product rules from Equation (19).
Associativity of the bilinear product ⊙ on ℝ² forces one of three forms:

(a) Complex: u ⊙ v = (u₁v₁ - u₂v₂, u₁v₂ + u₂v₁)  [μ = -1]
(b) Dual:    u ⊙ v = (u₁v₁, u₁v₂ + u₂v₁)          [μ = 0]
(c) Split:   u ⊙ v = (u₁v₁ + u₂v₂, u₁v₂ + u₂v₁)  [μ = +1]

where μ is the discriminant parameter.
-/
inductive PairProduct
  | complex
  | dual
  | split
  deriving DecidableEq, Repr

/-- The general bilinear product with discriminant μ.
Setting μ = -1, 0, +1 gives the three cases. -/
def bilinearProduct (μ : ℝ) (u v : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 * v.1 + μ * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- Complex product (19a): standard complex multiplication -/
def complexProduct (u v : ℝ × ℝ) : ℝ × ℝ := bilinearProduct (-1) u v

/-- Dual product (19b): multiplication in dual numbers ℝ[ε]/(ε²) -/
def dualProduct (u v : ℝ × ℝ) : ℝ × ℝ := bilinearProduct 0 u v

/-- Split product (19c): multiplication in split-complex numbers -/
def splitProduct (u v : ℝ × ℝ) : ℝ × ℝ := bilinearProduct 1 u v

/-- The general bilinear product is associative for any μ. -/
theorem bilinearProduct_assoc (μ : ℝ) (u v w : ℝ × ℝ) :
    bilinearProduct μ (bilinearProduct μ u v) w =
    bilinearProduct μ u (bilinearProduct μ v w) := by
  simp only [bilinearProduct]
  ext <;> ring

/-- The complex product is associative. -/
theorem complexProduct_assoc (u v w : ℝ × ℝ) :
    complexProduct (complexProduct u v) w = complexProduct u (complexProduct v w) :=
  bilinearProduct_assoc (-1) u v w

/-- The dual product is associative. -/
theorem dualProduct_assoc (u v w : ℝ × ℝ) :
    dualProduct (dualProduct u v) w = dualProduct u (dualProduct v w) :=
  bilinearProduct_assoc 0 u v w

/-- The split product is associative. -/
theorem splitProduct_assoc (u v w : ℝ × ℝ) :
    splitProduct (splitProduct u v) w = splitProduct u (splitProduct v w) :=
  bilinearProduct_assoc 1 u v w

/-- Complex product corresponds to actual complex multiplication. -/
theorem complexProduct_eq_mul (u v : ℝ × ℝ) :
    let z₁ : ℂ := ⟨u.1, u.2⟩
    let z₂ : ℂ := ⟨v.1, v.2⟩
    let prod := complexProduct u v
    (⟨prod.1, prod.2⟩ : ℂ) = z₁ * z₂ := by
  simp only [complexProduct, bilinearProduct]
  apply Complex.ext
  · simp only [Complex.mul_re]; ring
  · simp only [Complex.mul_im]

/-- CLASSIFICATION THEOREM (Eq. 19 derivation):

The general 2D bilinear associative unital algebra has multiplication:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + a·u₂v₂, u₁v₂ + u₂v₁ + b·u₂v₂)

This is GeneralBilinearAlgebra(a, b) = mathlib's QuadraticAlgebra(a, b).

Via completing the square (change of basis e' = e - b/2), we get:
  GeneralBilinearAlgebra(a, b) ≃+* MuAlgebra(a + b²/4)

So any such algebra is ISOMORPHIC to bilinearProduct(μ) for μ = a + b²/4.

NOTE: The original theorem statement (claiming EQUALITY) was incorrect.
The correct result is ISOMORPHISM - see TwoDimClassification.completingSquareAlgEquiv.
-/
theorem classification_bilinear_isomorphic :
    ∀ (a b : ℝ),
      Nonempty (Algebra.TwoDimClassification.GeneralBilinearAlgebra a b ≃+*
                Algebra.TwoDimClassification.MuAlgebra (a + b^2/4)) := by
  intro a b
  exact ⟨(Algebra.TwoDimClassification.completingSquareAlgEquiv a b).toRingEquiv⟩

/-- A bilinear product on ℝ² with identity (1,0) is determined by (0,1)*(0,1) = (a, b).
    The resulting algebra is isomorphic to MuAlgebra(a + b²/4).

    This theorem shows:
    1. Bilinearity + identity determines the algebra by its structure constants
    2. The structure constants (a, b) classify the algebra up to isomorphism
    3. The isomorphism class depends only on μ = a + b²/4 -/
theorem classification_by_structure_constants (a b : ℝ) :
    let μ := a + b^2/4
    Nonempty (Algebra.TwoDimClassification.GeneralBilinearAlgebra a b ≃+*
              Algebra.TwoDimClassification.MuAlgebra μ) :=
  ⟨(Algebra.TwoDimClassification.completingSquareAlgEquiv a b).toRingEquiv⟩

end PairPostulate

section BornRule

/-- The Born rule: probability/rate is modulus-squared.
This is Equation (28): p(x) = |x|²

This file verifies its algebraic and mean-phase properties.
-/
def bornRule (z : ℂ) : ℝ := Complex.normSq z

/-- Born rule equals squared norm. -/
theorem bornRule_eq_norm_sq (z : ℂ) : bornRule z = ‖z‖ ^ 2 := by
  simp only [bornRule, Complex.normSq_eq_norm_sq]

/-- Born rule is non-negative. -/
theorem bornRule_nonneg (z : ℂ) : 0 ≤ bornRule z := Complex.normSq_nonneg z

/-- Born rule of a product is the product of Born rules.
This follows from |z₁ · z₂|² = |z₁|² · |z₂|². -/
theorem bornRule_mul (z₁ z₂ : ℂ) : bornRule (z₁ * z₂) = bornRule z₁ * bornRule z₂ := by
  simp only [bornRule, Complex.normSq_mul]

/-- Born rule of unit complex number is 1. -/
theorem bornRule_of_unit (θ : ℝ) : bornRule (Complex.exp (θ * I)) = 1 := by
  simp only [bornRule, normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow]

/-- The Feynman sum rule: amplitudes add as complex numbers.
This is Equation (18): u ⊕ v = (u₁ + v₁, u₂ + v₂)

Combined with the Born rule, this gives quantum interference. -/
theorem feynmanSumRule (z₁ z₂ : ℂ) :
    bornRule (z₁ + z₂) = bornRule z₁ + bornRule z₂ + 2 * (z₁.re * z₂.re + z₁.im * z₂.im) := by
  simp only [bornRule, Complex.normSq_add]
  congr 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]

/-- Interference term in the Feynman sum rule.
When z₁ = exp(iθ) and z₂ = exp(iφ), the interference term is 2cos(θ - φ). -/
theorem interference_term (θ φ : ℝ) :
    let z₁ := Complex.exp (θ * I)
    let z₂ := Complex.exp (φ * I)
    2 * (z₁.re * z₂.re + z₁.im * z₂.im) = 2 * Real.cos (θ - φ) := by
  show 2 * ((Complex.exp (θ * I)).re * (Complex.exp (φ * I)).re +
            (Complex.exp (θ * I)).im * (Complex.exp (φ * I)).im) = 2 * Real.cos (θ - φ)
  simp [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, Real.cos_sub, mul_add]

/-- The integral of cos over a full period is zero.
This is the key fact: the mean interference vanishes for uniform phases. -/
theorem integral_cos_full_period : ∫ x in (0 : ℝ)..(2 * π), Real.cos x = 0 := by
  rw [integral_cos]
  simp [Real.sin_two_pi, Real.sin_zero]

/-- Mean of |exp(iθ) + exp(iφ)|² over uniform phases.

For independent uniform phases θ, φ ∈ [0, 2π):
  |e^{iθ} + e^{iφ}|² = 1 + 1 + 2cos(θ - φ)

The mean over uniform phases is:
  ⟨|e^{iθ} + e^{iφ}|²⟩ = 2 + 2⟨cos(θ - φ)⟩ = 2 + 0 = 2

This verifies the mean-rate constraint for the chosen squared-norm readout.
-/
theorem mean_bornRule_sum_unit_phases :
    ∀ θ : ℝ, (1 / (2 * π)) * ∫ φ in (0 : ℝ)..(2 * π),
      bornRule (Complex.exp (θ * I) + Complex.exp ((φ : ℝ) * I)) = 2 := by
  intro θ
  have h1 : ∀ φ : ℝ, bornRule (Complex.exp (θ * I) + Complex.exp (φ * I)) =
      2 + 2 * Real.cos (θ - φ) := by
    intro φ
    rw [feynmanSumRule]
    simp only [bornRule_of_unit]
    have := interference_term θ φ
    simp only at this
    linarith [this]
  simp_rw [h1]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    have hcos : ∫ φ in (0 : ℝ)..(2 * π), Real.cos (θ - φ) = 0 := by
      have h := integral_cos (a := θ - 2 * π) (b := θ)
      simp only [Real.sin_sub_two_pi, sub_self] at h
      rw [intervalIntegral.integral_comp_sub_left (fun x => Real.cos x) θ]
      simp only [sub_zero]
      exact h
    rw [intervalIntegral.integral_const_mul, hcos]
    simp only [mul_zero, add_zero]
    field_simp
  · exact intervalIntegrable_const
  · apply IntervalIntegrable.const_mul
    exact Continuous.intervalIntegrable (by continuity) _ _

/-- SELECTION THEOREM:
The paper argues that among the three product types, only μ < 0 (complex-type)
gives a positive-definite conjugate norm, which is required for probability
interpretation in quantum mechanics.

This is the key result from TwoDimClassification.selection_theorem:
  μ < 0 ↔ (∀ z, 0 ≤ N(z) ∧ (N(z) = 0 → z = 0))

Note: All μ < 0 are isomorphic (via rescaling), so μ = -1 is just the canonical
representative. The physical content is μ < 0, not specifically μ = -1.
-/
theorem selection_complex_over_dual_split :
    ∀ μ : ℝ, μ < 0 ↔
      (∀ z : Algebra.TwoDimClassification.MuAlgebra μ,
        0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) := by
  intro μ
  exact (Algebra.TwoDimClassification.selection_theorem μ).symm

/-- The conjugate norm is multiplicative for ANY μ (not selective).
This was incorrectly claimed as selective in an earlier version. -/
theorem norm_multiplicative_all_mu (μ : ℝ) (u v : ℝ × ℝ) :
    let prod := bilinearProduct μ u v
    (u.1^2 - μ * u.2^2) * (v.1^2 - μ * v.2^2) = prod.1^2 - μ * prod.2^2 := by
  simp only [bilinearProduct]
  ring

end BornRule

section UnifiedView

/-- The unified structure: FOI's algebraic axioms apply in all three domains.

The paper's checklist (Table in Section 5) shows:
- Measure: Closure/Comm/Assoc/Limitless for ⊕
- Probability: + Closure/Right-dist for ∘ (chaining)
- Quantum: + Associativity for ∘ (needed to select among product rules)
-/
structure UnifiedFOIContext where
  /-- The underlying K&S semigroup (from FOI) -/
  α : Type*
  /-- K&S semigroup instance (identity-free) -/
  inst_base : KSSemigroupBase α
  /-- Representation theorem instance -/
  inst_repr : @HasRepresentationTheorem α inst_base
  /-- The representation map from FOI -/
  Θ : α → ℝ
  /-- Θ preserves order -/
  Θ_order : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b
  /-- Θ is additive -/
  Θ_add : ∀ x y : α, Θ (@KSSemigroupBase.op α inst_base x y) = Θ x + Θ y

/-- From a UnifiedFOIContext, extract the sum rule (FOI → Measure). -/
theorem unifiedContext_sumRule (ctx : UnifiedFOIContext) :
    ∀ x y, ctx.Θ (@KSSemigroupBase.op ctx.α ctx.inst_base x y) = ctx.Θ x + ctx.Θ y :=
  ctx.Θ_add

/-- From a UnifiedFOIContext, extract probability proportions (FOI → Probability). -/
theorem unifiedContext_productRule (ctx : UnifiedFOIContext) (u v w : ctx.α) :
    @proportionRepresentation ctx.α ctx.inst_base ctx.Θ w u =
    @proportionRepresentation ctx.α ctx.inst_base ctx.Θ v u *
    @proportionRepresentation ctx.α ctx.inst_base ctx.Θ w v :=
  @productRule ctx.α ctx.inst_base ctx.Θ u v w

/-- For quantum, we extend to complex amplitudes with the Born rule. -/
noncomputable def quantumAmplitude (ctx : UnifiedFOIContext) (phase : ℝ) (x : ctx.α) : ℂ :=
  Complex.exp (phase * I) * Real.exp (ctx.Θ x)

/-- The Born rule gives the rate from the amplitude. -/
theorem quantum_bornRule (ctx : UnifiedFOIContext) (phase : ℝ) (x : ctx.α) :
    bornRule (quantumAmplitude ctx phase x) = Real.exp (2 * ctx.Θ x) := by
  simp only [quantumAmplitude, bornRule]
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow, one_mul]
  simp only [Complex.normSq_ofReal]
  rw [← Real.exp_add, two_mul]

end UnifiedView

end KnuthSkilling.SymmetricalFoundation
