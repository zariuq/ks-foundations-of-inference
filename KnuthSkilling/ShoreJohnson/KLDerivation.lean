import KnuthSkilling.ShoreJohnson.Objective
import KnuthSkilling.ShoreJohnson.Constraints
import KnuthSkilling.ShoreJohnson.Theorem
import KnuthSkilling.ShoreJohnson.Bridge
import KnuthSkilling.ShoreJohnson.AppendixTheoremI

/-!
# Separable inference profiles and the conditional KL conclusion

This composition theorem assumes a separable stationarity bridge, ratio form,
Cauchy equation and measurability. It does not derive those premises from the
operator axioms. The conclusion is restricted to positive priors and candidates;
constraints may still admit boundary competitors. There is no global positivity
requirement on inferred posteriors.

The scale obtained from Cauchy rigidity is a real constant. Identifying its
minimizers with ordinary KL additionally requires a positive scale.
-/

namespace KnuthSkilling.ShoreJohnson.KLDerivation

open Classical
open Finset BigOperators

open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.Theorem
open KnuthSkilling.ShoreJohnson.KL
open KnuthSkilling.ShoreJohnson.AppendixTheoremI
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Proof

/-! ## Explicit assumption bundle -/

structure SeparableKLProfile where
  /-- Inference relation; no operator axioms are hidden in this field. -/
  I : Inference.InferenceMethod
  /-- Objective functional realizing inference on expected-value constraint sets. -/
  F : ObjectiveFunctional
  /-- Atom divergence used for the sum-form objective `ofAtom d`. -/
  d : ℝ → ℝ → ℝ
  /-- Objective realization on expected-value constraints with positive priors. -/
  realizesEV : RealizesEVPositive I F
  /-- Supplied stationarity certificates comparing the objective with the atom sum. -/
  appendix : SJAppendixAssumptions F d
  /-- Zero-source regularity, separate from product additivity. -/
  regularAtom : RegularAtom d
  /-- Ratio-form hypothesis: `d(w,u)=w*g(w/u)` for `w,u>0`. -/
  ratio : Theorem.RatioForm d
  /-- Multiplicative Cauchy equation for the ratio kernel on `(0,∞)`. -/
  gMul : MulCauchyOnPos ratio.g
  /-- Regularity gate excluding Hamel-basis pathologies. -/
  gMeas : Measurable ratio.g
  /-- Regularity gate for the probability-domain log conclusion. -/
  d1Meas : Measurable (d 1)

/-! ## Deriving Cauchy equation for d(1,·) from ratio form + MulCauchyOnPos -/

/-- From `RatioForm` and `MulCauchyOnPos`, derive the multiplicative Cauchy equation for `d(1, ·)`. -/
theorem d_one_cauchy_of_ratioForm_mulCauchyOnPos (d : ℝ → ℝ → ℝ) (ratio : Theorem.RatioForm d)
    (gMul : MulCauchyOnPos ratio.g) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₁ ≤ 1 → 0 < q₂ → q₂ ≤ 1 → d 1 (q₁ * q₂) = d 1 q₁ + d 1 q₂ := by
  intro q₁ q₂ hq₁_pos _hq₁_le1 hq₂_pos _hq₂_le1
  -- d(1, q) = g(1/q) for q > 0 (from ratio form)
  have h1 : d 1 q₁ = ratio.g q₁⁻¹ := by
    have := ratio.eq_mul_g_div 1 q₁ one_pos hq₁_pos
    simp only [one_mul, one_div] at this
    exact this
  have h2 : d 1 q₂ = ratio.g q₂⁻¹ := by
    have := ratio.eq_mul_g_div 1 q₂ one_pos hq₂_pos
    simp only [one_mul, one_div] at this
    exact this
  have hprod_pos : 0 < q₁ * q₂ := mul_pos hq₁_pos hq₂_pos
  have h3 : d 1 (q₁ * q₂) = ratio.g (q₁ * q₂)⁻¹ := by
    have := ratio.eq_mul_g_div 1 (q₁ * q₂) one_pos hprod_pos
    simp only [one_mul, one_div] at this
    exact this
  -- (q₁*q₂)⁻¹ = q₁⁻¹ * q₂⁻¹
  have hrecip : (q₁ * q₂)⁻¹ = q₁⁻¹ * q₂⁻¹ := by rw [mul_inv_rev, mul_comm]
  -- g(q₁⁻¹ * q₂⁻¹) = g(q₁⁻¹) + g(q₂⁻¹) by MulCauchyOnPos
  have hq₁_inv_pos : 0 < q₁⁻¹ := inv_pos.mpr hq₁_pos
  have hq₂_inv_pos : 0 < q₂⁻¹ := inv_pos.mpr hq₂_pos
  have hg_cauchy := gMul q₁⁻¹ q₂⁻¹ hq₁_inv_pos hq₂_inv_pos
  -- Combine
  calc d 1 (q₁ * q₂)
      = ratio.g (q₁ * q₂)⁻¹ := h3
    _ = ratio.g (q₁⁻¹ * q₂⁻¹) := by rw [hrecip]
    _ = ratio.g q₁⁻¹ + ratio.g q₂⁻¹ := hg_cauchy
    _ = d 1 q₁ + d 1 q₂ := by rw [← h1, ← h2]

/-! ## KL conclusion under explicit assumptions -/

theorem log_on_probabilities (h : SeparableKLProfile) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → h.d 1 q = C * Real.log q := by
  -- Derive Cauchy equation for d(1, ·) from ratio form + MulCauchyOnPos
  have hCauchy := d_one_cauchy_of_ratioForm_mulCauchyOnPos h.d h.ratio h.gMul
  -- Apply the general Cauchy → log theorem
  exact mul_cauchy_Ioc_eq_const_mul_log (h.d 1) hCauchy h.d1Meas

theorem d_eq_const_mul_klAtom (h : SeparableKLProfile) :
    ∃ C : ℝ, ∀ w u : ℝ, 0 < w → 0 < u → h.d w u = C * klAtom w u := by
  exact ratioForm_eq_const_mul_klAtom_of_measurable h.d h.ratio h.gMul h.gMeas

/-! ## From atom-level KL to objective-level KL -/

theorem sum_d_eq_const_mul_klAtom_of_posPrior {n : ℕ}
    (d : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u)
    (hReg : RegularAtom d)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (q : ProbDist n) :
    (∑ i : Fin n, d (q.p i) (p.p i)) = ∑ i : Fin n, C * klAtom (q.p i) (p.p i) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hqi : q.p i = 0
  · simpa [hqi, klAtom] using (hReg (p.p i))
  · have hq_pos : 0 < q.p i :=
      lt_of_le_of_ne (q.nonneg i) (Ne.symm hqi)
    have hp_pos : 0 < p.p i := hp i
    simp [hC (q.p i) (p.p i) hq_pos hp_pos, klAtom]

theorem isMinimizer_ofAtom_iff_ofAtom_const_mul_klAtom_of_posPrior {n : ℕ}
    (d : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u)
    (hReg : RegularAtom d)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (S : Inference.ConstraintSet n) (q : ProbDist n) :
    IsMinimizer (ofAtom d) p S q ↔ IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p S q := by
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hq_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q
    have hq'_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q'
    dsimp [ofAtom] at hle
    -- Transport the inequality through the pointwise `d = C * klAtom` identities.
    have hle' :
        (∑ i : Fin n, C * klAtom (q.p i) (p.p i)) ≤ ∑ i : Fin n, C * klAtom (q'.p i) (p.p i) := by
      calc
        (∑ i : Fin n, C * klAtom (q.p i) (p.p i))
            = ∑ i : Fin n, d (q.p i) (p.p i) := by simpa using hq_eq.symm
        _ ≤ ∑ i : Fin n, d (q'.p i) (p.p i) := hle
        _ = ∑ i : Fin n, C * klAtom (q'.p i) (p.p i) := by simpa using hq'_eq
    simpa [ofAtom] using hle'
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hq_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q
    have hq'_eq := sum_d_eq_const_mul_klAtom_of_posPrior d C hC hReg p hp q'
    dsimp [ofAtom] at hle
    have hle' :
        (∑ i : Fin n, d (q.p i) (p.p i)) ≤ ∑ i : Fin n, d (q'.p i) (p.p i) := by
      calc
        (∑ i : Fin n, d (q.p i) (p.p i))
            = ∑ i : Fin n, C * klAtom (q.p i) (p.p i) := by simpa using hq_eq
        _ ≤ ∑ i : Fin n, C * klAtom (q'.p i) (p.p i) := hle
        _ = ∑ i : Fin n, d (q'.p i) (p.p i) := by simpa using hq'_eq.symm
    simpa [ofAtom] using hle'

/-! ## Inference-level conclusion (for positive priors) -/

theorem infer_iff_scaledKL_of_identity (h : SeparableKLProfile) (C : ℝ)
    (hC : ∀ w u : ℝ, 0 < w → 0 < u → h.d w u = C * klAtom w u) :
    ∀ {n : ℕ} (p : ProbDist n) (cs : Constraints.EVConstraintSet n)
      (q : ProbDist n), (∀ i, 0 < p.p i) → (∀ i, 0 < q.p i) →
      (h.I.Infer p (Constraints.toConstraintSet cs) q ↔
        IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p (Constraints.toConstraintSet cs) q) := by
  intro n p cs q hp hqPos
  have hInferF :
      h.I.Infer p (Constraints.toConstraintSet cs) q ↔
        IsMinimizer h.F p (Constraints.toConstraintSet cs) q :=
    h.realizesEV.infer_iff_minimizer_ev p cs q hp
  have hKl :
      IsMinimizer (ofAtom h.d) p (Constraints.toConstraintSet cs) q ↔
        IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p (Constraints.toConstraintSet cs) q :=
    isMinimizer_ofAtom_iff_ofAtom_const_mul_klAtom_of_posPrior
      h.d C hC h.regularAtom p hp (Constraints.toConstraintSet cs) q
  constructor
  · intro hInfer
    have hMinF : IsMinimizer h.F p (Constraints.toConstraintSet cs) q := hInferF.1 hInfer
    have hq_mem : q ∈ Constraints.toConstraintSet cs := hMinF.1
    have hMinD : IsMinimizer (ofAtom h.d) p (Constraints.toConstraintSet cs) q :=
      (isMinimizer_iff_isMinimizer_ofAtom_of_pos h.appendix p hp cs q hq_mem hqPos).1 hMinF
    have hMinKl : IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p
        (Constraints.toConstraintSet cs) q := (hKl.1 hMinD)
    exact hMinKl
  · intro hMinKl
    have hq_mem : q ∈ Constraints.toConstraintSet cs := hMinKl.1
    have hMinD : IsMinimizer (ofAtom h.d) p (Constraints.toConstraintSet cs) q :=
      (hKl.2 hMinKl)
    have hMinF : IsMinimizer h.F p (Constraints.toConstraintSet cs) q :=
      (isMinimizer_iff_isMinimizer_ofAtom_of_pos h.appendix p hp cs q hq_mem hqPos).2 hMinD
    exact (hInferF.2 hMinF)


theorem infer_iff_scaledKL_of_positive (h : SeparableKLProfile) :
    ∃ C : ℝ, ∀ {n : ℕ} (p : ProbDist n) (cs : Constraints.EVConstraintSet n)
      (q : ProbDist n), (∀ i, 0 < p.p i) → (∀ i, 0 < q.p i) →
      (h.I.Infer p (Constraints.toConstraintSet cs) q ↔
        IsMinimizer (ofAtom (fun w u => C * klAtom w u)) p (Constraints.toConstraintSet cs) q) := by
  obtain ⟨C, hC⟩ := d_eq_const_mul_klAtom h
  exact ⟨C, infer_iff_scaledKL_of_identity h C hC⟩


end KnuthSkilling.ShoreJohnson.KLDerivation
