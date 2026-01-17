import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mettapedia.ProbabilityTheory.KnuthSkilling.VariationalTheorem

/-!
# K&S Section 6: Divergence (Variational Potential Application)

This file formalizes the **divergence formula** from K&S Section 6 "Variation".

## Background

From Appendix C (VariationalTheorem.lean), we have the general entropy form:
```
H_i(m_i) = A_i + B_i·m_i + C_i·(m_i·log(m_i) - m_i)
```

Section 6 specializes this to define **divergence** - a measure of how much a destination
measure `w` differs from a source measure `u`.

## The Divergence Formula (K&S Eq. 44)

Setting:
- `C = 1` (ensures H has a minimum, not maximum)
- `B_i = -log(u_i)` (places the unconstrained minimum at `u`)
- `A_i = u_i` (makes the minimum value zero)

Yields the **divergence formula**:
```
H(w | u) = Σ_i (u_i - w_i + w_i·log(w_i/u_i))
```

## Properties

1. **Non-negativity**: `H(w|u) ≥ 0`
2. **Zero iff equal**: `H(w|u) = 0 ↔ w = u`
3. **Not symmetric**: `H(w|u) ≠ H(u|w)` in general
4. **Not a metric**: Triangle inequality fails

These properties show that divergence quantifies "from-to" separation, but cannot
define a geometric distance.

## References

- K&S "Foundations of Inference" (2012), Section 6 "Variation"
- Especially Section 6.1 "Divergence and Distance"
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Divergence

open Real
open scoped Topology

/-! ## Single-Variable Divergence Function

The per-atom divergence function `φ(w, u) = u - w + w·log(w/u)`.
-/

/-- The **per-atom divergence function**: `φ(w, u) = u - w + w·log(w/u)`.

This measures how much a single destination value `w` diverges from source `u`.
When `w = u`, we have `φ(u, u) = u - u + u·log(1) = 0`. -/
noncomputable def atomDivergence (w u : ℝ) : ℝ :=
  u - w + w * log (w / u)

/-- Alternative form: `φ(w, u) = u - w + w·log(w) - w·log(u)`. -/
theorem atomDivergence_alt (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    atomDivergence w u = u - w + w * log w - w * log u := by
  unfold atomDivergence
  rw [log_div (ne_of_gt hw) (ne_of_gt hu)]
  ring

/-- When `w = u`, divergence is zero. -/
theorem atomDivergence_self (u : ℝ) (hu : 0 < u) : atomDivergence u u = 0 := by
  unfold atomDivergence
  simp [log_one, ne_of_gt hu]

/-- The key inequality: `t - 1 - log t ≥ 0` for `t > 0`, with equality iff `t = 1`.

This is the standard "log inequality" from information theory. -/
theorem log_ineq (t : ℝ) (ht : 0 < t) : 0 ≤ t - 1 - log t := by
  have h := add_one_le_exp (log t)
  rw [exp_log ht] at h
  linarith

/-- Strict version: `t - 1 - log t > 0` when `t ≠ 1`. -/
theorem log_ineq_strict (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) : 0 < t - 1 - log t := by
  have hlog_ne : log t ≠ 0 := log_ne_zero_of_pos_of_ne_one ht ht1
  have h := add_one_lt_exp hlog_ne
  rw [exp_log ht] at h
  linarith

/-- The divergence function is non-negative for positive arguments.

**Proof**: Let `s = u/w`. Then `φ(w,u) = w·(s - 1 - log(s))` where `s > 0`.
By the log inequality, `s - 1 - log(s) ≥ 0`, hence `φ(w,u) ≥ 0`. -/
theorem atomDivergence_nonneg (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    0 ≤ atomDivergence w u := by
  unfold atomDivergence
  -- Rewrite: u - w + w·log(w/u) = w·(u/w - 1 + log(w/u))
  --                              = w·(u/w - 1 - log(u/w))
  have hw_ne : w ≠ 0 := ne_of_gt hw
  have hu_ne : u ≠ 0 := ne_of_gt hu
  let s := u / w
  have hs : 0 < s := div_pos hu hw
  -- φ(w,u) = w * (s - 1 - log s)
  have hrewrite : u - w + w * log (w / u) = w * (s - 1 - log s) := by
    simp only [s]
    rw [log_div hw_ne hu_ne]
    have : log w - log u = -(log u - log w) := by ring
    rw [this, ← log_div hu_ne hw_ne]
    field_simp
    ring
  rw [hrewrite]
  exact mul_nonneg (le_of_lt hw) (log_ineq s hs)

/-- Divergence equals zero if and only if `w = u`. -/
theorem atomDivergence_eq_zero_iff (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    atomDivergence w u = 0 ↔ w = u := by
  constructor
  · -- If φ(w,u) = 0, then w = u
    intro h
    unfold atomDivergence at h
    have hw_ne : w ≠ 0 := ne_of_gt hw
    have hu_ne : u ≠ 0 := ne_of_gt hu
    let s := u / w
    have hs : 0 < s := div_pos hu hw
    -- φ(w,u) = w * (s - 1 - log s) = 0
    have hrewrite : u - w + w * log (w / u) = w * (s - 1 - log s) := by
      simp only [s]
      rw [log_div hw_ne hu_ne]
      have : log w - log u = -(log u - log w) := by ring
      rw [this, ← log_div hu_ne hw_ne]
      field_simp
      ring
    rw [hrewrite] at h
    -- w > 0 and w * (s - 1 - log s) = 0 implies s - 1 - log s = 0
    have hcore : s - 1 - log s = 0 := by
      have := mul_eq_zero.mp h
      cases this with
      | inl hw0 => exact absurd hw0 hw_ne
      | inr h' => exact h'
    -- s - 1 - log s = 0 implies s = 1 (since strict inequality holds for s ≠ 1)
    by_contra hw_ne_u
    -- s ≠ 1 because s = u/w and w ≠ u
    have hs1 : s ≠ 1 := by
      simp only [s]
      intro heq
      have : u = w := by field_simp at heq; linarith
      exact hw_ne_u this.symm
    have hstrict := log_ineq_strict s hs hs1
    linarith
  · -- If w = u, then φ(w,u) = 0
    intro heq
    rw [heq]
    exact atomDivergence_self u hu

/-! ## Vector Divergence

For vectors of measures, the total divergence is the sum of per-atom divergences.
-/

/-- **Total divergence** between destination `w` and source `u` (K&S Eq. 44).

`H(w | u) = Σ_i (u_i - w_i + w_i·log(w_i/u_i))`

This is the unique variational potential with the required properties. -/
noncomputable def divergence {n : ℕ} (w u : Fin n → ℝ) : ℝ :=
  ∑ i, atomDivergence (w i) (u i)

/-- Divergence is non-negative when all components are positive. -/
theorem divergence_nonneg {n : ℕ} (w u : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i) :
    0 ≤ divergence w u := by
  unfold divergence
  apply Finset.sum_nonneg
  intro i _
  exact atomDivergence_nonneg (w i) (u i) (hw i) (hu i)

/-- Divergence equals zero if and only if `w = u` (pointwise). -/
theorem divergence_eq_zero_iff {n : ℕ} (w u : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i) :
    divergence w u = 0 ↔ w = u := by
  constructor
  · -- If divergence = 0, then w = u
    intro h
    unfold divergence at h
    -- Sum of non-negative terms equals zero → each term is zero
    have hall_zero : ∀ i, atomDivergence (w i) (u i) = 0 := by
      have hsum_nonneg : ∀ i ∈ Finset.univ, 0 ≤ atomDivergence (w i) (u i) := fun i _ =>
        atomDivergence_nonneg (w i) (u i) (hw i) (hu i)
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg hsum_nonneg).mp h i (Finset.mem_univ i)
    ext i
    exact (atomDivergence_eq_zero_iff (w i) (u i) (hw i) (hu i)).mp (hall_zero i)
  · -- If w = u, then divergence = 0
    intro heq
    unfold divergence
    simp only [heq]
    apply Finset.sum_eq_zero
    intro i _
    exact atomDivergence_self (u i) (hu i)

/-! ## Non-Symmetry: Divergence is Not a Metric

K&S emphasizes that divergence is NOT symmetric and does NOT satisfy the triangle inequality.
Hence it cannot be a geometric distance.
-/

/-- **Divergence is not symmetric**: There exist `w, u` with `H(w|u) ≠ H(u|w)`.

This is easy to see: `φ(w, u) = u - w + w·log(w/u)` while `φ(u, w) = w - u + u·log(u/w)`.
These are generally different.

**Concrete example**: `φ(1, 2) = 1 - log(2) ≈ 0.307` while `φ(2, 1) = -1 + 2·log(2) ≈ 0.386`. -/
theorem divergence_not_symmetric :
    ∃ w u : ℝ, 0 < w ∧ 0 < u ∧ atomDivergence w u ≠ atomDivergence u w := by
  use 1, 2
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold atomDivergence
  -- φ(1, 2) = 2 - 1 + 1·log(1/2) = 1 - log(2)
  -- φ(2, 1) = 1 - 2 + 2·log(2/1) = -1 + 2·log(2)
  -- If equal: 1 - log(2) = -1 + 2·log(2), i.e., 2 = 3·log(2), i.e., log(2) = 2/3
  -- But log(2) ≠ 2/3 (can verify: exp(2/3) ≈ 1.95 ≠ 2)
  intro h
  have hlog2_pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  -- Simplify both sides
  simp only [div_one] at h
  have hlog_half : log (1 / 2) = -log 2 := by
    rw [one_div, log_inv]
  rw [hlog_half] at h
  -- From h: 2 - 1 + 1 * (-log 2) = 1 - 2 + 2 * log 2
  -- Simplify: 1 - log 2 = -1 + 2 * log 2
  have heq : log 2 = 2/3 := by linarith
  -- But log 2 ≠ 2/3. We show this via: log 2 > 2/3 because exp(2/3) < 2
  -- This is a numerical fact that requires exp(2/3) ≈ 1.948 < 2
  -- Use mathlib's precise bound: log_two_gt_d9 : 0.6931471803 < log 2
  -- Since 0.6931471803 > 2/3 = 0.666..., we have log 2 ≠ 2/3
  have hlog2_gt : (2 : ℝ) / 3 < log 2 := by
    have h1 : (2 : ℝ) / 3 < 0.6931471803 := by norm_num
    exact lt_trans h1 log_two_gt_d9
  linarith

/-- **Triangle inequality fails**: There exist `w, v, u` with `H(w|u) > H(w|v) + H(v|u)`.

**Concrete example**: With `w = 1`, `v = 2`, `u = 4`:
- `φ(1, 4) = 3 - 2·log(2)`
- `φ(1, 2) + φ(2, 4) = (1 - log 2) + (2 - 2·log 2) = 3 - 3·log(2)`

Since `log 2 > 0`, we have `3 - 2·log 2 > 3 - 3·log 2`. -/
theorem divergence_triangle_fails :
    ∃ w v u : ℝ, 0 < w ∧ 0 < v ∧ 0 < u ∧
      atomDivergence w u > atomDivergence w v + atomDivergence v u := by
  use 1, 2, 4
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  unfold atomDivergence
  -- φ(1, 4) = 4 - 1 + 1·log(1/4) = 3 + log(1/4) = 3 - 2·log 2
  -- φ(1, 2) = 2 - 1 + 1·log(1/2) = 1 - log 2
  -- φ(2, 4) = 4 - 2 + 2·log(2/4) = 2 + 2·log(1/2) = 2 - 2·log 2
  -- Sum: (1 - log 2) + (2 - 2·log 2) = 3 - 3·log 2
  -- Need: 3 - 2·log 2 > 3 - 3·log 2, i.e., log 2 > 0
  have hlog2_pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog_quarter : log (1 / 4) = -2 * log 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [one_div, log_inv, h4, log_pow]; ring
  have hlog_half : log (1 / 2) = -log 2 := by
    rw [one_div, log_inv]
  have hlog_half' : log (2 / 4) = -log 2 := by
    rw [show (2 : ℝ) / 4 = 1 / 2 by norm_num, hlog_half]
  simp only [hlog_quarter, hlog_half, hlog_half']
  linarith

/-! ## Derivational Connection to entropyForm

The divergence formula is NOT arbitrary - it is **uniquely determined** by the K&S variational
framework. From `VariationalTheorem.lean`:

1. The variational equation `H'(m_x · m_y) = λ(m_x) + μ(m_y)` forces `H(m) = A + Bm + C(m log m - m)`
   (this is `variationalEquation_solution`)

2. The parameters `A, B, C` are then **forced** by requirements:
   - `C > 0`: ensures a minimum (not maximum) — `entropyForm_second_deriv_pos`
   - `B = -log(u)`: places the minimum at `m = u` — `entropyForm_critical_at_u`
   - `A = u`: makes the minimum value zero — `entropyForm_minimum_value_zero`

3. These constraints are summarized in `divergence_parameters_forced`.

The theorems below verify the algebraic equivalence and the derivational connection.
-/

/-- Divergence as a specialization of entropyForm (algebraic verification).

Setting `A = u`, `B = -log(u)`, `C = 1` in `entropyForm A B C` gives:
`H(w) = u + (-log u)·w + 1·(w·log w - w) = u - w·log u + w·log w - w = u - w + w·log(w/u)`

which is exactly `atomDivergence w u`. -/
theorem atomDivergence_eq_entropyForm (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    atomDivergence w u =
      VariationalTheorem.entropyForm u (-log u) 1 w := by
  unfold atomDivergence VariationalTheorem.entropyForm
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have hw_ne : w ≠ 0 := ne_of_gt hw
  rw [log_div hw_ne hu_ne]
  ring

/-- The divergence formula achieves its minimum at `w = u`.

This follows from `entropyForm_critical_at_u`: with `B = -log(u)` and `C = 1`,
the critical point of `entropyForm` is at `exp(-B/C) = exp(log u) = u`. -/
theorem atomDivergence_minimized_at (u : ℝ) (hu : 0 < u) :
    ∀ w : ℝ, 0 < w → atomDivergence u u ≤ atomDivergence w u := by
  intro w hw
  rw [atomDivergence_self u hu]
  exact atomDivergence_nonneg w u hw hu

/-- The minimum value of divergence is zero (at `w = u`).

This is `entropyForm_minimum_value_zero` restated for divergence. -/
theorem atomDivergence_min_value_zero (u : ℝ) (hu : 0 < u) :
    atomDivergence u u = 0 := atomDivergence_self u hu

/-! ## Gibbs' Inequality (Information-Theoretic Form)

When `w` and `u` are probability distributions (sum to 1), the divergence becomes
the Kullback-Leibler divergence, and non-negativity is known as Gibbs' inequality.
-/

/-- For probability distributions, divergence simplifies to KL divergence.

If `Σ w_i = 1` and `Σ u_i = 1`, then:
`H(w|u) = Σ (u_i - w_i + w_i·log(w_i/u_i)) = Σ w_i·log(w_i/u_i)`

since `Σ u_i - Σ w_i = 1 - 1 = 0`. -/
theorem divergence_eq_kl_for_prob {n : ℕ} (w u : Fin n → ℝ)
    (hw_sum : ∑ i, w i = 1) (hu_sum : ∑ i, u i = 1) :
    divergence w u = ∑ i, w i * log (w i / u i) := by
  unfold divergence atomDivergence
  -- The divergence sum is Σ (u_i - w_i + w_i·log(w_i/u_i))
  -- = Σ u_i - Σ w_i + Σ w_i·log(w_i/u_i)  (splitting sums)
  -- = 1 - 1 + Σ w_i·log(w_i/u_i)          (using hw_sum, hu_sum)
  -- = Σ w_i·log(w_i/u_i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hw_sum, hu_sum, sub_self, zero_add]

/-! ## Connection to Mathlib's KL Divergence

Mathlib defines `InformationTheory.klFun x = x * log x + 1 - x` (the per-point KL function).
Our `atomDivergence w u` relates to this by: `atomDivergence w u = u * klFun(w/u)`.

This establishes that our K&S-derived divergence coincides with the standard information-theoretic
KL divergence, validating that K&S's axiomatic approach reproduces the correct formula.
-/

/-- Our `atomDivergence` equals mathlib's `klFun` scaled by `u`.

`atomDivergence w u = u - w + w·log(w/u) = u · klFun(w/u)`

where `klFun t = t·log(t) + 1 - t`. -/
theorem atomDivergence_eq_mul_klFun (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    atomDivergence w u = u * InformationTheory.klFun (w / u) := by
  unfold atomDivergence InformationTheory.klFun
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have hw_ne : w ≠ 0 := ne_of_gt hw
  rw [log_div hw_ne hu_ne]
  field_simp [hu_ne]
  ring

/-- Corollary: Non-negativity via mathlib's `klFun_nonneg`.

Since `klFun t ≥ 0` for `t ≥ 0`, and `u > 0`, we have `atomDivergence w u ≥ 0`. -/
theorem atomDivergence_nonneg' (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    0 ≤ atomDivergence w u := by
  rw [atomDivergence_eq_mul_klFun w u hw hu]
  exact mul_nonneg (le_of_lt hu) (InformationTheory.klFun_nonneg (le_of_lt (div_pos hw hu)))

/-! ## Extension to Zero (Handling w = 0)

The convention `0 * log(0) = 0` is standard in information theory. This allows us to
extend `atomDivergence` continuously to the boundary case `w = 0`.

Mathematically: `lim_{w → 0⁺} w·log(w/u) = 0` since `lim_{x → 0⁺} x·log(x) = 0`.
Hence `atomDivergence 0 u` can be continuously extended to `u`.

Using the relationship `atomDivergence w u = u * klFun(w/u)` and mathlib's `klFun 0 = 1`:
- `atomDivergenceExt 0 u = u * klFun(0) = u * 1 = u`
-/

/-- Extended per-atom divergence that handles `w = 0` via the standard convention.

When `w = 0`: `φ(0, u) = u` (continuous extension via `0 * log(0) = 0`).
When `w > 0`: `φ(w, u) = u - w + w·log(w/u)` (original formula).

This is equivalent to `u * klFun(w/u)` extended to `w = 0`. -/
noncomputable def atomDivergenceExt (w u : ℝ) : ℝ :=
  if w = 0 then u else u - w + w * log (w / u)

/-- `atomDivergenceExt` agrees with `atomDivergence` for positive `w`. -/
theorem atomDivergenceExt_eq_atomDivergence (w u : ℝ) (hw : 0 < w) :
    atomDivergenceExt w u = atomDivergence w u := by
  simp only [atomDivergenceExt, ne_of_gt hw, ↓reduceIte, atomDivergence]

/-- `atomDivergenceExt 0 u = u`. -/
@[simp]
theorem atomDivergenceExt_zero (u : ℝ) : atomDivergenceExt 0 u = u := by
  simp only [atomDivergenceExt, ↓reduceIte]

/-- `atomDivergenceExt` equals `u * klFun(w/u)` when `u > 0` and `w ≥ 0`.

This is the fundamental relationship connecting our K&S-derived formula to mathlib's `klFun`. -/
theorem atomDivergenceExt_eq_mul_klFun (w u : ℝ) (hw : 0 ≤ w) (hu : 0 < u) :
    atomDivergenceExt w u = u * InformationTheory.klFun (w / u) := by
  rcases hw.eq_or_lt with rfl | hw_pos
  · -- Case w = 0: klFun(0) = 1, so u * klFun(0) = u
    simp only [atomDivergenceExt_zero, zero_div, InformationTheory.klFun_zero, mul_one]
  · -- Case w > 0: use the relationship proven earlier
    rw [atomDivergenceExt_eq_atomDivergence w u hw_pos]
    exact atomDivergence_eq_mul_klFun w u hw_pos hu

/-- `atomDivergenceExt` is non-negative for `w ≥ 0` and `u > 0`. -/
theorem atomDivergenceExt_nonneg (w u : ℝ) (hw : 0 ≤ w) (hu : 0 < u) :
    0 ≤ atomDivergenceExt w u := by
  rw [atomDivergenceExt_eq_mul_klFun w u hw hu]
  exact mul_nonneg (le_of_lt hu) (InformationTheory.klFun_nonneg (div_nonneg hw (le_of_lt hu)))

/-- `atomDivergenceExt w u = 0 ↔ w = u` for `w ≥ 0` and `u > 0`. -/
theorem atomDivergenceExt_eq_zero_iff (w u : ℝ) (hw : 0 ≤ w) (hu : 0 < u) :
    atomDivergenceExt w u = 0 ↔ w = u := by
  rw [atomDivergenceExt_eq_mul_klFun w u hw hu]
  have hu_ne : u ≠ 0 := ne_of_gt hu
  constructor
  · intro h
    -- u * klFun(w/u) = 0 with u > 0 implies klFun(w/u) = 0
    have hkl : InformationTheory.klFun (w / u) = 0 := by
      have := mul_eq_zero.mp h
      cases this with
      | inl hu0 => exact absurd hu0 hu_ne
      | inr h' => exact h'
    -- klFun(w/u) = 0 ↔ w/u = 1 for w/u ≥ 0
    rw [InformationTheory.klFun_eq_zero_iff (div_nonneg hw (le_of_lt hu))] at hkl
    field_simp at hkl
    exact hkl
  · intro heq
    rw [heq, div_self hu_ne, InformationTheory.klFun_one, mul_zero]

/-- The function `atomDivergenceExt w u` equals `u * klFun(w/u)` for all `w`. -/
theorem atomDivergenceExt_eq_klFun_forall (w u : ℝ) (hu : 0 < u) :
    atomDivergenceExt w u = u * InformationTheory.klFun (w / u) := by
  by_cases hw : w = 0
  · simp only [hw, atomDivergenceExt_zero, zero_div, InformationTheory.klFun_zero, mul_one]
  · simp only [atomDivergenceExt, hw, ↓reduceIte, InformationTheory.klFun]
    have hu_ne : u ≠ 0 := ne_of_gt hu
    rw [log_div hw hu_ne]
    field_simp [hu_ne]
    ring

/-- Continuity of `atomDivergenceExt` in `w` at `w = 0` (for fixed `u > 0`).

This is the key result showing our extension is mathematically justified.
It follows from `continuous_klFun` and the relationship `atomDivergenceExt w u = u * klFun(w/u)`. -/
theorem continuousAt_atomDivergenceExt_zero (u : ℝ) (hu : 0 < u) :
    ContinuousAt (fun w => atomDivergenceExt w u) 0 := by
  have heq : (fun w => atomDivergenceExt w u) = (fun w => u * InformationTheory.klFun (w / u)) :=
    funext (fun w => atomDivergenceExt_eq_klFun_forall w u hu)
  rw [heq]
  apply Continuous.continuousAt
  apply Continuous.mul continuous_const
  apply InformationTheory.continuous_klFun.comp
  exact continuous_id.div_const u

/-- `atomDivergenceExt` is continuous on `[0, ∞)` in `w` (for fixed `u > 0`). -/
theorem continuous_atomDivergenceExt (u : ℝ) (hu : 0 < u) :
    Continuous (fun w => atomDivergenceExt w u) := by
  have heq : (fun w => atomDivergenceExt w u) = (fun w => u * InformationTheory.klFun (w / u)) :=
    funext (fun w => atomDivergenceExt_eq_klFun_forall w u hu)
  rw [heq]
  apply Continuous.mul continuous_const
  apply InformationTheory.continuous_klFun.comp
  exact continuous_id.div_const u

/-! ## Countable Sum Extension (ℕ → ℝ)

For infinite-dimensional cases, we extend divergence to countable sums using
summability conditions. This connects to the measure-theoretic setting.
-/

/-- Infinite-dimensional divergence for sequences with summability conditions.

`divergenceInf w u = Σ_{n : ℕ} atomDivergenceExt (w n) (u n)`

where we require the sum to converge. -/
noncomputable def divergenceInf (w u : ℕ → ℝ) : ℝ :=
  ∑' n, atomDivergenceExt (w n) (u n)

/-- Sufficient condition for `divergenceInf` to be well-defined:
if `w` and `u` are summable with `u` positive, then the divergence sum converges. -/
theorem summable_atomDivergenceExt (w u : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hu : ∀ n, 0 < u n)
    (hu_sum : Summable u)
    (hw_sum : Summable w)
    (hwu_sum : Summable (fun n => w n * |log (w n / u n)|)) :
    Summable (fun n => atomDivergenceExt (w n) (u n)) := by
  -- atomDivergenceExt (w n) (u n) = u n - w n + w n * log (w n / u n) for w n > 0
  -- = u n for w n = 0
  -- The sum is bounded by u n + w n + w n * |log(w n/u n)| which is summable.
  have hbound : Summable (fun n => u n + w n + w n * |log (w n / u n)|) :=
    hu_sum.add hw_sum |>.add hwu_sum
  refine Summable.of_norm_bounded hbound (fun n => ?_)
  -- Need: ‖atomDivergenceExt (w n) (u n)‖ ≤ u n + w n + w n * |log (w n / u n)|
  -- For ℝ, ‖x‖ = |x|
  rw [Real.norm_eq_abs]
  by_cases hwn : w n = 0
  · -- Case w n = 0: atomDivergenceExt 0 (u n) = u n, and |u n| = u n since u n > 0
    simp only [hwn, atomDivergenceExt_zero, abs_of_pos (hu n), zero_mul, add_zero]
    linarith [hu n, hw n]
  · -- Case w n > 0: atomDivergenceExt (w n) (u n) = u n - w n + w n * log (w n / u n)
    have hwn_pos : 0 < w n := (hw n).lt_of_ne' hwn
    simp only [atomDivergenceExt, hwn, ↓reduceIte]
    have hu_nonneg : 0 ≤ u n := le_of_lt (hu n)
    have hw_nonneg : 0 ≤ w n := le_of_lt hwn_pos
    -- |u n - w n + w n * log (w n / u n)| ≤ |u n - w n| + |w n * log (w n / u n)|
    -- ≤ (u n + w n) + w n * |log (w n / u n)|
    -- First, prove |a - b| ≤ a + b for nonneg a, b
    have abs_sub_le_add : |u n - w n| ≤ u n + w n := by
      have h := abs_add_le (u n) (-(w n))
      simp only [abs_neg] at h
      calc |u n - w n| = |u n + -(w n)| := by ring_nf
        _ ≤ |u n| + |w n| := h
        _ = u n + w n := by rw [abs_of_nonneg hu_nonneg, abs_of_nonneg hw_nonneg]
    calc |u n - w n + w n * log (w n / u n)|
        ≤ |u n - w n| + |w n * log (w n / u n)| := abs_add_le _ _
      _ ≤ (u n + w n) + |w n * log (w n / u n)| := by linarith
      _ = (u n + w n) + |w n| * |log (w n / u n)| := by rw [abs_mul]
      _ = (u n + w n) + w n * |log (w n / u n)| := by rw [abs_of_pos hwn_pos]

/-- `atomDivergenceExt 0 0 = 0`. This is the natural boundary behavior. -/
@[simp]
theorem atomDivergenceExt_zero_zero : atomDivergenceExt 0 0 = 0 := by
  simp only [atomDivergenceExt, ↓reduceIte]

/-- For finite support sequences matching on their support, `divergenceInf` equals
the finite `divergence`.

We pad both sequences with zeros outside the support, so `atomDivergenceExt 0 0 = 0`
ensures the tail contributes nothing. -/
theorem divergenceInf_eq_divergence {n : ℕ} (w u : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (_hu : ∀ i, 0 < u i) :
    divergenceInf (fun k => if h : k < n then w ⟨k, h⟩ else 0)
                  (fun k => if h : k < n then u ⟨k, h⟩ else 0) =
    divergence w u := by
  unfold divergenceInf divergence
  -- The tsum equals a finite sum because terms outside Finset.range n are zero
  rw [tsum_eq_sum (s := Finset.range n)]
  · -- The sums match via reindexing
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    -- For i : Fin n, the condition i.val < n is always true
    simp only [i.isLt, ↓reduceDIte]
    exact atomDivergenceExt_eq_atomDivergence (w i) (u i) (hw i)
  · -- For k ∉ Finset.range n, i.e., k ≥ n, the term is 0
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have hk_not_lt : ¬(k < n) := not_lt.mpr hk
    simp only [hk_not_lt, dite_false, atomDivergenceExt_zero_zero]

/-! ## Connection to Measure-Theoretic KL Divergence

Mathlib defines the KL divergence for general measures as:
```
klDiv μ ν = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
```
where `klFun x = x * log x + 1 - x`.

For **discrete measures** on a countable set, this integral becomes a sum:
- If `μ = Σ_n w_n · δ_n` and `ν = Σ_n u_n · δ_n` (weighted counting measures)
- Then `klDiv μ ν = Σ_n u_n · klFun(w_n / u_n) = Σ_n atomDivergenceExt w_n u_n`

This shows that our K&S-derived formula is the discrete case of the general measure-theoretic
KL divergence, validating the derivation from the variational framework.
-/

/-- The measure-theoretic connection: `atomDivergenceExt` equals the integrand
in mathlib's `klDiv` definition.

For a discrete measure at point `n` with weights `w_n` (destination) and `u_n` (source):
- Radon-Nikodym derivative: `dμ/dν (n) = w_n / u_n`
- KL integrand: `klFun(w_n / u_n) * u_n = atomDivergenceExt w_n u_n`

This is exactly what `atomDivergenceExt_eq_mul_klFun` states (when `u_n > 0`). -/
theorem atomDivergenceExt_is_klDiv_integrand (w u : ℝ) (hw : 0 ≤ w) (hu : 0 < u) :
    atomDivergenceExt w u = u * InformationTheory.klFun (w / u) :=
  atomDivergenceExt_eq_mul_klFun w u hw hu

/-- The K&S divergence formula for discrete measures agrees with mathlib's `klDiv`.

For finite discrete measures (represented as `Fin n → ℝ`), our formula
`divergence w u = Σ_i atomDivergence w_i u_i` equals `klDiv μ_w μ_u`
where `μ_w` and `μ_u` are the corresponding discrete probability measures.

This theorem states the formula-level equivalence. The full measure-theoretic
equivalence would require constructing the measures and using mathlib's `klDiv`. -/
theorem divergence_formula_agrees_with_klDiv {n : ℕ} (w u : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 < u i) :
    divergence w u = ∑ i, (u i) * InformationTheory.klFun (w i / u i) := by
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  rcases (hw i).eq_or_lt with hwi | hwi
  · -- w i = 0 case
    simp only [← hwi, atomDivergence, zero_div, log_zero, mul_zero, sub_zero,
               InformationTheory.klFun_zero, mul_one, add_zero]
  · -- w i > 0 case
    exact atomDivergence_eq_mul_klFun (w i) (u i) hwi (hu i)

end Mettapedia.ProbabilityTheory.KnuthSkilling.Divergence
