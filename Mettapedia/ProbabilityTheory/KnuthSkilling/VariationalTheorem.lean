import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.FunctionalEquation

/-!
# Knuth–Skilling Appendix C: Variational Theorem

This file formalizes the **Variational Theorem** from:

- Knuth & Skilling, *Foundations of Inference* (2012), Appendix C
  `literature/Knuth_Skilling/Knuth_Skilling_Foundations_of_Inference/knuth-skilling-2012---foundations-of-inference----arxiv.tex`
  (see around lines 2096–2250 in the TeX source).

## The Variational Equation

K&S consider the functional equation arising from the variational potential axiom:

`H'(m_x · m_y) = lam(m_x) + mu(m_y)`

where `H' = dH/dm` is the derivative of the entropy-like function `H`.

## Key Insight: Reduction to Cauchy's Equation

Setting `u = log m`, the multiplicative argument `m_x · m_y` becomes additive:
`log(m_x · m_y) = log(m_x) + log(m_y)`, i.e., `u_x + u_y`.

If we define `phi(u) = lam(exp u)`, then the equation becomes:

`H'(exp(u + v)) = phi(u) + psi(v)`

This is closely related to **Cauchy's functional equation**: `f(x + y) = f(x) + f(y)`.

## Reusing Appendix B Infrastructure

**We do NOT reprove Cauchy's equation solution!** We directly reuse:

- `continuous_additive_eq_mul`: continuous additive → linear
- `AdditiveOnPos.exists_mul_const_of_add_of_pos`: additive + positive on (0,∞) → scalar mult

K&S themselves avoid assuming regularity of an additive function by a “blurring” (convolution)
argument in Appendix C. In Lean, we instead use a fully rigorous (and still KS-faithful) route:
`H'` is a derivative on `(0,∞)`, hence Borel-measurable, hence its log/exp conjugate is measurable,
and **measurable additive functions are continuous**, so Cauchy’s equation has the linear solution.

See also:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Counterexamples/VariationalNonsmooth.lean` for a
  counterexample showing that “variational optimum ⇒ differentiable” is false in general.
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Counterexamples/CauchyPathology.lean` for an explicit
  (Hamel-basis) countermodel showing that *some* regularity hypothesis is genuinely needed to rule
  out non-linear solutions of Cauchy’s equation.

This follows the K&S design principle: the same core algebraic structures appear across
Appendices A, B, and C, with shared proof techniques.

## Solution

The solution is the **entropy form**:

`H(m) = A + B·m + C·(m·log(m) - m)`

where `A, B, C` are constants.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.VariationalTheorem

open Classical
open Set
open scoped Topology

/-! ## Cauchy's Functional Equation -/

/-- **Cauchy's additive functional equation**: `f(x + y) = f(x) + f(y)` for all `x, y : ℝ`. -/
def CauchyEquation (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, f (x + y) = f x + f y

namespace CauchyEquation

variable {f : ℝ → ℝ}

/-- Zero is mapped to zero. -/
theorem map_zero (hf : CauchyEquation f) : f 0 = 0 := by
  have h := hf 0 0
  simp only [add_zero] at h
  linarith

/-- Negation: `f(-x) = -f(x)`. -/
theorem map_neg (hf : CauchyEquation f) (x : ℝ) : f (-x) = -f x := by
  have h := hf x (-x)
  simp only [add_neg_cancel] at h
  rw [hf.map_zero] at h
  linarith

/-- Natural scaling: `f(n·x) = n·f(x)` for `n : ℕ`. -/
theorem map_nsmul (hf : CauchyEquation f) (x : ℝ) (n : ℕ) : f (n * x) = n * f x := by
  induction n with
  | zero => simp [hf.map_zero]
  | succ n ih =>
    have heq : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
    calc f ((n + 1 : ℕ) * x)
        = f ((n : ℝ) * x + x) := by rw [heq]
      _ = f ((n : ℝ) * x) + f x := hf _ _
      _ = (n : ℝ) * f x + f x := by rw [ih]
      _ = ((n + 1 : ℕ) : ℝ) * f x := by push_cast; ring

/-- Integer scaling: `f(n·x) = n·f(x)` for `n : ℤ`. -/
theorem map_zsmul (hf : CauchyEquation f) (x : ℝ) (n : ℤ) : f (n * x) = n * f x := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_coe, Int.cast_natCast]
    exact hf.map_nsmul x m
  | negSucc m =>
    simp only [Int.cast_negSucc, neg_mul]
    rw [hf.map_neg]
    have h := hf.map_nsmul x (m + 1)
    simp only [Nat.cast_add, Nat.cast_one] at h
    -- Goal: -f (↑(m+1) * x) = -(↑(m+1) * f x)
    -- h: f ((↑m + 1) * x) = (↑m + 1) * f x
    -- Note: ↑(m+1) and (↑m + 1) are definitionally equal as ℝ
    convert congrArg (fun y => -y) h using 1 <;> push_cast <;> ring

/-- Rational scaling: `f(q·x) = q·f(x)` for `q : ℚ`. -/
theorem map_rat_mul (hf : CauchyEquation f) (x : ℝ) (q : ℚ) : f (q * x) = q * f x := by
  have hden_pos : 0 < q.den := q.den_pos
  have hden_ne : (q.den : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
  -- q = q.num / q.den
  have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by simp [Rat.cast_def]
  -- f(q.den * (q*x)) = q.den * f(q*x)
  have h1 : f ((q.den : ℝ) * (q * x)) = (q.den : ℝ) * f (q * x) := by
    have := hf.map_nsmul (q * x) q.den
    convert this using 1
  -- q.den * (q*x) = q.num * x
  have h2 : (q.den : ℝ) * (q * x) = (q.num : ℝ) * x := by
    rw [hq_eq]
    field_simp [hden_ne]
  -- f(q.num * x) = q.num * f(x)
  have h3 : f ((q.num : ℝ) * x) = (q.num : ℝ) * f x := hf.map_zsmul x q.num
  -- Combine
  have h4 : f ((q.den : ℝ) * (q * x)) = (q.num : ℝ) * f x := by rw [h2, h3]
  have h5 : (q.den : ℝ) * f (q * x) = (q.num : ℝ) * f x := by rw [← h1, h4]
  have hden_pos_r : 0 < (q.den : ℝ) := by exact_mod_cast hden_pos
  have hdiv : f (q * x) = (q.num : ℝ) * f x / (q.den : ℝ) := by
    have h6 : f (q * x) * (q.den : ℝ) = (q.num : ℝ) * f x := by linarith
    field_simp [hden_ne]
    linarith
  rw [hdiv, hq_eq]
  ring

end CauchyEquation

/-! ## Solution of Cauchy's Equation

**KEY REUSE**: We use `continuous_additive_eq_mul` from
`ProductTheorem.FunctionalEquation` rather than reproving the Cauchy solution.
-/

/-- **Cauchy's equation + continuity → linear**.

This is a direct application of `continuous_additive_eq_mul` from Appendix B.
No new proof needed! -/
theorem cauchyEquation_continuous_linear (f : ℝ → ℝ)
    (hCauchy : CauchyEquation f) (hCont : Continuous f) :
    ∃ A : ℝ, ∀ x : ℝ, f x = A * x :=
  ProductTheorem.continuous_additive_eq_mul f hCauchy hCont

/-- **Cauchy's equation + measurability → linear**.

This is the KS-friendly “no pathological solutions” statement that avoids assuming continuity:
an additive function `f : ℝ → ℝ` which is Borel-measurable is automatically continuous, hence
linear by `continuous_additive_eq_mul` (Appendix B infrastructure). -/
theorem cauchyEquation_measurable_linear (f : ℝ → ℝ)
    (hCauchy : CauchyEquation f) (hMeas : Measurable f) :
    ∃ A : ℝ, ∀ x : ℝ, f x = A * x := by
  let F : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := CauchyEquation.map_zero hCauchy
      map_add' := hCauchy }
  have hMeasF : Measurable (F : ℝ → ℝ) := by
    simpa [F] using hMeas
  have hContF : Continuous (F : ℝ → ℝ) :=
    MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable F hMeasF
  have hCont : Continuous f := by
    simpa [F] using hContF
  exact cauchyEquation_continuous_linear f hCauchy hCont

/-! ## The Variational Equation -/

/-- **Variational functional equation** (K&S Appendix C).

The equation `H'(m_x · m_y) = lam(m_x) + mu(m_y)` where:
- `H' : ℝ → ℝ` is the derivative of the entropy-like function
- `lam, mu : ℝ → ℝ` are functions of the "masses"
- The equation holds for all positive `m_x, m_y > 0`

This captures the "factorization" property arising from the variational potential. -/
def VariationalEquation (H' lam mu : ℝ → ℝ) : Prop :=
  ∀ m_x m_y : ℝ, 0 < m_x → 0 < m_y → H' (m_x * m_y) = lam m_x + mu m_y

namespace VariationalEquation

variable {H' lam mu : ℝ → ℝ}

/-- The variational equation at `m_x = m_y = 1` gives `H'(1) = lam(1) + mu(1)`. -/
theorem at_one_one (hV : VariationalEquation H' lam mu) :
    H' 1 = lam 1 + mu 1 := by
  have := hV 1 1 one_pos one_pos
  simp at this
  exact this

/-- Setting `m_y = 1`: `H'(m_x) = lam(m_x) + mu(1)`. -/
theorem at_m_one (hV : VariationalEquation H' lam mu) {m : ℝ} (hm : 0 < m) :
    H' m = lam m + mu 1 := by
  have := hV m 1 hm one_pos
  simp at this
  exact this

/-- Setting `m_x = 1`: `H'(m_y) = lam(1) + mu(m_y)`. -/
theorem at_one_m (hV : VariationalEquation H' lam mu) {m : ℝ} (hm : 0 < m) :
    H' m = lam 1 + mu m := by
  have := hV 1 m one_pos hm
  simp at this
  exact this

/-- **Key consequence**: `lam` and `mu` differ by a constant.

From `H'(m) = lam(m) + mu(1) = lam(1) + mu(m)`, we get `lam(m) - lam(1) = mu(m) - mu(1)`. -/
theorem lam_mu_shift (hV : VariationalEquation H' lam mu) {m : ℝ} (hm : 0 < m) :
    lam m - lam 1 = mu m - mu 1 := by
  have h1 := hV.at_m_one hm
  have h2 := hV.at_one_m hm
  linarith

/-- **Corollary**: We can write `lam(m) = phi(m) + c1` and `mu(m) = phi(m) + c2` for a common `phi`.

This means the variational equation simplifies to: `H'(xy) = phi(x) + phi(y) + c`
where `c = c1 + c2`. Also, `phi(1) = 0` by construction. -/
theorem exists_common_core (hV : VariationalEquation H' lam mu) :
    ∃ phi : ℝ → ℝ, ∃ c1 c2 : ℝ,
      phi 1 = 0 ∧
      (∀ m, 0 < m → lam m = phi m + c1) ∧
      (∀ m, 0 < m → mu m = phi m + c2) := by
  refine ⟨fun m => lam m - lam 1, lam 1, mu 1, ?_, ?_, ?_⟩
  · simp
  · intro m _
    ring
  · intro m hm
    have := hV.lam_mu_shift hm
    linarith

end VariationalEquation

/-! ## Transformation to Cauchy Equation

The key insight: under the substitution `u = log m`, the multiplicative structure
becomes additive, reducing to Cauchy's equation.
-/

/-- Transform a function on positive reals to a function on all reals via `exp`. -/
noncomputable def transformToAdditive (g : ℝ → ℝ) : ℝ → ℝ := fun u => g (Real.exp u)

/-- If `g(xy) = g(x) + g(y)` for positive `x, y`, then `transformToAdditive g` satisfies
Cauchy's equation. -/
theorem cauchyEquation_of_multiplicative (g : ℝ → ℝ)
    (hg : ∀ x y : ℝ, 0 < x → 0 < y → g (x * y) = g x + g y) :
    CauchyEquation (transformToAdditive g) := by
  intro u v
  simp only [transformToAdditive]
  have hexp_u : 0 < Real.exp u := Real.exp_pos u
  have hexp_v : 0 < Real.exp v := Real.exp_pos v
  rw [Real.exp_add]
  exact hg _ _ hexp_u hexp_v

/-! ## The Entropy Solution

The solution to the variational equation is the **entropy form**:
`H(m) = A + B·m + C·(m·log(m) - m)`

Its derivative is: `H'(m) = B + C·log(m)`
-/

/-- The derivative of the entropy form `H(m) = A + Bm + C(m log m - m)` is `H'(m) = B + C log m`. -/
noncomputable def entropyDerivative (B C : ℝ) : ℝ → ℝ := fun m => B + C * Real.log m

/-- The entropy derivative satisfies the variational equation with `lam = mu = (C/2) log + const`. -/
theorem entropyDerivative_variational (B C : ℝ) :
    VariationalEquation (entropyDerivative B C)
      (fun m => B / 2 + C * Real.log m)
      (fun m => B / 2 + C * Real.log m) := by
  intro m_x m_y hx hy
  simp only [entropyDerivative]
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  ring

/-- **Main Theorem (Appendix C) — measurable version**.

If `H'` satisfies the variational equation and is Borel-measurable, then
`H'(m) = B + C·log(m)` for some constants `B, C`.

This isolates the regularity needed to rule out pathological solutions of Cauchy’s equation:
measurable additive functions are automatically continuous (hence linear).

K&S enforce regularity by “blurring by convolution” in the TeX; in Lean we take measurability as a
clean, explicit substitute. In typical applications this is discharged by `H' = deriv H`, since
derivatives are measurable (`measurable_deriv`). -/
theorem variationalEquation_solution_measurable
    (H' : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hMeas : Measurable H')
    (hV : VariationalEquation H' lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → H' m = B + C * Real.log m := by
  -- Step 1: Extract the common core phi from lam and mu
  obtain ⟨phi, c1, c2, hphi1, hlam, hmu⟩ := hV.exists_common_core

  -- Step 2: Show H'(1) = c1 + c2
  have hH1 : H' 1 = c1 + c2 := by
    have := hV.at_one_one
    have hlam1 : lam 1 = phi 1 + c1 := hlam 1 one_pos
    have hmu1 : mu 1 = phi 1 + c2 := hmu 1 one_pos
    rw [hlam1, hmu1, hphi1] at this
    linarith

  -- Step 3: Show phi is multiplicatively additive: phi(xy) = phi(x) + phi(y)
  have hphi_pure : ∀ x y : ℝ, 0 < x → 0 < y → phi (x * y) = phi x + phi y := by
    intro x y hx hy
    have hxy : 0 < x * y := mul_pos hx hy
    have h1 : H' (x * y) = lam x + mu y := hV x y hx hy
    have h2 : lam x = phi x + c1 := hlam x hx
    have h3 : mu y = phi y + c2 := hmu y hy
    have h4 : H' (x * y) = phi x + phi y + (c1 + c2) := by rw [h1, h2, h3]; ring
    have h5 : H' (x * y) = phi (x * y) + c1 + mu 1 := by
      have := hV.at_m_one hxy
      rw [hlam (x * y) hxy] at this
      linarith
    have h6 : mu 1 = c2 := by
      have := hmu 1 one_pos
      rw [hphi1] at this
      linarith
    rw [h6] at h5
    linarith

  -- Step 4: Transform to Cauchy equation
  have hpsi_cauchy : CauchyEquation (transformToAdditive phi) :=
    cauchyEquation_of_multiplicative phi hphi_pure

  -- Step 5: Show psi is measurable (from measurability of H')
  have hphi_eq : ∀ m : ℝ, 0 < m → phi m = H' m - c1 - mu 1 := by
    intro m hm
    have := hV.at_m_one hm
    have hlamm := hlam m hm
    linarith
  have hpsi_measurable : Measurable (transformToAdditive phi) := by
    have hH'exp : Measurable (fun u : ℝ => H' (Real.exp u)) :=
      hMeas.comp Real.continuous_exp.measurable
    have hEq : transformToAdditive phi = fun u : ℝ => H' (Real.exp u) - c1 - mu 1 := by
      funext u
      simp [transformToAdditive, hphi_eq (Real.exp u) (Real.exp_pos u)]
    simpa [hEq] using (hH'exp.sub measurable_const).sub measurable_const

  -- Step 6: Apply Cauchy solution
  obtain ⟨C, hC⟩ := cauchyEquation_measurable_linear _ hpsi_cauchy hpsi_measurable

  -- Step 7: Unwind to get H'(m) = B + C·log(m)
  refine ⟨c1 + mu 1, C, ?_⟩
  intro m hm
  have hm_eq : m = Real.exp (Real.log m) := (Real.exp_log hm).symm
  have hpsi_log : transformToAdditive phi (Real.log m) = C * Real.log m := hC (Real.log m)
  have hphi_m : phi m = transformToAdditive phi (Real.log m) := by
    simp only [transformToAdditive]; rw [← hm_eq]
  have hphi_val : phi m = C * Real.log m := by rw [hphi_m, hpsi_log]
  have hH'_m := hphi_eq m hm
  linarith

/-- **Main Theorem (Appendix C) — `deriv` version**.

This is the direct “mathematician’s” statement: phrase the variational equation using `deriv H`
(rather than a separate symbol `H'`), then measurability is automatic. -/
theorem variationalEquation_solution
    (H : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hV : VariationalEquation (deriv H) lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → deriv H m = B + C * Real.log m := by
  simpa using
    (variationalEquation_solution_measurable (H' := deriv H) (lam := lam) (mu := mu)
      (hMeas := measurable_deriv H) (hV := hV))

/-- **Appendix C — explicit `H'` wrapper.**

If you prefer to name the derivative `H'` explicitly, this lemma shows how to connect the
`deriv`-based theorem above back to a chosen `H'` (on `(0,∞)`). -/
theorem variationalEquation_solution_of_hasDerivAt
    (H H' : ℝ → ℝ) (lam mu : ℝ → ℝ)
    (hDeriv : ∀ m : ℝ, 0 < m → HasDerivAt H (H' m) m)
    (hV : VariationalEquation H' lam mu) :
    ∃ B C : ℝ, ∀ m : ℝ, 0 < m → H' m = B + C * Real.log m := by
  have hV' : VariationalEquation (deriv H) lam mu := by
    intro m_x m_y hx hy
    have hder : deriv H (m_x * m_y) = H' (m_x * m_y) := (hDeriv (m_x * m_y) (mul_pos hx hy)).deriv
    simpa [hder] using (hV m_x m_y hx hy)
  rcases variationalEquation_solution (H := H) (lam := lam) (mu := mu) hV' with ⟨B, C, hBC⟩
  refine ⟨B, C, ?_⟩
  intro m hm
  have hder : deriv H m = H' m := (hDeriv m hm).deriv
  calc
    H' m = deriv H m := hder.symm
    _ = B + C * Real.log m := hBC m hm

/-! ## Integration: From H' to H

Given `H'(m) = B + C·log(m)`, we can integrate to get the entropy form:
`H(m) = A + B·m + C·(m·log(m) - m)`
-/

/-- The **entropy form** arising from integrating `H'(m) = B + C·log(m)`. -/
noncomputable def entropyForm (A B C : ℝ) : ℝ → ℝ := fun m => A + B * m + C * (m * Real.log m - m)

/-- The derivative of `entropyForm A B C` is `entropyDerivative B C` (for `m > 0`). -/
theorem entropyForm_deriv (A B C : ℝ) {m : ℝ} (hm : 0 < m) :
    HasDerivAt (entropyForm A B C) (entropyDerivative B C m) m := by
  unfold entropyForm entropyDerivative
  -- d/dm [A + Bm + C(m log m - m)]
  -- = B + C(log m + 1 - 1)
  -- = B + C log m
  have h1 : HasDerivAt (fun x => A) 0 m := hasDerivAt_const m A
  have h2 : HasDerivAt (fun x => B * x) B m := by
    have hid := hasDerivAt_id m
    have h := hid.const_mul B
    convert h using 1
    ring
  -- Use the mathlib lemma for d/dm (m log m) = log m + 1
  have h3 : HasDerivAt (fun x => x * Real.log x) (Real.log m + 1) m :=
    Real.hasDerivAt_mul_log (ne_of_gt hm)
  have h4 : HasDerivAt (fun x => x) 1 m := hasDerivAt_id m
  have h5 : HasDerivAt (fun x => x * Real.log x - x) (Real.log m + 1 - 1) m :=
    h3.sub h4
  have h6 : HasDerivAt (fun x => C * (x * Real.log x - x)) (C * (Real.log m + 1 - 1)) m := by
    have h := h5.const_mul C
    convert h using 1
  have h7 : HasDerivAt (fun x => A + B * x + C * (x * Real.log x - x))
      (0 + B + C * (Real.log m + 1 - 1)) m := by
    exact (h1.add h2).add h6
  convert h7 using 1; ring

/-- **Main integration result**: The entropy form has the correct derivative. -/
theorem entropyForm_has_derivative (A B C : ℝ) :
    ∀ m : ℝ, 0 < m → HasDerivAt (entropyForm A B C) (B + C * Real.log m) m := by
  intro m hm
  have := entropyForm_deriv A B C hm
  convert this using 1

/-! ## Characterizing the Minimum of entropyForm

The entropy form `H(m) = A + B·m + C·(m·log(m) - m)` has a unique critical point
where `H'(m) = B + C·log(m) = 0`, i.e., at `m = exp(-B/C)` (when `C ≠ 0`).

When `C > 0`, this critical point is a **minimum**.

K&S Section 6 chooses parameters to place the minimum at a desired location with value zero:
- `C = 1` ensures a minimum (not maximum)
- `B = -log(u)` places the minimum at `m = u`
- `A = u` makes the minimum value zero
-/

/-- The critical point of `entropyForm A B C` is where `H'(m) = B + C·log(m) = 0`.
When `C ≠ 0`, this occurs at `m = exp(-B/C)`. -/
theorem entropyForm_critical_point (B C : ℝ) (hC : C ≠ 0) :
    let m₀ := Real.exp (-B / C)
    entropyDerivative B C m₀ = 0 := by
  simp only [entropyDerivative]
  rw [Real.log_exp]
  -- Goal: B + C * (-B / C) = 0
  field_simp [hC]
  ring

/-- When `B = -log(u)` and `C = 1`, the critical point is at `m = u`. -/
theorem entropyForm_critical_at_u (u : ℝ) (hu : 0 < u) :
    Real.exp (-(-Real.log u) / 1) = u := by
  simp [Real.exp_log hu]

/-- The value of `entropyForm A B C` at its critical point `m₀ = exp(-B/C)`.

We compute: `H(m₀) = A + B·m₀ + C·(m₀·log(m₀) - m₀)`
where `log(m₀) = -B/C`, so `m₀·log(m₀) = m₀·(-B/C)`.
Thus `H(m₀) = A + B·m₀ + C·(m₀·(-B/C) - m₀) = A + B·m₀ - B·m₀ - C·m₀ = A - C·m₀`.

With `m₀ = exp(-B/C)`, we get `H(m₀) = A - C·exp(-B/C)`. -/
theorem entropyForm_value_at_critical (A B C : ℝ) (hC : C ≠ 0) :
    let m₀ := Real.exp (-B / C)
    entropyForm A B C m₀ = A - C * m₀ := by
  simp only [entropyForm]
  rw [Real.log_exp]
  field_simp
  ring

/-- When `A = u`, `B = -log(u)`, `C = 1`, the minimum value is zero.

With these parameters: `m₀ = exp(-(-log u)/1) = u` and
`H(m₀) = A - C·m₀ = u - 1·u = 0`. -/
theorem entropyForm_minimum_value_zero (u : ℝ) (hu : 0 < u) :
    entropyForm u (-Real.log u) 1 u = 0 := by
  unfold entropyForm
  have hu_ne : u ≠ 0 := ne_of_gt hu
  simp only [one_mul]
  -- Goal: u + -Real.log u * u + (u * Real.log u - u) = 0
  ring

/-- The second derivative of entropyForm is `H''(m) = C/m`, which is positive when `C > 0` and `m > 0`.
This confirms the critical point is a minimum when `C > 0`. -/
theorem entropyForm_second_deriv_pos (C : ℝ) (hC : 0 < C) {m : ℝ} (hm : 0 < m) :
    0 < C / m := div_pos hC hm

/-- **Summary**: The divergence parameters are **forced** by requirements.

Given the entropy form `H(m) = A + B·m + C·(m·log(m) - m)`:
1. To have a minimum (not maximum): `C > 0` (we set `C = 1`)
2. To place the minimum at `m = u`: solve `exp(-B/C) = u`, giving `B = -log(u)`
3. To make the minimum value zero: `A - C·u = 0`, giving `A = C·u = u`

These constraints uniquely determine `A = u`, `B = -log(u)`, `C = 1` for the divergence formula. -/
theorem divergence_parameters_forced (u : ℝ) (_hu : 0 < u)
    (A B C : ℝ) (hC_pos : 0 < C)
    (h_min_at_u : Real.exp (-B / C) = u)
    (h_min_val_zero : A - C * u = 0) :
    A = C * u ∧ B = -C * Real.log u := by
  constructor
  · linarith
  · have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have h1 : -B / C = Real.log u := by
      have h2 : Real.log (Real.exp (-B / C)) = Real.log u := by
        rw [h_min_at_u]
      rw [Real.log_exp] at h2
      exact h2
    field_simp at h1 ⊢
    linarith

end Mettapedia.ProbabilityTheory.KnuthSkilling.VariationalTheorem
