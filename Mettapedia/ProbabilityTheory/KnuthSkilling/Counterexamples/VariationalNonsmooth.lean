/-
# Counterexamples for Appendix C Regularity Claims

Knuth & Skilling (Appendix C) motivate replacing a variational inequality by a
first-order differential condition.  In general optimization, **existence of an
(optimal) minimum does not force differentiability**.

This file records small, Lean-checkable counterexamples that clarify the needed
regularity assumptions.

We include both:
- a **positive** example: a smooth function with a global minimum (`x ↦ x^2`);
- a **negative** example: a nonsmooth function with a global minimum (`x ↦ |x|`).
-/

import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples

open Set

/-! ## Positive example: smooth function with a global minimum -/

theorem sq_isMinOn_univ_zero : IsMinOn (fun x : ℝ => x ^ 2) (Set.univ) (0 : ℝ) := by
  -- `0^2 ≤ x^2` because `x^2 ≥ 0`.
  refine (isMinOn_univ_iff (f := fun x : ℝ => x ^ 2) (a := (0 : ℝ))).2 ?_
  intro x
  simpa using (sq_nonneg x)

theorem sq_differentiableAt_zero : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) (0 : ℝ) := by
  exact differentiableAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := (0 : ℝ))

/-! ## Negative example: nonsmooth function with a global minimum -/

theorem abs_isMinOn_univ_zero : IsMinOn (abs : ℝ → ℝ) (Set.univ) (0 : ℝ) := by
  refine (isMinOn_univ_iff (f := (abs : ℝ → ℝ)) (a := (0 : ℝ))).2 ?_
  intro x
  simp

theorem abs_not_differentiableAt_zero : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) (0 : ℝ) :=
  not_differentiableAt_abs_zero

/-- A compact “KS-relevant” statement: there exist global minimizers that are not differentiable. -/
theorem exists_isMinOn_not_differentiableAt :
    ∃ (H : ℝ → ℝ) (x₀ : ℝ), IsMinOn H Set.univ x₀ ∧ ¬ DifferentiableAt ℝ H x₀ := by
  refine ⟨abs, 0, abs_isMinOn_univ_zero, abs_not_differentiableAt_zero⟩

/-! ## (Optional) K&S-shaped variant on `(0, ∞)`

The function `m ↦ |log m|` has a global minimum at `m = 1` on the positive reals.
This aligns closely with the “log-coordinates” used in Appendix C.

We only record the minimizer fact here; non-differentiability at `m = 1` can be
proved but is not needed for our main Appendix C derivation (which works via
measurability of `H'`).
-/

theorem abs_log_isMinOn_pos_one :
    IsMinOn (fun m : ℝ => |Real.log m|) (Ioi (0 : ℝ)) (1 : ℝ) := by
  intro m hm
  -- `|log 1| = 0 ≤ |log m|`.
  simp [Real.log_one]

end Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples
