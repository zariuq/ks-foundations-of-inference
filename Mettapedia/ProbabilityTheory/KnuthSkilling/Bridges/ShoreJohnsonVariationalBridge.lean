import Mettapedia.ProbabilityTheory.KnuthSkilling.Variational.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KL

/-!
# Shore--Johnson <-> Appendix C bridge: the Cauchy/log gate

Both the Knuth--Skilling Appendix C variational route and the Shore--Johnson (1980) route
ultimately rely on the same analytic rigidity fact:

> A (multiplicative) Cauchy functional equation has only logarithmic solutions once a regularity
> gate (here: Borel measurability) excludes Hamel-basis pathologies.

In code this shared "Gate R" appears in two guises:

* **K&S Appendix C** (`Variational/Main.lean`): solve the separated equation
  `H'(xy) = lam x + mu y` (under measurability of `H'`), producing
  `H'(m) = B + C * log m`.
* **Shore--Johnson** (`ShoreJohnson/KL.lean`): solve the special case
  `g(xy) = g x + g y`, producing `g(x) = C * log x`.

This file makes the connection formal: Shore--Johnson's log rigidity is a direct corollary of
the Appendix C lemma, by taking `lam = mu = g` and observing the constant term vanishes.

This file is intentionally **opt-in**: it imports both developments, but neither development
imports this bridge.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges

open Mettapedia.ProbabilityTheory.KnuthSkilling.Variational
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KL

theorem mulCauchyOnPos_eq_const_mul_log_of_variationalEquation_solution_measurable
    (g : ℝ → ℝ) (hg : MulCauchyOnPos g) (hMeas : Measurable g) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → g x = C * Real.log x := by
  -- Interpret multiplicative Cauchy as the variational equation with `lam = mu = g`.
  have hV : VariationalEquation g g g := by
    intro x y hx hy
    simpa using hg x y hx hy

  rcases
      variationalEquation_solution_measurable (H' := g) (lam := g) (mu := g)
        (hMeas := hMeas) (hV := hV) with
    ⟨B, C, hBC⟩

  -- Multiplicative Cauchy forces `g 1 = 0`, hence the affine constant is zero.
  have hg1 : g 1 = 0 := by
    have h : g 1 = g 1 + g 1 := by
      simpa using (hg 1 1 one_pos one_pos)
    have h' : g 1 + 0 = g 1 + g 1 := by
      simpa [add_zero] using h
    have h'' : (0 : ℝ) = g 1 := add_left_cancel h'
    simpa using h''.symm

  have hB : B = 0 := by
    have h1 := hBC 1 one_pos
    -- `log 1 = 0`, so `h1` reduces to `g 1 = B`.
    have : (0 : ℝ) = B := by simpa [hg1] using h1
    simpa using this.symm

  refine ⟨C, ?_⟩
  intro x hx
  have hx' := hBC x hx
  simpa [hB] using hx'

/-! ## Convenience: the bridge lemma is the same statement as the SJ lemma. -/

theorem mulCauchyOnPos_eq_const_mul_log
    (g : ℝ → ℝ) (hg : MulCauchyOnPos g) (hMeas : Measurable g) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → g x = C * Real.log x :=
  mulCauchyOnPos_eq_const_mul_log_of_variationalEquation_solution_measurable g hg hMeas

end Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges
