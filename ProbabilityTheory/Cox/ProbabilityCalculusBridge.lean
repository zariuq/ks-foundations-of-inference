import ProbabilityTheory.Cox.ProductRuleDerivation
import KnuthSkilling.Probability.ProbabilityCalculus

/-!
# Product and complement conclusions on their declared domains

The two connectors consume separate axiom packages. They neither identify the
two regraduations nor construct an event-level probability model.
-/

namespace ProbabilityTheory.Cox

open Set

/-- Cox’s product rule already gives the multiplicative regrade:
`p(F x y) = p x * p y` for `x,y ∈ (0,1]`.

This is the same multiplicative form used by the K&S probability calculus
after regraduation. -/
theorem cox_productRule_regrade (C : CoxFullAxioms) :
    ∃ p : ℝ → ℝ, StrictMonoOn p (Ioc (0 : ℝ) 1) ∧ ContinuousOn p (Ioc (0 : ℝ) 1) ∧
      (∀ x y, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → p (C.F x y) = p x * p y) ∧ p 1 = 1 :=
  cox_productRule C

/-- Cox’s negation rule implies **standard complement after regrading** by `x ↦ x^r`:

`(G x)^r = 1 - x^r` on `(0,1)` for some `r > 0`. -/
theorem cox_negationRule_complement (N : CoxNegationAxioms) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Ioo (0 : ℝ) 1, (N.G x) ^ r = 1 - x ^ r := by
  obtain ⟨r, hr, h⟩ := CoxNegationAxioms.negation_power_family N
  refine ⟨r, hr, ?_⟩
  intro x hx
  have h1 := h x hx
  linarith

end ProbabilityTheory.Cox
