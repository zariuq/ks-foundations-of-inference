import KnuthSkilling.Variational.Main
import KnuthSkilling.ShoreJohnson.KL
import KnuthSkilling.ShoreJohnson.KLWitness

/-!
# Variational rigidity and admissible inference

The measurable positive-domain Cauchy equation is a specialization of Appendix C's
separated equation. Its affine constant vanishes at one. This analytic gate does
not derive the separable profile from inference-operator laws.
The separate KL operator witness accepts the positive prior with no information
and refuses the empty constraint set; total solvability is not assumed.
-/

namespace KnuthSkilling.Bridges
open KnuthSkilling.Variational KnuthSkilling.ShoreJohnson.KL

theorem mulCauchyOnPos_eq_const_mul_log_of_variationalEquation_solution_measurable
    (g : ℝ → ℝ) (hg : MulCauchyOnPos g) (hMeas : Measurable g) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → g x = C * Real.log x := by
  obtain ⟨B, C, hBC⟩ := variationalEquation_solution_measurable
    (H' := g) (lam := g) (mu := g) (hMeas := hMeas) (hV := hg)
  have hg1 : g 1 = 0 := by have hh := hg 1 1 one_pos one_pos; simp only [one_mul] at hh; linarith
  have hB : B = 0 := by simpa [hg1] using (hBC 1 one_pos).symm
  exact ⟨C, fun x hx => by simpa [hB] using hBC x hx⟩

theorem mulCauchyOnPos_eq_const_mul_log
    (g : ℝ → ℝ) (hg : MulCauchyOnPos g) (hMeas : Measurable g) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → g x = C * Real.log x :=
  mulCauchyOnPos_eq_const_mul_log_of_variationalEquation_solution_measurable g hg hMeas

open KnuthSkilling.ShoreJohnson KnuthSkilling.ShoreJohnson.Inference

/-- An inhabited operator profile distinguishes no information from impossible information. -/
theorem kl_inference_domain_control {n : ℕ} (p : Information.InformationEntropy.ProbDist n)
    (hp : ∀ i, 0 < p.p i) :
    KLWitness.klInference.Infer p Set.univ p ∧
      ∀ q, ¬KLWitness.klInference.Infer p ∅ q :=
  ⟨KLWitness.klInference_priorPreservation p hp,
    fun q => not_infer_empty KLWitness.klInference_axioms p q⟩

end KnuthSkilling.Bridges
