import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.NonModularDistributive
import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.VariationalNonsmooth
import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.CauchyPathology

/-!
# Knuth–Skilling: Counterexamples

This module re-exports small countermodels/counterexamples used to clarify which hypotheses are
actually needed in the Knuth–Skilling development.

Notably:
- `...Counterexamples.VariationalNonsmooth` shows that “variational optimum ⇒ differentiable” is
  false in general.
- `...Counterexamples.CauchyPathology` builds a non-`A*x` additive function (Hamel-basis style),
  demonstrating why Appendix C needs an explicit regularity condition (measurable/continuous/etc.).
- `...Counterexamples.NonModularDistributive` shows disjoint additivity does not imply modularity.
-/
