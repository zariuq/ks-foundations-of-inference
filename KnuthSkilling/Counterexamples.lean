import KnuthSkilling.Counterexamples.NonModularDistributive
import KnuthSkilling.Counterexamples.VariationalNonsmooth
import KnuthSkilling.Counterexamples.CauchyPathology
import KnuthSkilling.Counterexamples.RegradeCounterexample
import KnuthSkilling.Counterexamples.SigmaAdditivityNecessity
import KnuthSkilling.Additive.Counterexamples.BenV2Theorem1
import KnuthSkilling.Additive.Counterexamples.KSSeparationNotDerivable
import KnuthSkilling.Additive.Counterexamples.NegativeWithoutIdentity
import KnuthSkilling.Additive.Counterexamples.ProductFailsSeparation
import KnuthSkilling.Additive.Counterexamples.SemidirectNoSeparation

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
- `...Additive.Counterexamples.NegativeWithoutIdentity` shows why the bounded-below/identity
  hypothesis matters for the additive representation theorem.
- `...Additive.Counterexamples.ProductFailsSeparation` and
  `...Additive.Counterexamples.SemidirectNoSeparation` witness failures of separation-style
  hypotheses in simple algebraic models.
-/
