import KnuthSkilling.ShoreJohnson.Inference
import KnuthSkilling.ShoreJohnson.Constraints
import KnuthSkilling.ShoreJohnson.Objective
import KnuthSkilling.ShoreJohnson.TheoremI
import KnuthSkilling.ShoreJohnson.SystemIndependence
import KnuthSkilling.ShoreJohnson.Theorem
import KnuthSkilling.ShoreJohnson.OperatorAtomBridge
import KnuthSkilling.ShoreJohnson.KL
import KnuthSkilling.ShoreJohnson.Bridge
import KnuthSkilling.ShoreJohnson.KLDerivation
import KnuthSkilling.ShoreJohnson.GradientSeparability
import KnuthSkilling.ShoreJohnson.SJ3Locality
import KnuthSkilling.ShoreJohnson.KLWitness
import KnuthSkilling.ShoreJohnson.RatioInvarianceCounterexample
import KnuthSkilling.ShoreJohnson.Integration

/-!
# Shore-Johnson (1980) entrypoint

This entrypoint keeps two threads visible:

1. **SJ axioms and inference formalism** (SJ1--SJ4) leading to sum-form objectives and
   system independence. Core modules:
   `Inference`, `Constraints`, `Objective`, `TheoremI`, `SystemIndependence`,
   `OperatorAtomBridge`, `Theorem`, `KL`.

2. **Path C overlap with Appendix C**. The Shore-Johnson path derives the same
   multiplicative Cauchy/log equation used in the Appendix C variational route.
   See `ShoreJohnson.KLDerivation` and compare with
   `KnuthSkilling/Variational/Main.lean`.

Analytic regularity for SJ3 -> locality is packaged in `GradientSeparability` and
`SJ3Locality`. We also include **positive** and **negative** examples of the
ratio-invariance axiom:
- `KLWitness`: KL atom satisfies `DerivRatioInvariant`.
- `RatioInvarianceCounterexample`: quadratic loss fails it.
-/
