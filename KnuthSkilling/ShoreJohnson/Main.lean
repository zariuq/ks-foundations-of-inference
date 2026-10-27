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
import KnuthSkilling.ShoreJohnson.MaximumEntropy

/-!
# Finite inference laws and conditional Shore–Johnson analysis

* `Inference`, `Constraints`, `Objective`: partial inference, affine observations,
  explicit admissibility and minimizer observations.
* `GradientSeparability`, `SJ3Locality`, `TheoremI`: analytic transport and a
  variational comparison under stated ratio/cocycle, derivative and convexity laws.
* `KLWitness`: a concrete positive-reference KL model, existence, and the
  conditional positive-scale conclusion with prior preservation.
* `MaximumEntropy`: a four-law countermodel showing why prior preservation matters.
* `SystemIndependence`, `Theorem`, `KL`, `Bridge`: functional-equation rigidity
  under atom-level hypotheses, and its connection to finite divergence.

The operator-to-analytic implications remain separate theorem targets; this
entrypoint does not certify a complete five-axiom derivation of KL.
-/
