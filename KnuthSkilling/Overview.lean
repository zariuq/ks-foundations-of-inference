/-
# Foundations of inference: constructions and their boundaries

## Ordered combination

`Api` presents the public theorem statements. Additive representation means
an order embedding preserving the supplied operation, not a surjection onto ℝ.
Hölder uses absence of anomalous pairs; cuts and the maintained Grid construction
use their stated separation profiles. Concrete real, nonnegative-real and
identity-free positive-real models check that these profiles can be inhabited.
Positive-anchor calibration compares the actual maps from different routes.
`zero_anchor_globalization_impossible` rules out zero at a positive anchor.
Unit calibration preserves the supplied map up to a positive scale and adds no
representation-existence assumption.

## Products and probability

Appendix B has a shared tensor proof with explicit regularity and distributivity
premises. Its normalization is a faithful multiplicative observation and preserves
authored folds. An additive embedding alone supplies no multiplicative law.
The inverse-based route additionally requires a real order isomorphism.

`ProbabilityCalculus` is the common sum/product/Bayes interface. The scalar Cox
profile and lattice bivaluations have different supplied assumptions; their
calibration premises are not silently deduced from the operator laws.
Normalizing event weights requires positive total mass. Finite coordinate and
Mathlib-measure bridges prove preservation of the supplied probability answers.
Countable additivity needs separately supplied event and continuity conditions.

## Information and variational inference

Extended KL retains singular source mass as infinity. Real KL interpretations
require the stated support and summability premises.
Appendix C's logarithmic rigidity requires its regularity gate; additive Hamel
pathologies and nonsmooth minima separate that gate from algebra and optimality.

Shore--Johnson is opt-in. Inference is specified on admissible constraints;
existence and at-most-one uniqueness are separate. Concrete KL inference satisfies
the guarded operator laws. The separable analytic profile is supplied separately:
it has not been derived from those operator laws. Prior preservation has its own
role, distinguished by the maximum-entropy control.

## Examples and countermodels

Finite weighted events provide inhabited probability models. The finite decision
example proves extraction, observation-relative precision and attained credal
minima. Expected utility and maximin are additional decision rules.
Incomparability does not imply failure of Boolean complementation: the four-element
diamond is Boolean. Disjoint additivity without relative complements need not imply
modularity; numerical risk valuations must not be confused with event probabilities.

The default entry point imports the core and interpretation layers below.
Shore--Johnson and the counterexample aggregate remain explicit imports.
-/

import KnuthSkilling.Api
import KnuthSkilling.FoundationsOfInference
import KnuthSkilling.Bridges.GoertzelGroupFix
import KnuthSkilling.Probability.Independence
import KnuthSkilling.Probability.ConditionalProbability
import KnuthSkilling.Core.SymmetricalFoundation
