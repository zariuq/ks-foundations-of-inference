import KnuthSkilling.Multiplicative.FunctionalEquation
import KnuthSkilling.Multiplicative.DirectProduct
import KnuthSkilling.Multiplicative.ScaledMultRep
import KnuthSkilling.Multiplicative.Main
import KnuthSkilling.Multiplicative.Proofs.Direct.DirectProof
import KnuthSkilling.Multiplicative.StrictMonoSolution

/-!
# Product-equation and distributive-tensor routes

The functional route consumes a global additive order isomorphism and
distributivity. The direct route consumes associativity, distributivity and an
injective right scaling map. Both produce `ScaledMultRep`, whose normalization
is unique for a fixed tensor. Neither route is Cox's interval generator theorem.

`DistributiveTensor` is the shared direct proof home; both historical direct
entrypoints import it. The optional Fibonacci proof is checked separately and
is not imported here.
-/
