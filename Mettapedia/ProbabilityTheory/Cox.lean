import Mettapedia.ProbabilityTheory.Cox.Basic
import Mettapedia.ProbabilityTheory.Cox.Derivation

/-!
# Cox's Theorem: Probability from Plausibility

This module formalizes Cox's theorem (1946, 1961), which derives the laws of
probability from axioms about plausible reasoning.

## The Cox Approach

Cox shows that if plausibility satisfies:
1. **Real-valued**: p(A|B) ∈ [0,1]
2. **Product rule**: p(A∧B|C) = F(p(A|C), p(B|A∧C)) for some F
3. **Negation rule**: p(¬A|B) = G(p(A|B)) for some G
4. **Consistency**: Equivalent propositions have equal plausibility

Then functional equation analysis forces:
- F(x,y) = x·y (product rule)
- G(x) = 1-x (negation rule)

**Key insight**: Commutativity F(x,y) = F(y,x) is DERIVED, not assumed!

## Files

- `Basic.lean`: Core axiom structures (PlausibilityFunction, ConjunctionRule, etc.)
- `Derivation.lean`: Proofs that standard rules satisfy axioms, connection to Kolmogorov

## Connection to Imprecise Probability

Cox's associativity axiom is what forces additivity. Without it:
- Sub/super-additivity gives imprecise probability (see `ImpreciseProbability/`)
- The counterexample in `Seminorm.lean` shows coherent but non-regular previsions

## Connection to Knuth-Skilling

K&S claim to derive probability from weaker axioms (no continuity, no inverses).
Their `CoxConsistency` structure in `KnuthSkilling/ProbabilityDerivation.lean`
captures the algebraic essence and proves `cox_implies_kolmogorov`.

The relationship is:
- Cox: Functional equations on [0,1] → forces F = multiplication
- K&S: Lattice algebra on valuations → forces addition via regraduation
- Both derive commutativity (don't assume it)

## Status

- ✅ Basic axiom structures
- ✅ Standard rules satisfy axioms
- ✅ Commutativity at boundary (partial)
- 🔶 Full functional equation derivation (needs Aczél theory)
- ✅ Connection to Kolmogorov (via K&S path)

## References

- Cox, R.T. "The Algebra of Probable Inference" (1961)
- Jaynes, E.T. "Probability Theory: The Logic of Science" (2003)
- Dupré & Tipler "The Cox Theorem" (2006)
- Knuth & Skilling "Foundations of Inference" (2012)
-/
