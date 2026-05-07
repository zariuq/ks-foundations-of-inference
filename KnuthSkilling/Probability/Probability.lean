/-
# KnuthSkilling Probability - Interpretation Layer

This module provides the **probability interpretation** of the abstract
algebraic structures. It connects the Core representation theorems to
the familiar probability calculus and information measures.

## What's Exported

### Probability Calculus
- **ProbabilityDerivation**: Full derivation from Appendix A+B
- **ProbabilityCalculus**: Canonical interface (sum rule, product rule, Bayes)
- **ConditionalProbability**: K&S Section 7 (chaining axiom)
- **Independence**: Independence axioms and consequences

### Information Theory
- **Divergence**: K&S Section 6 (KL divergence foundations)
- **InformationEntropy**: K&S Section 8 (Shannon entropy)
- **DivergenceMathlib**: Bridge to `Mathlib.InformationTheory.klDiv`
- **InformationEntropyMathlib**: Bridge to mathlib entropy

## Layer Structure

```
Core (abstract algebra)
    ↓
Probability (interpretation)
    ↓
Applications (specific uses)
```

This module depends on Core but is NOT imported by Core,
ensuring clean layering.

## Usage

```lean
import KnuthSkilling.Probability.Probability

-- Access probability calculus
#check ProbabilityCalculus.sumRule
#check ProbabilityCalculus.bayesTheorem
```
-/

-- Probability calculus
import KnuthSkilling.Probability.ProbabilityDerivation
import KnuthSkilling.Probability.ProbabilityCalculus
import KnuthSkilling.Probability.ConditionalProbability
import KnuthSkilling.Probability.Independence

-- Information theory
import KnuthSkilling.Information.Divergence
import KnuthSkilling.Information.DivergenceMathlib
import KnuthSkilling.Information.InformationEntropy
import KnuthSkilling.Information.InformationEntropyMathlib
