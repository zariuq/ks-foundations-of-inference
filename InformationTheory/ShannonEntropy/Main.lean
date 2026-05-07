import InformationTheory.ShannonEntropy.Faddeev
import InformationTheory.ShannonEntropy.Shannon1948
import InformationTheory.ShannonEntropy.Properties
import InformationTheory.ShannonEntropy.ShannonKhinchin
import InformationTheory.ShannonEntropy.Interface
import InformationTheory.ShannonEntropy.Equivalence
import InformationTheory.ShannonEntropy.MeasureTheoreticBridge

/-!
# Shannon Entropy (Entry Point)

This module is a small, reviewer-friendly entry point for the Shannon-entropy
axiomatizations and their relationships.

This entry point is intended to be the "shipping" interface for the finite Shannon
entropy formalization, including:

- Axiomatizations: Faddeev (1956), Shannon (1948), Shannon-Khinchin (1957)
- Equivalence glue between axiom systems
- A unified interface connecting:
  - `ProbVec n` (mathlib `stdSimplex`-based) and
  - `ProbDist n` (K&S / Foundations finite distributions)
- KL divergence and a measure-theoretic bridge for discrete measures
-/
