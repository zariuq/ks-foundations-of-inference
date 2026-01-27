import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Finite Probability as a Special Case of K\&S Section 5.2

This short file records the structural observation behind K\&S Section 5.2:
finite probability on sets is an instance of the inclusion--exclusion identity on a
generalized Boolean algebra (GBA).

Concretely, for any type `α`, the lattice `Set α` is a GBA: set difference `s \\ t` is a relative
complement of `t` inside `s`. Therefore, the K\&S inclusion--exclusion identity applies directly
to finitely additive (disjoint-additive) set functions.

References:
- Knuth \& Skilling, *Foundations of Inference* (2012), Section 5.2.
- This project: `Additive/Proofs/GridInduction/InclusionExclusion.lean`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

open Classical

/-! ## Set α is a Generalized Boolean Algebra

Mathlib provides `GeneralizedBooleanAlgebra (Set α)`: set difference `s \\ t` is the relative
complement of `t` inside `s`.  This is the structural input for the inclusion--exclusion identity
in K\&S Section 5.2. -/

example {α : Type*} : GeneralizedBooleanAlgebra (Set α) := inferInstance

/-! ## Classical Inclusion-Exclusion is a Special Case

For any finite type `α` and any measure `m : Set α → ℝ` that is:
1. Monotone
2. Disjoint-additive: m(A ∪ B) = m(A) + m(B) when A ∩ B = ∅

The inclusion-exclusion formula holds:
  m(A ∪ B) + m(A ∩ B) = m(A) + m(B)

**Why**: This follows from K&S Section 5.2 applied to the GBA `Set α`.

**Examples**:
- Uniform measure on Fin n: m(A) = |A|/n
- Weighted measure: m(A) = Σᵢ∈A pᵢ
- Coin flip: m({H}) = m({T}) = 1/2

All of these are Generalized Boolean Algebras with disjoint-additive measures,
so Section 5.2 applies.

## Summary

Finite probability on sets is naturally phrased at the level of generalized Boolean algebras.
K\&S Section 5.2 isolates exactly the algebraic identity (inclusion--exclusion) that underlies
finite additivity in this setting.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
