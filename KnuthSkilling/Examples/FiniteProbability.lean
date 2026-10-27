import KnuthSkilling.Probability.BooleanRepresentation

/-!
# Finite probability and complemented event decomposition

Set events form a Boolean algebra. Disjoint-additive real weights satisfy
inclusion-exclusion by the shared complemented-lattice argument; neither a finite
sample space nor monotonicity is needed for this algebraic identity.
For concrete supplied weights and normalized probabilities see `Bridges.Model`.
-/

namespace KnuthSkilling.Examples

example {α : Type*} : GeneralizedBooleanAlgebra (Set α) := inferInstance

/-- The actual inclusion-exclusion law, rather than only the lattice instance. -/
theorem finite_probability_modular {α : Type*} (v : Set α → ℝ)
    (h : ∀ A B, Disjoint A B → v (A ∪ B) = v A + v B) (A B : Set α) :
    v (A ∪ B) + v (A ∩ B) = v A + v B :=
  KnuthSkilling.Probability.BooleanRepresentation.modular_of_disjoint_add v h A B

end KnuthSkilling.Examples
