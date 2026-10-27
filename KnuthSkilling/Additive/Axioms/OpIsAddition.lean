/-
# Additive observations of ordered combination

The Hölder and cuts constructions supply an additive order embedding under
separate hypotheses. `Multiplicative ℝ` in the Hölder bridge is a type tag:
its multiplication is real addition, so no logarithm is needed.

Additivity forces an existing identity to map to zero. A positive reference
fixes the remaining scale; translating all values does not preserve additivity.
These algebraic laws support probability interpretations through separate event
and conditioning semantics.
-/

import KnuthSkilling.Additive.Main
import KnuthSkilling.Additive.Axioms.SandwichSeparation

namespace KnuthSkilling.Additive.Axioms.OpIsAddition

open KnuthSkillingMonoidBase KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open KnuthSkilling.Additive
open KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding
open KnuthSkilling.Additive.Axioms.AnomalousPairs

/-! ## Section 1: The Main Derived Result -/

/-- The normalized Hölder representation, with all order and addition laws retained. -/
theorem op_is_addition_via_Θ (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) :=
  representation_from_noAnomalousPairs

/-- Identity-free version: existence of an additive order embedding (no normalization). -/
theorem op_is_addition_via_Θ_semigroup (α : Type*) [KSSemigroupBase α] [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) :=
  representation_semigroup

/-- Alternative path via KSSeparation (the original K&S approach).

`KSSeparation` is the "sandwich axiom" from K&S Appendix A. It implies:
1. Commutativity of `op`
2. The Archimedean property
3. No anomalous pairs

And thus the representation theorem follows. -/
theorem op_is_addition_via_KSSeparation (α : Type*)
    [KnuthSkillingAlgebraBase α] [KSSeparationStrict α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) :=
  exists_Theta_of_hasNormalizedRepresentation α

/-! ## Section 2: Consequences of Additivity -/

/-- Commutativity is a consequence of the additive representation.

If Θ(op x y) = Θ x + Θ y, then since + is commutative in ℝ, we have
Θ(op x y) = Θ(op y x), and since Θ is injective (order-preserving), op x y = op y x. -/
theorem op_comm_from_representation (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∀ x y : α, op x y = op y x :=
  KnuthSkilling.Additive.op_comm_of_hasRepresentationTheorem (α := α)

/-- Iterate of op becomes multiplication in the representation.

Θ(x ⊕ x ⊕ ... ⊕ x) = n · Θ(x) -/
theorem iterate_op_is_smul (α : Type*) [KnuthSkillingMonoidBase α]
    (Θ : α → ℝ) (hΘ_ident : Θ ident = 0) (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y) :
    ∀ (x : α) (n : ℕ), Θ (iterate_op x n) = n * Θ x := by
  intro x n
  induction n with
  | zero => simp [iterate_op_zero, hΘ_ident]
  | succ n ih =>
    rw [iterate_op_succ, hΘ_add, ih]
    simp only [Nat.cast_succ]
    ring

/-! ## Section 3: Uniqueness (Up to Positive Scaling)

The representation Θ : α → ℝ satisfying the three properties is unique up to
a positive multiplicative constant. An identity maps to zero automatically.
-/

/-- If two representations agree at identity, they differ by a positive scale factor.

This is a direct application of `representation_uniqueness_structure` from HolderEmbedding.lean,
which uses only the two supplied representations and a positive reference. -/
theorem representation_unique_up_to_scale (α : Type*) [KnuthSkillingMonoidBase α]
    (Θ₁ Θ₂ : α → ℝ)
    (hΘ₁_order : ∀ a b : α, a ≤ b ↔ Θ₁ a ≤ Θ₁ b)
    (hΘ₂_order : ∀ a b : α, a ≤ b ↔ Θ₂ a ≤ Θ₂ b)
    (hΘ₁_ident : Θ₁ ident = 0)
    (hΘ₂_ident : Θ₂ ident = 0)
    (hΘ₁_add : ∀ x y : α, Θ₁ (op x y) = Θ₁ x + Θ₁ y)
    (hΘ₂_add : ∀ x y : α, Θ₂ (op x y) = Θ₂ x + Θ₂ y)
    (a : α) (ha : ident < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, Θ₂ x = c * Θ₁ x :=
  representation_uniqueness_structure_of_ref Θ₁ Θ₂ hΘ₁_order hΘ₂_order hΘ₁_add hΘ₂_add hΘ₁_ident hΘ₂_ident a ha

/-! All three construction routes interpret the supplied operation, rather than
replacing it. Commutativity is derived from injectivity and real addition;
iteration counts event occurrences. Scale comparison is independent of which
construction produced the maps. -/

end KnuthSkilling.Additive.Axioms.OpIsAddition
