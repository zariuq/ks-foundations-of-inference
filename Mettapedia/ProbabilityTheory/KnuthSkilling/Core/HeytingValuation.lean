/-
# Heyting Valuations: Proper K&S on Distributive Lattices

## The Key Insight

Standard K&S probability on Boolean algebras uses:
- P(A) + P(¬A) = 1

But on Heyting algebras, complements don't satisfy ¬¬a = a, so this doesn't work.

The proper generalization uses the **modularity axiom**:
- ν(x) + ν(y) = ν(x ∨ y) + ν(x ∧ y)

This avoids complements entirely, working directly with lattice operations (∨, ∧).

## Key Properties

On Boolean algebras, modularity + normalization recovers standard probability.
On non-Boolean Heyting algebras, we get a proper probability-like measure
that respects the partial order structure without forcing total ordering.

## References

- nLab: "valuation (measure theory)" - https://ncatlab.org/nlab/show/valuation+(measure+theory)
- Knuth "Lattice Duality" (NASA TR 2004) - https://ntrs.nasa.gov/citations/20040081076
- Knuth "Measuring on Lattices" (arXiv:0909.3684)
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

/-! ## Modular Valuations on Distributive Lattices -/

/-- A **modular valuation** on a distributive lattice satisfies the key axiom
    that makes probability work on non-Boolean structures.

    The modularity axiom `ν(x) + ν(y) = ν(x ∨ y) + ν(x ∧ y)` is the
    lattice-theoretic analogue of inclusion-exclusion, but without
    requiring complements. -/
structure ModularValuation (α : Type*) [DistribLattice α] [BoundedOrder α] where
  /-- The valuation function -/
  val : α → ℝ
  /-- Monotonicity: larger lattice elements get larger values -/
  monotone : Monotone val
  /-- Strictness: bottom gets value 0 -/
  val_bot : val ⊥ = 0
  /-- Normalization: top gets value 1 -/
  val_top : val ⊤ = 1
  /-- **THE KEY AXIOM**: Modularity (lattice inclusion-exclusion) -/
  modular : ∀ x y : α, val x + val y = val (x ⊔ y) + val (x ⊓ y)

namespace ModularValuation

variable {α : Type*} [DistribLattice α] [BoundedOrder α]
variable (ν : ModularValuation α)

/-! ## Basic Properties -/

/-- Values are non-negative. -/
theorem nonneg (a : α) : 0 ≤ ν.val a := by
  have h := ν.monotone (bot_le : ⊥ ≤ a)
  simp only [ν.val_bot] at h
  exact h

/-- Values are at most 1. -/
theorem le_one (a : α) : ν.val a ≤ 1 := by
  have h := ν.monotone (le_top : a ≤ ⊤)
  simp only [ν.val_top] at h
  exact h

/-- Values are bounded in [0, 1]. -/
theorem bounded (a : α) : 0 ≤ ν.val a ∧ ν.val a ≤ 1 :=
  ⟨ν.nonneg a, ν.le_one a⟩

/-! ## Modularity Consequences -/

/-- For disjoint elements (x ⊓ y = ⊥), modularity becomes additivity. -/
theorem additive_of_disjoint {x y : α} (h : x ⊓ y = ⊥) :
    ν.val x + ν.val y = ν.val (x ⊔ y) := by
  have := ν.modular x y
  simp only [h, ν.val_bot, add_zero] at this
  exact this

/-- Symmetric form of modularity. -/
theorem modular_symm (x y : α) :
    ν.val (x ⊔ y) = ν.val x + ν.val y - ν.val (x ⊓ y) := by
  have := ν.modular x y
  linarith

/-- The meet is bounded by either argument's valuation. -/
theorem val_inf_le_left (x y : α) : ν.val (x ⊓ y) ≤ ν.val x :=
  ν.monotone inf_le_left

theorem val_inf_le_right (x y : α) : ν.val (x ⊓ y) ≤ ν.val y :=
  ν.monotone inf_le_right

/-- Either argument's valuation is bounded by the join. -/
theorem val_le_sup_left (x y : α) : ν.val x ≤ ν.val (x ⊔ y) :=
  ν.monotone le_sup_left

theorem val_le_sup_right (x y : α) : ν.val y ≤ ν.val (x ⊔ y) :=
  ν.monotone le_sup_right

end ModularValuation

/-! ## Connection to Boolean Probability -/

/-- On a Boolean algebra, modularity implies the standard complement rule.
    This shows modular valuations generalize Boolean probability.

    Note: Defined outside namespace to avoid typeclass diamond with
    DistribLattice + BoundedOrder vs BooleanAlgebra. -/
theorem ModularValuation.boolean_complement_rule
    {α : Type*} [BooleanAlgebra α] (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ = 1 := by
  have h := ν.modular a aᶜ
  simp only [sup_compl_eq_top, inf_compl_eq_bot, ν.val_top, ν.val_bot, add_zero] at h
  exact h

/-! ## Heyting-Specific Theory

In Heyting algebras, the complement `aᶜ` is defined as `a ⇨ ⊥` (Heyting implication to bottom).
Key properties:
- `a ⊓ aᶜ = ⊥` always (this is `inf_compl_self`)
- `a ⊔ aᶜ ≤ ⊤` always, but `a ⊔ aᶜ = ⊤` only for "classical" elements
-/

section HeytingValuation

variable {α : Type*} [HeytingAlgebra α]

/-- In a Heyting algebra, the pseudo-complement satisfies a ⊓ aᶜ = ⊥.
    Unlike Boolean algebras, a ⊔ aᶜ ≠ ⊤ in general. -/
theorem heyting_not_boolean_complement (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ ≤ 1 := by
  -- ν(a) + ν(aᶜ) = ν(a ⊔ aᶜ) + ν(a ⊓ aᶜ)
  have h := ν.modular a aᶜ
  -- In Heyting algebra: a ⊓ aᶜ = ⊥ always
  rw [inf_compl_self, ν.val_bot, add_zero] at h
  -- But a ⊔ aᶜ ≤ ⊤ (may not equal ⊤!)
  rw [h]
  exact ν.le_one (a ⊔ aᶜ)

/-- The "gap" from excluded middle: how far a ⊔ aᶜ is from ⊤.
    This measures the "non-Boolean-ness" at element a. -/
noncomputable def excludedMiddleGap (ν : ModularValuation α) (a : α) : ℝ :=
  1 - ν.val (a ⊔ aᶜ)

/-- The excluded middle gap is always non-negative. -/
theorem excludedMiddleGap_nonneg (ν : ModularValuation α) (a : α) :
    0 ≤ excludedMiddleGap ν a := by
  unfold excludedMiddleGap
  have h := ν.le_one (a ⊔ aᶜ)
  linarith

/-- For elements satisfying excluded middle, the gap is zero. -/
theorem excludedMiddleGap_eq_zero_of_em (ν : ModularValuation α) (a : α)
    (h : a ⊔ aᶜ = ⊤) : excludedMiddleGap ν a = 0 := by
  unfold excludedMiddleGap
  simp only [h, ν.val_top, sub_self]

/-- Elements satisfying excluded middle behave like Boolean elements. -/
theorem boolean_like_of_em (ν : ModularValuation α) (a : α) (h : a ⊔ aᶜ = ⊤) :
    ν.val a + ν.val aᶜ = 1 := by
  have hmod := ν.modular a aᶜ
  rw [h, inf_compl_self, ν.val_top, ν.val_bot, add_zero] at hmod
  exact hmod

end HeytingValuation

/-! ## The Key Theorem: Valuations Preserve Incomparability Structure -/

section PreservesStructure

variable {α : Type*} [DistribLattice α] [BoundedOrder α]

/-
Key insight about modular valuations and structure preservation:

Unlike naive monotone valuations (which map to totally ordered ℝ),
a modular valuation "remembers" lattice structure through the
relationship between ν(a), ν(b), ν(a ⊓ b), ν(a ⊔ b).

Specifically:
- If a ≤ b, then a ⊓ b = a and a ⊔ b = b, so ν(a ⊓ b) = ν(a)
- If a ∥ b (incomparable), then typically ν(a ⊓ b) < min(ν(a), ν(b))

To make this fully formal would require either:
1. Strict monotonicity: a < b → ν(a) < ν(b), or
2. Faithfulness: ν(a) = ν(b) → a = b

These are stronger than plain monotonicity and represent
different flavors of "non-degenerate" valuations.
-/

omit [BoundedOrder α] in
/-- Weak detection: if a ⊓ b = a, then a ≤ b.
    The contrapositive: if a ≰ b, then a ⊓ b ≠ a.
    This is purely lattice-theoretic (no valuation needed). -/
theorem inf_eq_left_iff_le (a b : α) : a ⊓ b = a ↔ a ≤ b :=
  inf_eq_left

omit [BoundedOrder α] in
/-- Weak detection: if a ⊔ b = a, then b ≤ a.
    The contrapositive: if b ≰ a, then a ⊔ b ≠ a. -/
theorem sup_eq_left_iff_ge (a b : α) : a ⊔ b = a ↔ b ≤ a :=
  sup_eq_left

end PreservesStructure

end Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting
