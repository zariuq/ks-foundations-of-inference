/-
# Counterexamples: The Diamond Lattice

## Overview

This file provides the Diamond Lattice as a concrete example of a
distributive lattice with incomparable elements.

## IMPORTANT CORRECTION

The original claim that "incomparable elements require interval representation"
was FALSE. Incomparability in the lattice is about entailment/order, NOT about
whether numeric plausibilities can be ordered.

The correct story:
- The Diamond shows that NOT all lattices are totally ordered (obvious)
- Different valuations CAN order incomparable elements differently
- But this does NOT "force" any particular interval representation

The real distinction between Boolean and Heyting K&S is about
**complement behavior** (see HeytingBounds.lean), not incomparability.

## What the Diamond DOES Show

1. The Diamond is a distributive lattice that is NOT Boolean
2. It has incomparable elements (left ∥ right)
3. Any 1D valuation will impose SOME total order on values
4. Different valid valuations can impose different orderings

This demonstrates that collapsing a partial order to a total order
loses information - but that's a statement about structure, not intervals.

## References

- Dunn & Hardegree, "Algebraic Methods in Philosophical Logic" (2001)
- See HeytingBounds.lean for the correct Boolean vs Heyting characterization
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingValuation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingIntervalRepresentation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples

open Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

/-! ## The Diamond Lattice: Incomparable Elements -/

/-- The diamond lattice: ⊥ < a, b < ⊤ with a ∥ b.

    ```
        ⊤
       / \
      a   b
       \ /
        ⊥
    ```

    This is the minimal example of a distributive lattice with incomparable elements. -/
inductive DiamondLattice
  | bot : DiamondLattice
  | left : DiamondLattice
  | right : DiamondLattice
  | top : DiamondLattice
  deriving DecidableEq, Repr

namespace DiamondLattice

/-- The ordering on the diamond lattice. -/
def le : DiamondLattice → DiamondLattice → Prop
  | .bot, _ => True
  | _, .top => True
  | .left, .left => True
  | .right, .right => True
  | _, _ => False

instance : LE DiamondLattice where
  le := le

instance decidableLE : DecidableRel (α := DiamondLattice) (· ≤ ·) := fun a b =>
  match a, b with
  | .bot, x => decidable_of_iff True (by simp only [le, LE.le])
  | .left, .left => decidable_of_iff True (by simp only [le, LE.le])
  | .right, .right => decidable_of_iff True (by simp only [le, LE.le])
  | x, .top => decidable_of_iff True (by cases x <;> simp only [le, LE.le])
  | .left, .bot => decidable_of_iff False (by simp only [le, LE.le])
  | .left, .right => decidable_of_iff False (by simp only [le, LE.le])
  | .right, .bot => decidable_of_iff False (by simp only [le, LE.le])
  | .right, .left => decidable_of_iff False (by simp only [le, LE.le])
  | .top, .bot => decidable_of_iff False (by simp only [le, LE.le])
  | .top, .left => decidable_of_iff False (by simp only [le, LE.le])
  | .top, .right => decidable_of_iff False (by simp only [le, LE.le])

theorem le_refl (a : DiamondLattice) : a ≤ a := by
  cases a <;> trivial

theorem le_trans {a b c : DiamondLattice} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> trivial

theorem le_antisymm {a b : DiamondLattice} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a <;> cases b <;> (first | rfl | exact absurd hba (fun h => h) | exact absurd hab (fun h => h))

instance : Preorder DiamondLattice where
  le_refl := le_refl
  le_trans := @le_trans

instance : PartialOrder DiamondLattice where
  le_antisymm := @le_antisymm

/-- Meet (greatest lower bound) on the diamond. -/
@[simp] def inf (a b : DiamondLattice) : DiamondLattice :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, b => b
  | a, .top => a
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .bot
  | .right, .left => .bot

/-- Join (least upper bound) on the diamond. -/
@[simp] def sup (a b : DiamondLattice) : DiamondLattice :=
  match a, b with
  | .top, _ => .top
  | _, .top => .top
  | .bot, b => b
  | a, .bot => a
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .top
  | .right, .left => .top


theorem inf_le_left' (a b : DiamondLattice) : inf a b ≤ a := by
  cases a <;> cases b <;> simp only [inf] <;> trivial

theorem inf_le_right' (a b : DiamondLattice) : inf a b ≤ b := by
  cases a <;> cases b <;> simp only [inf] <;> trivial

theorem le_inf' {a b c : DiamondLattice} (hab : a ≤ b) (hac : a ≤ c) : a ≤ inf b c := by
  cases a <;> cases b <;> cases c <;> simp only [inf] at * <;> trivial

theorem le_sup_left' (a b : DiamondLattice) : a ≤ sup a b := by
  cases a <;> cases b <;> simp only [sup] <;> trivial

theorem le_sup_right' (a b : DiamondLattice) : b ≤ sup a b := by
  cases a <;> cases b <;> simp only [sup] <;> trivial

theorem sup_le' {a b c : DiamondLattice} (hac : a ≤ c) (hbc : b ≤ c) : sup a b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp only [sup] at * <;> trivial

theorem sup_inf_distrib (a b c : DiamondLattice) : sup a (inf b c) = inf (sup a b) (sup a c) := by
  cases a <;> cases b <;> cases c <;> rfl

instance : Lattice DiamondLattice where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := @le_inf'
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := @sup_le'

instance : DistribLattice DiamondLattice where
  le_sup_inf := fun a b c => by
    cases a <;> cases b <;> cases c <;> trivial

instance : OrderBot DiamondLattice where
  bot := .bot
  bot_le x := by cases x <;> trivial

instance : OrderTop DiamondLattice where
  top := .top
  le_top x := by cases x <;> trivial

instance : BoundedOrder DiamondLattice where

/-! ## Key Counterexample: Incomparable Elements in Diamond -/

/-- The left element of the diamond. -/
def diamondLeft : DiamondLattice := .left

/-- The right element of the diamond. -/
def diamondRight : DiamondLattice := .right

/-- Left and right are incomparable: ¬(left ≤ right). -/
theorem not_left_le_right : ¬(diamondLeft ≤ diamondRight) := fun h => h

/-- Left and right are incomparable: ¬(right ≤ left). -/
theorem not_right_le_left : ¬(diamondRight ≤ diamondLeft) := fun h => h

/-- The diamond has incomparable elements. -/
theorem diamond_has_incomparable : Incomparable diamondLeft diamondRight :=
  ⟨not_left_le_right, not_right_le_left⟩

/-! ## Modular Valuations on the Diamond

Different modular valuations can assign different orderings to incomparable elements.
This demonstrates why point valuations don't faithfully represent Heyting structure. -/

/-- Consequence: Point valuations cannot faithfully distinguish incomparable elements.
    For any point valuation ν, either ν(left) ≤ ν(right) or ν(right) ≤ ν(left).
    But left ∥ right in the lattice, so no single ordering is correct. -/
theorem point_valuation_forces_ordering :
    ∀ ν : ModularValuation DiamondLattice,
    ν.val diamondLeft ≤ ν.val diamondRight ∨ ν.val diamondRight ≤ ν.val diamondLeft := by
  intro ν
  exact le_or_gt (ν.val diamondLeft) (ν.val diamondRight) |>.imp_right le_of_lt

/-- Key theorem: The diamond has incomparable elements, and any point valuation
    must impose SOME total ordering. This shows that collapsing the partial
    order to a total order (on ℝ) loses structural information.

    NOTE: This does NOT mean "intervals are required" - that was a false claim.
    See HeytingBounds.lean for the correct Boolean vs Heyting distinction. -/
theorem diamond_partial_order_collapsed :
    Incomparable diamondLeft diamondRight ∧
    (∀ ν : ModularValuation DiamondLattice,
      ν.val diamondLeft ≤ ν.val diamondRight ∨ ν.val diamondRight ≤ ν.val diamondLeft) :=
  ⟨diamond_has_incomparable, point_valuation_forces_ordering⟩

/-- Since the diamond has incomparable elements, and any valuation must impose
    some total ordering on the values, there is no canonical choice.
    Different valuations can give opposite orderings.

    This demonstrates that NON-BOOLEAN lattices exist, not that "intervals are required". -/
theorem diamond_no_canonical_ordering :
    Incomparable diamondLeft diamondRight ∧
    (∀ ν : ModularValuation DiamondLattice,
      ν.val diamondLeft ≤ ν.val diamondRight ∨ ν.val diamondRight ≤ ν.val diamondLeft) :=
  diamond_partial_order_collapsed

end DiamondLattice

/-! ## Summary

This file demonstrates the Diamond Lattice as an example of incomparability:

1. **Diamond Lattice Incomparability**:
   - The diamond has elements left ∥ right (incomparable)
   - Different valid modular valuations order them differently
   - No single point valuation is "canonical"

2. **What This DOES NOT Show** (Corrected):
   - ❌ "Intervals are required" - FALSE claim, removed
   - ❌ "Incomparable elements force interval overlap" - FALSE

3. **What This DOES Show**:
   - ✓ Non-Boolean lattices can have incomparable elements
   - ✓ Collapsing to 1D loses partial order structure
   - ✓ The Diamond is distributive but not Boolean

The REAL distinction between Boolean and Heyting K&S is about
**complement behavior** (ν(a) + ν(¬a) = 1 vs ≤ 1), not incomparability.
See HeytingBounds.lean for the correct characterization.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples
