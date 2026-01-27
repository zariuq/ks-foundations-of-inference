/-
# Interval Valuations for Imprecise Probability

## Overview

This file defines **interval valuations** that assign each lattice element
a closed interval [lower, upper] ⊆ [0,1] instead of a single point.

Interval valuations are useful for:
- Imprecise probability (Walley, credal sets)
- Upper/lower probability bounds
- Robust Bayesian analysis

## IMPORTANT CORRECTION

This file previously claimed that "incomparable elements must have overlapping
intervals" - that claim was FALSE and has been removed.

The correct characterization of the Boolean vs Heyting distinction is in
`HeytingBounds.lean`, which shows:
- The gate is the **complement behavior**: ν(a) + ν(¬a) = 1 (Boolean) vs ≤ 1 (Heyting)
- The interval [ν(a), 1 - ν(¬a)] captures the "excluded middle gap"
- Boolean algebras collapse to points; Heyting algebras have slack

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- Augustin et al., "Introduction to Imprecise Probabilities" (2014)
- See HeytingBounds.lean for the correct Heyting characterization
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingValuation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

/-! ## Interval Valuations for Imprecise Probability -/

/-- An **interval valuation** assigns each lattice element a closed interval [lower, upper] ⊆ [0,1].

    This is useful for imprecise probability where we don't commit to a single
    probability value but instead maintain bounds.

    Note: This is a general structure for imprecise probability.
    For the specific Heyting K&S characterization (where intervals arise from
    non-Boolean complement behavior), see `HeytingBounds.lean`. -/
structure IntervalValuation (α : Type*) [DistribLattice α] [BoundedOrder α] where
  /-- Lower bound function -/
  lower : α → ℝ
  /-- Upper bound function -/
  upper : α → ℝ
  /-- Intervals are well-formed -/
  lower_le_upper : ∀ a, lower a ≤ upper a
  /-- Lower bounds are monotone -/
  lower_monotone : Monotone lower
  /-- Upper bounds are monotone -/
  upper_monotone : Monotone upper
  /-- Bottom maps to 0 -/
  lower_bot : lower ⊥ = 0
  upper_bot : upper ⊥ = 0
  /-- Top maps to 1 -/
  lower_top : lower ⊤ = 1
  upper_top : upper ⊤ = 1
  /-- Lower bounds are non-negative -/
  lower_nonneg : ∀ a, 0 ≤ lower a
  /-- Upper bounds are at most 1 -/
  upper_le_one : ∀ a, upper a ≤ 1

namespace IntervalValuation

variable {α : Type*} [DistribLattice α] [BoundedOrder α]
variable (iv : IntervalValuation α)

/-! ## Basic Properties -/

/-- The interval associated with an element. -/
def interval (a : α) : Set ℝ := Set.Icc (iv.lower a) (iv.upper a)

/-- Intervals are non-empty (since lower ≤ upper). -/
theorem interval_nonempty (a : α) : (iv.interval a).Nonempty := by
  use iv.lower a
  simp only [interval, Set.mem_Icc, le_refl, iv.lower_le_upper, and_self]

/-- Intervals are bounded in [0, 1]. -/
theorem interval_subset_unit (a : α) : iv.interval a ⊆ Set.Icc 0 1 := by
  intro x hx
  simp only [interval, Set.mem_Icc] at hx ⊢
  constructor
  · calc 0 ≤ iv.lower a := iv.lower_nonneg a
         _ ≤ x := hx.1
  · calc x ≤ iv.upper a := hx.2
         _ ≤ 1 := iv.upper_le_one a

/-- The width of an interval (measures uncertainty/imprecision). -/
noncomputable def width (a : α) : ℝ := iv.upper a - iv.lower a

/-- Widths are non-negative. -/
theorem width_nonneg (a : α) : 0 ≤ iv.width a := by
  unfold width
  have := iv.lower_le_upper a
  linarith

/-- Bottom has zero width. -/
theorem width_bot : iv.width ⊥ = 0 := by
  unfold width
  simp only [iv.lower_bot, iv.upper_bot, sub_self]

/-- Top has zero width. -/
theorem width_top : iv.width ⊤ = 0 := by
  unfold width
  simp only [iv.lower_top, iv.upper_top, sub_self]

/-! ## Point Valuations as Special Case -/

/-- A point valuation is an interval valuation where lower = upper everywhere. -/
def IsPoint : Prop := ∀ a, iv.lower a = iv.upper a

/-- For point valuations, width is zero everywhere. -/
theorem width_zero_of_isPoint (h : iv.IsPoint) (a : α) : iv.width a = 0 := by
  unfold width
  rw [h a]
  ring

/-! ## Converting ModularValuation to IntervalValuation -/

/-- Every ModularValuation gives rise to a (trivial) point-valued IntervalValuation. -/
def ofModular (ν : ModularValuation α) : IntervalValuation α where
  lower := ν.val
  upper := ν.val
  lower_le_upper _ := le_refl _
  lower_monotone := ν.monotone
  upper_monotone := ν.monotone
  lower_bot := ν.val_bot
  upper_bot := ν.val_bot
  lower_top := ν.val_top
  upper_top := ν.val_top
  lower_nonneg := ν.nonneg
  upper_le_one := ν.le_one

/-- An IntervalValuation from a ModularValuation is always a point valuation. -/
theorem ofModular_isPoint (ν : ModularValuation α) :
    (ofModular ν).IsPoint := fun _ => rfl

/-! ## Compatibility with ModularValuations -/

/-- A ModularValuation is **compatible** with an IntervalValuation if it fits inside. -/
def Compatible (ν : ModularValuation α) (iv : IntervalValuation α) : Prop :=
  ∀ a, iv.lower a ≤ ν.val a ∧ ν.val a ≤ iv.upper a

/-- The trivial interval from a modular valuation is compatible with itself. -/
theorem ofModular_compatible (ν : ModularValuation α) :
    Compatible ν (ofModular ν) := by
  intro a
  simp only [ofModular, le_refl, and_self]

end IntervalValuation

/-! ## Incomparable Elements -/

/-- Two elements are **incomparable** if neither is less than or equal to the other. -/
def Incomparable {α : Type*} [Preorder α] (a b : α) : Prop := ¬(a ≤ b) ∧ ¬(b ≤ a)

/-- For a totally ordered type, all elements are comparable. -/
theorem totalOrder_no_incomparable {β : Type*} [LinearOrder β] (a b : β) :
    ¬Incomparable a b := by
  intro ⟨hab, hba⟩
  rcases le_or_gt a b with h | h
  · exact hab h
  · exact hba (le_of_lt h)

/-! ## The Space of Compatible Valuations -/

section ValuationSpace

variable {α : Type*} [DistribLattice α] [BoundedOrder α]

/-- The set of all ModularValuations compatible with a given IntervalValuation. -/
def compatibleValuations (iv : IntervalValuation α) : Set (ModularValuation α) :=
  { ν | IntervalValuation.Compatible ν iv }

/-- An interval valuation is **realizable** if there exists a compatible ModularValuation. -/
def IntervalValuation.Realizable (iv : IntervalValuation α) : Prop :=
  ∃ ν : ModularValuation α, IntervalValuation.Compatible ν iv

/-- A point interval valuation is always realizable (by the valuation it came from). -/
theorem IntervalValuation.ofModular_realizable (ν : ModularValuation α) :
    (IntervalValuation.ofModular ν).Realizable :=
  ⟨ν, IntervalValuation.ofModular_compatible ν⟩

end ValuationSpace

/-! ## Interval Width Statistics -/

section WidthStatistics

variable {α : Type*} [DistribLattice α] [BoundedOrder α]

/-- The maximum width across all elements (for finite lattices). -/
noncomputable def maxWidth (iv : IntervalValuation α) [Fintype α] : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty) iv.width

/-- For point valuations, max width is zero. -/
theorem maxWidth_zero_of_isPoint [Fintype α] (iv : IntervalValuation α) (h : iv.IsPoint) :
    maxWidth iv = 0 := by
  simp only [maxWidth]
  have hw : ∀ a : α, iv.width a = 0 := iv.width_zero_of_isPoint h
  apply Finset.sup'_eq_of_forall
  intro a _
  exact hw a

end WidthStatistics

/-! ## Summary

This file provides:

1. **IntervalValuation**: A structure for imprecise probability that assigns
   intervals [lower, upper] ⊆ [0,1] to each element.

2. **Point valuations**: The special case where intervals collapse to points.

3. **Compatibility**: When a precise (modular) valuation fits within intervals.

4. **Width statistics**: Measures of imprecision.

IMPORTANT: The distinction between Boolean and Heyting K&S is NOT about
"incomparable elements forcing interval overlap" (that was a false claim).

The correct characterization is in `HeytingBounds.lean`:
- Define lower(a) := ν(a), upper(a) := 1 - ν(¬a)
- The gap upper - lower equals the excluded middle gap
- Boolean: gap = 0 (points); Heyting: gap ≥ 0 (intervals with slack)
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting
