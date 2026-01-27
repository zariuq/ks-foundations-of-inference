/-
# Interval Probability Calculus for Heyting K&S

## Overview

This file develops probability calculus for interval-valued probabilities
on distributive lattices (including Heyting algebras).

For intervals, we get bounds from monotonicity:
- lower(A ⊔ B) ≥ max(lower(A), lower(B))
- upper(A ⊓ B) ≤ min(upper(A), upper(B))

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- de Cooman & Hermans, "Imprecise probability trees" (2008)
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingValuation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingIntervalRepresentation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

variable {α : Type*} [DistribLattice α] [BoundedOrder α]

/-! ## Basic Interval Bounds from Monotonicity -/

section MonotonicityBounds

variable (iv : IntervalValuation α)

/-- Lower bound for join: the join is at least as large as either argument. -/
theorem lower_sup_ge_max (a b : α) :
    iv.lower (a ⊔ b) ≥ max (iv.lower a) (iv.lower b) := by
  apply max_le
  · exact iv.lower_monotone le_sup_left
  · exact iv.lower_monotone le_sup_right

/-- Upper bound for join: bounded by 1. -/
theorem upper_sup_le_one (a b : α) :
    iv.upper (a ⊔ b) ≤ 1 :=
  iv.upper_le_one (a ⊔ b)

/-- Lower bound for meet: bounded by either argument. -/
theorem lower_inf_le_min (a b : α) :
    iv.lower (a ⊓ b) ≤ min (iv.lower a) (iv.lower b) := by
  apply le_min
  · exact iv.lower_monotone inf_le_left
  · exact iv.lower_monotone inf_le_right

/-- Upper bound for meet: bounded by either argument. -/
theorem upper_inf_le_min (a b : α) :
    iv.upper (a ⊓ b) ≤ min (iv.upper a) (iv.upper b) := by
  apply le_min
  · exact iv.upper_monotone inf_le_left
  · exact iv.upper_monotone inf_le_right

/-- Lower bound for meet: non-negative. -/
theorem lower_inf_nonneg (a b : α) :
    0 ≤ iv.lower (a ⊓ b) :=
  iv.lower_nonneg (a ⊓ b)

end MonotonicityBounds

/-! ## Interval Arithmetic Properties -/

section IntervalArithmetic

variable (iv : IntervalValuation α)

/-- The interval for ⊥ is {0}. -/
theorem interval_bot : iv.interval ⊥ = {0} := by
  simp only [IntervalValuation.interval, iv.lower_bot, iv.upper_bot, Set.Icc_self]

/-- The interval for ⊤ is {1}. -/
theorem interval_top : iv.interval ⊤ = {1} := by
  simp only [IntervalValuation.interval, iv.lower_top, iv.upper_top, Set.Icc_self]

/-- For a ≤ b, the intervals are nested: interval(a) has lower values than interval(b). -/
theorem interval_le_of_le {a b : α} (h : a ≤ b) :
    iv.lower a ≤ iv.lower b ∧ iv.upper a ≤ iv.upper b :=
  ⟨iv.lower_monotone h, iv.upper_monotone h⟩

/-
Note: The converse "disjoint intervals imply comparable elements" requires
FaithfulIntervalValuation. For a general IntervalValuation, intervals can be
disjoint even for incomparable elements (the valuation may not faithfully
represent the lattice structure).

See `FaithfulIntervalValuation.interval_intersect_of_incomparable` in
HeytingIntervalRepresentation.lean for the faithful case.
-/

end IntervalArithmetic

/-! ## Conditioning Basics -/

section Conditioning

variable (iv : IntervalValuation α)

/-- For conditioning, we need the evidence to have positive probability.
    The conditioned interval is related to the meet. -/
theorem conditioning_meet_bound (a e : α) :
    iv.lower (a ⊓ e) ≤ iv.lower e ∧ iv.upper (a ⊓ e) ≤ iv.upper e :=
  ⟨iv.lower_monotone inf_le_right, iv.upper_monotone inf_le_right⟩

/-- The conditional probability lower bound: lower(a ∧ e) / upper(e).
    P(a | e) ≈ P(a ∧ e) / P(e), so this gives a lower bound. -/
noncomputable def conditionalLowerBound' (a e : α) : ℝ :=
  iv.lower (a ⊓ e) / iv.upper e

/-- The conditional probability upper bound: upper(a ∧ e) / lower(e). -/
noncomputable def conditionalUpperBound' (a e : α) : ℝ :=
  iv.upper (a ⊓ e) / iv.lower e

/-- Conditional lower bound is in [0, 1] when evidence has positive upper probability. -/
theorem conditionalLowerBound'_mem_unit (a e : α) (he : 0 < iv.upper e) :
    0 ≤ conditionalLowerBound' iv a e ∧ conditionalLowerBound' iv a e ≤ 1 := by
  constructor
  · apply div_nonneg (iv.lower_nonneg _) (le_of_lt he)
  · unfold conditionalLowerBound'
    rw [div_le_one he]
    calc iv.lower (a ⊓ e) ≤ iv.upper (a ⊓ e) := iv.lower_le_upper _
      _ ≤ iv.upper e := iv.upper_monotone inf_le_right

end Conditioning

/-! ## Summary

This file provides basic interval arithmetic for Heyting probability:

1. **Monotonicity Bounds**:
   - lower(A ⊔ B) ≥ max(lower(A), lower(B))
   - upper(A ⊓ B) ≤ min(upper(A), upper(B))

2. **Interval Properties**:
   - interval(⊥) = {0}, interval(⊤) = {1}
   - Comparable elements have consistently ordered intervals

3. **Conditioning**:
   - P(A|E) lower bound: lower(A∧E) / upper(E)
   - P(A|E) upper bound: upper(A∧E) / lower(E)

The key insight: interval arithmetic from monotonicity alone gives useful bounds,
but stronger results (like disjoint intervals implying comparability) require
the FaithfulIntervalValuation structure from HeytingIntervalRepresentation.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting
