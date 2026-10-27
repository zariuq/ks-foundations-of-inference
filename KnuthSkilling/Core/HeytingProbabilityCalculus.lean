/-
# Interval bounds and sound conditional observations

Monotonicity supplies endpoint inequalities. Conditional ratios are outer
bounds for every supplied compatible modular valuation when the lower evidence
bound is positive. The upper ratio can exceed one, so the observation theorem
clips it at one. Total real division at zero supplies no conditioning guarantee.
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.HeytingValuation
import KnuthSkilling.Core.HeytingBounds

namespace KnuthSkilling.Heyting

variable {α : Type*} [DistribLattice α] [BoundedOrder α]

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

section IntervalArithmetic

variable (iv : IntervalValuation α)

/-- The interval for ⊥ is {0}. -/
theorem interval_bot : iv.interval ⊥ = {0} := by
  simp only [IntervalValuation.interval, iv.lower_bot, iv.upper_bot, Set.Icc_self]

/-- The interval for ⊤ is {1}. -/
theorem interval_top : iv.interval ⊤ = {1} := by
  simp only [IntervalValuation.interval, iv.lower_top, iv.upper_top, Set.Icc_self]

/-- Comparable inputs have coordinatewise ordered endpoints; this is not set containment. -/
theorem interval_le_of_le {a b : α} (h : a ≤ b) :
    iv.lower a ≤ iv.lower b ∧ iv.upper a ≤ iv.upper b :=
  ⟨iv.lower_monotone h, iv.upper_monotone h⟩

end IntervalArithmetic

section Conditioning

variable (iv : IntervalValuation α)

/-- The meet is below the evidence at both endpoints. -/
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

section ConditionalSoundness
variable {α : Type*} [HeytingAlgebra α]

/-- Every compatible valuation's conditional value lies in the clipped outer bounds. -/
theorem conditionalBounds_sound (iv : IntervalValuation α) (ν : ModularValuation α)
    (hν : IntervalValuation.Compatible ν iv) (a e : α) (he : 0 < iv.lower e) :
    ν.val (a ⊓ e) / ν.val e ∈
      Set.Icc (conditionalLowerBound' iv a e) (min 1 (conditionalUpperBound' iv a e)) := by
  have hv : 0 < ν.val e := lt_of_lt_of_le he (hν e).1
  constructor
  · exact div_le_div₀ (ν.nonneg _) (hν (a ⊓ e)).1 hv (hν e).2
  · apply le_min
    · exact (div_le_one hv).mpr (ν.monotone inf_le_right)
    · exact div_le_div₀ (le_trans (ν.nonneg _) (hν (a ⊓ e)).2) (hν (a ⊓ e)).2 he (hν e).1

/-- The complement-derived interval carries a compatible witness automatically. -/
theorem conditionalBounds_ofHeyting (ν : ModularValuation α) (a e : α) (he : 0 < ν.val e) :
    ν.val (a ⊓ e) / ν.val e ∈
      Set.Icc (conditionalLowerBound' (IntervalValuation.ofHeyting ν) a e)
        (min 1 (conditionalUpperBound' (IntervalValuation.ofHeyting ν) a e)) :=
  conditionalBounds_sound _ ν (IntervalValuation.ofHeyting_compatible ν) a e he

end ConditionalSoundness

/-- Raw upper ratios need clipping even for realizable complement-derived intervals. -/
theorem threeChain_conditional_upper_exceeds_one :
    conditionalUpperBound' (IntervalValuation.ofHeyting threeChainValuation)
      (1 : Fin 3) (1 : Fin 3) = 2 ∧
      threeChainValuation.val ((1 : Fin 3) ⊓ 1) / threeChainValuation.val 1 = 1 := by
  norm_num [conditionalUpperBound', IntervalValuation.ofHeyting, lowerBound, upperBound,
    threeChainValuation]

theorem threeChain_zero_evidence :
    ¬0 < (IntervalValuation.ofHeyting threeChainValuation).lower (0 : Fin 3) := by
  norm_num [IntervalValuation.ofHeyting, lowerBound, threeChainValuation]

end KnuthSkilling.Heyting
