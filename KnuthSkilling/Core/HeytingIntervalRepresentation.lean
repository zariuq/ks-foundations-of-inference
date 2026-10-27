/-
# Normalized interval observations

Pointwise endpoint bounds and monotonicity do not assert that a compatible
modular valuation exists. Realizability is separate. `ofModular` retains an
exact point readout; the complement-derived interval is supplied by
`IntervalValuation.ofHeyting` in `HeytingBounds`.
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.HeytingValuation

namespace KnuthSkilling.Heyting

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

/-- The interval associated with an element. -/
def interval (a : α) : Set ℝ := Set.Icc (iv.lower a) (iv.upper a)

/-- Intervals are non-empty (since lower ≤ upper). -/
theorem interval_nonempty (a : α) : (iv.interval a).Nonempty := by
  exact Set.nonempty_Icc.mpr (iv.lower_le_upper a)

/-- Intervals are bounded in [0, 1]. -/
theorem interval_subset_unit (a : α) : iv.interval a ⊆ Set.Icc 0 1 := by
  exact Set.Icc_subset_Icc (iv.lower_nonneg a) (iv.upper_le_one a)

/-- The width of an interval (measures uncertainty/imprecision). -/
noncomputable def width (a : α) : ℝ := iv.upper a - iv.lower a

/-- Widths are non-negative. -/
theorem width_nonneg (a : α) : 0 ≤ iv.width a := by
  exact sub_nonneg.mpr (iv.lower_le_upper a)

/-- Bottom has zero width. -/
theorem width_bot : iv.width ⊥ = 0 := by
  unfold width
  simp only [iv.lower_bot, iv.upper_bot, sub_self]

/-- Top has zero width. -/
theorem width_top : iv.width ⊤ = 0 := by
  unfold width
  simp only [iv.lower_top, iv.upper_top, sub_self]

/-- A point valuation is an interval valuation where lower = upper everywhere. -/
def IsPoint : Prop := ∀ a, iv.lower a = iv.upper a

/-- For point valuations, width is zero everywhere. -/
theorem width_zero_of_isPoint (h : iv.IsPoint) (a : α) : iv.width a = 0 := by
  exact sub_eq_zero.mpr (h a).symm

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

/-- A ModularValuation is **compatible** with an IntervalValuation if it fits inside. -/
def Compatible (ν : ModularValuation α) (iv : IntervalValuation α) : Prop :=
  ∀ a, iv.lower a ≤ ν.val a ∧ ν.val a ≤ iv.upper a

/-- The trivial interval from a modular valuation is compatible with itself. -/
theorem ofModular_compatible (ν : ModularValuation α) :
    Compatible ν (ofModular ν) := by
  intro a
  simp only [ofModular, le_refl, and_self]

end IntervalValuation

/-- Two elements are **incomparable** if neither is less than or equal to the other. -/
def Incomparable {α : Type*} [Preorder α] (a b : α) : Prop := ¬(a ≤ b) ∧ ¬(b ≤ a)

/-- For a totally ordered type, all elements are comparable. -/
theorem totalOrder_no_incomparable {β : Type*} [LinearOrder β] (a b : β) :
    ¬Incomparable a b := by
  rintro ⟨hab, hba⟩
  exact (le_total a b).elim hab hba

section ValuationSpace

variable {α : Type*} [DistribLattice α] [BoundedOrder α]

/-- The set of all ModularValuations compatible with a given IntervalValuation. -/
def compatibleValuations (iv : IntervalValuation α) : Set (ModularValuation α) :=
  { ν | IntervalValuation.Compatible ν iv }

/-- An interval valuation is **realizable** if there exists a compatible ModularValuation. -/
def IntervalValuation.Realizable (iv : IntervalValuation α) : Prop :=
  ∃ ν : ModularValuation α, IntervalValuation.Compatible ν iv

/-- The point readout constructed from a modular valuation has that compatible witness. -/
theorem IntervalValuation.ofModular_realizable (ν : ModularValuation α) :
    (IntervalValuation.ofModular ν).Realizable :=
  ⟨ν, IntervalValuation.ofModular_compatible ν⟩

end ValuationSpace

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

end KnuthSkilling.Heyting
