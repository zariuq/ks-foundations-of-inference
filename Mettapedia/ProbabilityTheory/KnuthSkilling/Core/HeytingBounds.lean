/-
# Heyting Bounds: The Correct Gate Between Boolean and Heyting K&S

## The Key Insight

The difference between Boolean and Heyting K&S is NOT about "incomparable elements
forcing interval overlap" (that claim is false).

The real gate is the **complement behavior**:
- Boolean: ν(a) + ν(¬a) = 1 (equality)
- Heyting: ν(a) + ν(¬a) ≤ 1 (inequality - there's slack!)

## The Correct Interval Construction

From a modular valuation ν on a Heyting algebra, define:
- lower(a) := ν(a)
- upper(a) := 1 - ν(¬a)

Then:
- lower(a) ≤ upper(a) follows immediately from ν(a) + ν(¬a) ≤ 1
- The gap upper(a) - lower(a) = 1 - ν(a) - ν(¬a) is exactly the "excluded middle gap"!

## Connection to Intuitionistic Logic

In intuitionistic logic, we have ¬¬a ≥ a but generally ¬¬a ≠ a.
The interval [lower(a), upper(a)] captures this:
- lower(a) = ν(a) is the "direct evidence for a"
- upper(a) = 1 - ν(¬a) is the "absence of evidence against a"

In classical logic these coincide. In intuitionistic logic, there's a gap!

## References

- This corrects the approach in HeytingIntervalRepresentation.lean
- Connects to the excludedMiddleGap in HeytingValuation.lean
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingValuation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

variable {α : Type*} [HeytingAlgebra α]

/-! ## The Heyting Bounds Construction -/

/-- Lower bound: direct evidence for a.
    This is simply the valuation ν(a). -/
noncomputable def lowerBound (ν : ModularValuation α) (a : α) : ℝ := ν.val a

/-- Upper bound: absence of evidence against a.
    This is 1 - ν(¬a), representing the "room left" after accounting for ¬a. -/
noncomputable def upperBound (ν : ModularValuation α) (a : α) : ℝ := 1 - ν.val aᶜ

/-! ## The Core Gate Theorem -/

/-- **The Heyting Gate**: lower(a) ≤ upper(a).

    This follows directly from the Heyting negation inequality ν(a) + ν(¬a) ≤ 1.
    Rearranging: ν(a) ≤ 1 - ν(¬a). -/
theorem lower_le_upper (ν : ModularValuation α) (a : α) :
    lowerBound ν a ≤ upperBound ν a := by
  unfold lowerBound upperBound
  have h := heyting_not_boolean_complement ν a
  linarith

/-- The gap between upper and lower is exactly the excluded middle gap! -/
theorem bound_gap_eq_em_gap (ν : ModularValuation α) (a : α) :
    upperBound ν a - lowerBound ν a = excludedMiddleGap ν a := by
  unfold upperBound lowerBound excludedMiddleGap
  -- Need: (1 - ν(¬a)) - ν(a) = 1 - ν(a ⊔ ¬a)
  -- From modularity: ν(a) + ν(¬a) = ν(a ⊔ ¬a) + ν(a ⊓ ¬a)
  -- And a ⊓ ¬a = ⊥, so ν(a ⊓ ¬a) = 0
  -- Thus: ν(a) + ν(¬a) = ν(a ⊔ ¬a)
  -- So: 1 - ν(¬a) - ν(a) = 1 - (ν(a) + ν(¬a)) = 1 - ν(a ⊔ ¬a)
  have hmod := ν.modular a aᶜ
  rw [inf_compl_self, ν.val_bot, add_zero] at hmod
  linarith

/-! ## Boolean Collapse Theorem -/

/-- **Boolean Collapse**: In a Boolean algebra, upper = lower (intervals collapse to points).

    This is because ν(a) + ν(¬a) = 1 in Boolean algebras. -/
theorem boolean_collapse {β : Type*} [BooleanAlgebra β]
    (ν : ModularValuation β) (a : β) :
    upperBound ν a = lowerBound ν a := by
  unfold upperBound lowerBound
  have h := ModularValuation.boolean_complement_rule ν a
  linarith

/-- In Boolean algebras, the bound gap is zero. -/
theorem boolean_gap_zero {β : Type*} [BooleanAlgebra β]
    (ν : ModularValuation β) (a : β) :
    upperBound ν a - lowerBound ν a = 0 := by
  rw [boolean_collapse]
  ring

/-! ## Non-Boolean Gap Existence -/

/-- Elements satisfying excluded middle have zero gap. -/
theorem gap_zero_of_em (ν : ModularValuation α) (a : α) (h : a ⊔ aᶜ = ⊤) :
    upperBound ν a - lowerBound ν a = 0 := by
  rw [bound_gap_eq_em_gap]
  exact excludedMiddleGap_eq_zero_of_em ν a h

/-- Elements NOT satisfying excluded middle have positive gap (when ν is "faithful").
    Note: h_not_em is the semantic condition; h_faithful ensures ν detects it. -/
theorem gap_pos_of_not_em (ν : ModularValuation α) (a : α)
    (_h_not_em : a ⊔ aᶜ ≠ ⊤)
    (h_faithful : ν.val (a ⊔ aᶜ) < 1) :
    upperBound ν a - lowerBound ν a > 0 := by
  rw [bound_gap_eq_em_gap]
  unfold excludedMiddleGap
  linarith

/-! ## Monotonicity Properties -/

/-- Lower bounds are monotone: a ≤ b implies lower(a) ≤ lower(b). -/
theorem lowerBound_monotone (ν : ModularValuation α) : Monotone (lowerBound ν) := by
  intro a b hab
  exact ν.monotone hab

/-- Upper bounds are monotone: a ≤ b implies upper(a) ≤ upper(b).

    This follows because a ≤ b implies bᶜ ≤ aᶜ (contravariance of complement),
    so ν(bᶜ) ≤ ν(aᶜ), hence 1 - ν(aᶜ) ≤ 1 - ν(bᶜ). -/
theorem upperBound_monotone (ν : ModularValuation α) : Monotone (upperBound ν) := by
  intro a b hab
  unfold upperBound
  have hcompl : bᶜ ≤ aᶜ := compl_le_compl hab
  have hν : ν.val bᶜ ≤ ν.val aᶜ := ν.monotone hcompl
  linarith

/-! ## Bounds on ⊥ and ⊤ -/

/-- Lower bound of ⊥ is 0. -/
theorem lowerBound_bot (ν : ModularValuation α) : lowerBound ν ⊥ = 0 := ν.val_bot

/-- Upper bound of ⊥ is 0 (since ⊥ᶜ = ⊤ and ν(⊤) = 1). -/
theorem upperBound_bot (ν : ModularValuation α) : upperBound ν ⊥ = 0 := by
  unfold upperBound
  simp only [compl_bot, ν.val_top, sub_self]

/-- Lower bound of ⊤ is 1. -/
theorem lowerBound_top (ν : ModularValuation α) : lowerBound ν ⊤ = 1 := ν.val_top

/-- Upper bound of ⊤ is 1 (since ⊤ᶜ = ⊥ and ν(⊥) = 0). -/
theorem upperBound_top (ν : ModularValuation α) : upperBound ν ⊤ = 1 := by
  unfold upperBound
  simp only [compl_top, ν.val_bot, sub_zero]

/-! ## The Heyting Bounds Structure -/

/-- Construct Heyting bounds from a modular valuation. -/
noncomputable def HeytingBounds.mk' (ν : ModularValuation α) : α → ℝ × ℝ :=
  fun a => (lowerBound ν a, upperBound ν a)

/-- The interval [lower(a), upper(a)] for an element. -/
def heytingInterval (ν : ModularValuation α) (a : α) : Set ℝ :=
  Set.Icc (lowerBound ν a) (upperBound ν a)

/-- Intervals are non-empty. -/
theorem heytingInterval_nonempty (ν : ModularValuation α) (a : α) :
    (heytingInterval ν a).Nonempty := by
  use lowerBound ν a
  simp only [heytingInterval, Set.mem_Icc, le_refl, true_and]
  exact lower_le_upper ν a

/-- The width of the interval (measures "non-Boolean-ness"). -/
noncomputable def heytingWidth (ν : ModularValuation α) (a : α) : ℝ :=
  upperBound ν a - lowerBound ν a

/-- Width equals the excluded middle gap. -/
theorem heytingWidth_eq_em_gap (ν : ModularValuation α) (a : α) :
    heytingWidth ν a = excludedMiddleGap ν a :=
  bound_gap_eq_em_gap ν a

/-- Width is non-negative. -/
theorem heytingWidth_nonneg (ν : ModularValuation α) (a : α) : 0 ≤ heytingWidth ν a := by
  unfold heytingWidth
  have h := lower_le_upper ν a
  linarith

/-! ## Summary: The Correct Story

The Heyting bounds construction captures exactly what distinguishes
Boolean from Heyting probability:

1. **Lower bound** = ν(a) = "direct evidence for a"
2. **Upper bound** = 1 - ν(¬a) = "absence of evidence against a"

In Boolean algebras: lower = upper (points)
In Heyting algebras: lower ≤ upper (intervals with slack)

The **width** of the interval is the **excluded middle gap**:
- Zero for elements satisfying a ⊔ ¬a = ⊤
- Positive for elements where excluded middle fails

This is the CORRECT gate between Boolean and Heyting K&S.
It's NOT about "incomparable elements forcing interval overlap"
(that claim was false and has been corrected).

The connection to intuitionistic logic:
- In classical logic: knowing ¬a tells you everything about a
- In intuitionistic logic: ¬a only bounds a from above
- The gap measures how much "epistemic slack" exists
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting
