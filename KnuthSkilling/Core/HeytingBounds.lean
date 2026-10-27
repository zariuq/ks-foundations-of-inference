/-
# Heyting bounds as interval observations

The direct and not-refuted readouts define [ν(a), 1-ν(¬a)]. Its width is
an observed complement defect. Negation refines reflection of this interval;
exactness depends on whether the valuation distinguishes a from ¬¬a.
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.HeytingIntervalRepresentation
import Mathlib.Algebra.Order.Group.Pointwise.Interval

namespace KnuthSkilling.Heyting

variable {α : Type*} [HeytingAlgebra α]

/-- Lower bound: direct evidence for a.
    This is simply the valuation ν(a). -/
noncomputable def lowerBound (ν : ModularValuation α) (a : α) : ℝ := ν.val a

/-- Upper bound: absence of evidence against a.
    This is 1 - ν(¬a), representing the "room left" after accounting for ¬a. -/
noncomputable def upperBound (ν : ModularValuation α) (a : α) : ℝ := 1 - ν.val aᶜ

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
  rw [excludedMiddleGap_eq_complementGap]
  dsimp [upperBound, lowerBound, complementGap, ModularValuation.toSumRuleValuation,
    ProbabilityTheory.Common.SumRuleValuation.toAdditive]
  ring

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

/-- Package the complement-derived readout in the existing interval interface. -/
noncomputable def IntervalValuation.ofHeyting (ν : ModularValuation α) : IntervalValuation α where
  lower := lowerBound ν
  upper := upperBound ν
  lower_le_upper := KnuthSkilling.Heyting.lower_le_upper ν
  lower_monotone := lowerBound_monotone ν
  upper_monotone := upperBound_monotone ν
  lower_bot := lowerBound_bot ν
  upper_bot := upperBound_bot ν
  lower_top := lowerBound_top ν
  upper_top := upperBound_top ν
  lower_nonneg := ν.nonneg
  upper_le_one a := sub_le_self _ (ν.nonneg aᶜ)

theorem IntervalValuation.ofHeyting_interval (ν : ModularValuation α) (a : α) :
    (ofHeyting ν).interval a = heytingInterval ν a := rfl

theorem IntervalValuation.ofHeyting_compatible (ν : ModularValuation α) :
    Compatible ν (ofHeyting ν) := fun a =>
    ⟨le_refl _, KnuthSkilling.Heyting.lower_le_upper ν a⟩

theorem heytingWidth_zero_iff_observed (ν : ModularValuation α) (a : α) :
    heytingWidth ν a = 0 ↔ ν.val (a ⊔ aᶜ) = 1 := by
  rw [heytingWidth_eq_em_gap, excludedMiddleGap_eq_complementGap]
  exact complementGap_zero_iff_observed _ _

theorem heytingWidth_zero_iff_of_reflects_top (ν : ModularValuation α)
    (hTop : ∀ x, ν.val x = 1 → x = ⊤) (a : α) :
    heytingWidth ν a = 0 ↔ a ⊔ aᶜ = ⊤ := by
  rw [heytingWidth_eq_em_gap, excludedMiddleGap_eq_complementGap]
  exact complementGap_zero_iff_of_reflects_top _ hTop a

/-- Reflection uses the same involution on numerical answers, x ↦ 1-x. -/
theorem heytingInterval_compl_subset (ν : ModularValuation α) (a : α) :
    heytingInterval ν aᶜ ⊆ (fun x : ℝ => 1 - x) ⁻¹' heytingInterval ν a := by
  rw [heytingInterval, heytingInterval, Set.preimage_const_sub_Icc]
  apply Set.Icc_subset_Icc
  · dsimp [lowerBound, upperBound]; linarith
  · dsimp [lowerBound, upperBound]
    linarith [ν.monotone (le_compl_compl (a := a))]

/-- Exactness belongs to the observation, without identifying a and ¬¬a. -/
theorem heytingInterval_compl_eq_iff (ν : ModularValuation α) (a : α) :
    heytingInterval ν aᶜ = (fun x : ℝ => 1 - x) ⁻¹' heytingInterval ν a ↔
      ν.val aᶜᶜ = ν.val a := by
  rw [heytingInterval, heytingInterval, Set.preimage_const_sub_Icc,
    Set.Icc_eq_Icc_iff (lower_le_upper ν aᶜ)]
  dsimp [lowerBound, upperBound]
  constructor
  · rintro ⟨_, h⟩; linarith
  · intro h; constructor <;> linarith

theorem heytingInterval_compl_eq_of_regular (ν : ModularValuation α) (a : α)
    (ha : aᶜᶜ = a) :
    heytingInterval ν aᶜ = (fun x : ℝ => 1 - x) ⁻¹' heytingInterval ν a :=
  (heytingInterval_compl_eq_iff ν a).mpr (congrArg ν.val ha)

/-- The normalized rank valuation on the three-element Heyting chain. -/
noncomputable def threeChainValuation : ModularValuation (Fin 3) where
  val := fun a => (a.val : ℝ) / 2
  monotone := by
    intro a b hab
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hab
    · norm_num
  val_bot := by norm_num
  val_top := by norm_num
  modular := by
    intro a b
    rcases le_total a b with hab | hba
    · rw [sup_eq_right.mpr hab, inf_eq_left.mpr hab]
      ring
    · rw [sup_eq_left.mpr hba, inf_eq_right.mpr hba]

/-- The three-chain valuation satisfies the strict, one-way fidelity condition
used by K&S: a strict lattice comparison gives a strict scalar comparison. -/
theorem threeChainValuation_strictMono : StrictMono threeChainValuation.val := by
  intro a b hab
  simp only [threeChainValuation]
  apply div_lt_div_of_pos_right
  · exact_mod_cast hab
  · norm_num

/-- A scalar modular valuation can exist on a non-Boolean Heyting algebra while
its induced lower and upper truth bounds remain genuinely distinct.  Thus a
scalar measure and a point-valued Boolean truth assignment are different
notions. -/
theorem threeChain_scalar_measure_with_strict_heyting_gap :
    (1 : Fin 3) ⊔ (1 : Fin 3)ᶜ ≠ ⊤ ∧
    threeChainValuation.val (1 : Fin 3) = (1 : ℝ) / 2 ∧
    lowerBound threeChainValuation (1 : Fin 3) <
      upperBound threeChainValuation (1 : Fin 3) := by
  constructor
  · decide
  constructor
  · norm_num [threeChainValuation]
  · norm_num [lowerBound, upperBound, threeChainValuation]

/-- A normalized but non-injective valuation can hide failure of excluded middle. -/
noncomputable def threeChainEndpointValuation : ModularValuation (Fin 3) :=
  ModularValuation.ofChain (β := Fin 3) (fun a : Fin 3 => if a = 0 then 0 else 1)
    (by intro a b hab; dsimp only; split_ifs <;> try norm_num <;> omega)
    (by change (if (0 : Fin 3) = 0 then (0 : ℝ) else 1) = 0; norm_num)
    (by change (if (2 : Fin 3) = 0 then (0 : ℝ) else 1) = 1; simp [show (2 : Fin 3) ≠ 0 by decide])

theorem threeChain_zero_gap_without_lem :
    heytingWidth threeChainEndpointValuation (1 : Fin 3) = 0 ∧
      (1 : Fin 3) ⊔ (1 : Fin 3)ᶜ ≠ ⊤ := by
  constructor
  · have hc : (1 : Fin 3)ᶜ = 0 := by decide
    norm_num [heytingWidth, lowerBound, upperBound, threeChainEndpointValuation,
      ModularValuation.ofChain, hc]
  · decide

theorem threeChain_negation_strict_refinement :
    heytingInterval threeChainValuation (1 : Fin 3)ᶜ ⊂
      (fun x : ℝ => 1 - x) ⁻¹' heytingInterval threeChainValuation (1 : Fin 3) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨heytingInterval_compl_subset _ _, ?_⟩
  intro heq
  have h := (heytingInterval_compl_eq_iff threeChainValuation (1 : Fin 3)).mp heq
  have hcc : (1 : Fin 3)ᶜᶜ = 2 := by decide
  rw [hcc] at h
  norm_num [threeChainValuation] at h

end KnuthSkilling.Heyting
