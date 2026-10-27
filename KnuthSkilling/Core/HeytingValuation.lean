import Mathlib.Order.Heyting.Basic
import ProbabilityTheory.Structures.Valuation.Basic

/-!
# Modular valuations and complement observations

Modularity gives finite inclusion-exclusion without requiring Boolean
complements. The common additive-valuation interface supplies complement-sum
and defect laws. A zero numerical defect identifies excluded middle only when
the valuation detects equality with the top element.
-/

namespace KnuthSkilling.Heyting

/-- A normalized monotone modular valuation. -/
structure ModularValuation (α : Type*) [DistribLattice α] [BoundedOrder α] where
  val : α → ℝ
  monotone : Monotone val
  val_bot : val ⊥ = 0
  val_top : val ⊤ = 1
  modular : ∀ x y : α, val x + val y = val (x ⊔ y) + val (x ⊓ y)

namespace ModularValuation
variable {α : Type*} [DistribLattice α] [BoundedOrder α] (ν : ModularValuation α)

/-- Every normalized monotone readout of a chain is modular. -/
def ofChain {β : Type*} [LinearOrder β] [BoundedOrder β] (f : β → ℝ)
    (hf : Monotone f) (hbot : f ⊥ = 0) (htop : f ⊤ = 1) : ModularValuation β where
  val := f
  monotone := hf
  val_bot := hbot
  val_top := htop
  modular x y := by
    rcases le_total x y with h | h
    · rw [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
    · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]

/-- Modularity supplies the common inclusion-exclusion law with the same values. -/
def toSumRuleValuation : ProbabilityTheory.Common.SumRuleValuation α where
  val := ν.val
  mono _ _ h := ν.monotone h
  val_bot := ν.val_bot
  val_top := ν.val_top
  sum_rule x y := by have h := ν.modular x y; linarith

theorem nonneg (a : α) : 0 ≤ ν.val a := ν.toSumRuleValuation.nonneg a

theorem le_one (a : α) : ν.val a ≤ 1 := ν.toSumRuleValuation.le_one a

theorem bounded (a : α) : 0 ≤ ν.val a ∧ ν.val a ≤ 1 := ν.toSumRuleValuation.bounded a

theorem additive_of_disjoint {x y : α} (h : x ⊓ y = ⊥) :
    ν.val x + ν.val y = ν.val (x ⊔ y) :=
  (ν.toSumRuleValuation.additive_disjoint x y h).symm

theorem modular_symm (x y : α) : ν.val (x ⊔ y) = ν.val x + ν.val y - ν.val (x ⊓ y) :=
  ν.toSumRuleValuation.sum_rule x y

theorem val_inf_le_left (x y : α) : ν.val (x ⊓ y) ≤ ν.val x :=
  ν.toSumRuleValuation.toMonotoneValuation.val_inf_le_left x y

theorem val_inf_le_right (x y : α) : ν.val (x ⊓ y) ≤ ν.val y :=
  ν.toSumRuleValuation.toMonotoneValuation.val_inf_le_right x y

theorem val_le_sup_left (x y : α) : ν.val x ≤ ν.val (x ⊔ y) :=
  ν.toSumRuleValuation.toMonotoneValuation.val_le_sup_left x y

theorem val_le_sup_right (x y : α) : ν.val y ≤ ν.val (x ⊔ y) :=
  ν.toSumRuleValuation.toMonotoneValuation.val_le_sup_right x y

end ModularValuation

theorem ModularValuation.boolean_complement_rule
    {α : Type*} [BooleanAlgebra α] (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ = 1 := by
  simpa [ν.val_bot, ν.val_top] using ν.modular a aᶜ

section ComplementObservation
variable {α : Type*} [HeytingAlgebra α]

/-- Additivity determines the observed value of excluded middle. -/
theorem complementSum_eq_sup (v : ProbabilityTheory.Common.AdditiveValuation α) (a : α) :
    v.val a + v.val aᶜ = v.val (a ⊔ aᶜ) :=
  (v.additive a aᶜ (inf_compl_self a)).symm

/-- Numerical complement defect; it depends on the supplied observation. -/
def complementGap (v : ProbabilityTheory.Common.AdditiveValuation α) (a : α) : ℝ :=
  1 - (v.val a + v.val aᶜ)

theorem complementGap_eq_one_sub_sup (v : ProbabilityTheory.Common.AdditiveValuation α) (a : α) :
    complementGap v a = 1 - v.val (a ⊔ aᶜ) := by
  rw [complementGap, complementSum_eq_sup]

theorem complementGap_nonneg (v : ProbabilityTheory.Common.AdditiveValuation α) (a : α) :
    0 ≤ complementGap v a := by
  rw [complementGap_eq_one_sub_sup]
  exact sub_nonneg.mpr (v.le_one _)

theorem complementGap_zero_iff_observed (v : ProbabilityTheory.Common.AdditiveValuation α) (a : α) :
    complementGap v a = 0 ↔ v.val (a ⊔ aᶜ) = 1 := by
  rw [complementGap_eq_one_sub_sup]
  exact sub_eq_zero.trans eq_comm

/-- Top-reflection suffices; injectivity of the whole valuation is unnecessary. -/
theorem complementGap_zero_iff_of_reflects_top (v : ProbabilityTheory.Common.AdditiveValuation α)
    (hTop : ∀ x, v.val x = 1 → x = ⊤) (a : α) :
    complementGap v a = 0 ↔ a ⊔ aᶜ = ⊤ := by
  rw [complementGap_zero_iff_observed]
  exact ⟨hTop _, fun h => h ▸ v.val_top⟩

theorem heyting_not_boolean_complement (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ ≤ 1 := by
  rw [show ν.val a + ν.val aᶜ = ν.val (a ⊔ aᶜ) from
    complementSum_eq_sup ν.toSumRuleValuation.toAdditive a]
  exact ν.le_one _

noncomputable def excludedMiddleGap (ν : ModularValuation α) (a : α) : ℝ :=
  1 - ν.val (a ⊔ aᶜ)

/-- The modular and additive presentations give the same complement observation. -/
theorem excludedMiddleGap_eq_complementGap (ν : ModularValuation α) (a : α) :
    excludedMiddleGap ν a = complementGap ν.toSumRuleValuation.toAdditive a :=
  (complementGap_eq_one_sub_sup ν.toSumRuleValuation.toAdditive a).symm

theorem excludedMiddleGap_nonneg (ν : ModularValuation α) (a : α) :
    0 ≤ excludedMiddleGap ν a := by
  rw [excludedMiddleGap_eq_complementGap]
  exact complementGap_nonneg _ _

theorem excludedMiddleGap_eq_zero_of_em (ν : ModularValuation α) (a : α)
    (h : a ⊔ aᶜ = ⊤) : excludedMiddleGap ν a = 0 := by
  simp only [excludedMiddleGap, h, ν.val_top, sub_self]

theorem boolean_like_of_em (ν : ModularValuation α) (a : α) (h : a ⊔ aᶜ = ⊤) :
    ν.val a + ν.val aᶜ = 1 := by
  calc ν.val a + ν.val aᶜ = ν.val (a ⊔ aᶜ) :=
         complementSum_eq_sup ν.toSumRuleValuation.toAdditive a
       _ = 1 := by rw [h, ν.val_top]
end ComplementObservation

section PreservesStructure
variable {α : Type*} [DistribLattice α] [BoundedOrder α]

omit [BoundedOrder α] in
theorem inf_eq_left_iff_le (a b : α) : a ⊓ b = a ↔ a ≤ b := inf_eq_left

omit [BoundedOrder α] in
theorem sup_eq_left_iff_ge (a b : α) : a ⊔ b = a ↔ b ≤ a := sup_eq_left

end PreservesStructure
end KnuthSkilling.Heyting
