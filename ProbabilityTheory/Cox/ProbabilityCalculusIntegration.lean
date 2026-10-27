import KnuthSkilling.Probability.ProbabilityCalculus

/-!
# Finite additivity of a supplied regraded event model

A compatible event model supplies product and complement laws on one scale.
These laws imply disjoint finite additivity and the common probability-calculus
interface. No construction of this model from an arbitrary scalar generator is
asserted here.
-/

namespace ProbabilityTheory.Cox

open KnuthSkilling

structure CoxProbabilityModel (α : Type*)
    [PlausibilitySpace α] [ComplementedLattice α] where
  /-- Regraded plausibility `P(A|C)` on events. -/
  P : α → α → ℝ
  /-- Range: nonnegative. -/
  P_nonneg : ∀ a c, 0 ≤ P a c
  /-- Range: ≤ 1. -/
  P_le_one : ∀ a c, P a c ≤ 1
  /-- Normalization: P(⊤|C) = 1. -/
  P_top : ∀ c, P ⊤ c = 1
  /-- Normalization: P(⊥|C) = 0. -/
  P_bot : ∀ c, P ⊥ c = 0
  /-- Unconditional monotonicity. -/
  P_mono_uncond : ∀ {a b}, a ≤ b → P a ⊤ ≤ P b ⊤
  /-- Product rule (regraded): P(A∧B|C) = P(A|C)·P(B|A∧C). -/
  product_rule : ∀ a b c, P (a ⊓ b) c = P a c * P b (a ⊓ c)
  /-- Chosen complement operation (for Cox’s ¬A). -/
  compl : α → α
  /-- The chosen complement is indeed a complement. -/
  compl_isCompl : ∀ a, IsCompl a (compl a)
  /-- Complement rule (regraded): P(¬A|C) = 1 - P(A|C). -/
  complement_rule : ∀ a c, P (compl a) c = 1 - P a c

namespace CoxProbabilityModel

variable {α : Type*} [PlausibilitySpace α] [ComplementedLattice α]

noncomputable def valuation (M : CoxProbabilityModel α) : Valuation α where
  val := fun a => M.P a ⊤
  monotone := by
    intro a b hab
    exact M.P_mono_uncond hab
  val_bot := by simpa using (M.P_bot ⊤)
  val_top := by simpa using (M.P_top ⊤)

theorem sum_rule_disjoint (M : CoxProbabilityModel α) {a b : α} (h : Disjoint a b) :
    (M.valuation).val (a ⊔ b) = (M.valuation).val a + (M.valuation).val b := by
  have hleft := M.product_rule (a ⊔ b) a ⊤
  have hright := M.product_rule (a ⊔ b) (M.compl a) ⊤
  have hle : b ≤ M.compl a := (IsCompl.le_right_iff (M.compl_isCompl a)).mpr h.symm
  have hsplit : (a ⊔ b) ⊓ M.compl a = b := by
    rw [inf_sup_right, (M.compl_isCompl a).inf_eq_bot, bot_sup_eq, inf_eq_left.mpr hle]
  simp at hleft
  simp only [inf_top_eq, hsplit] at hright
  rw [M.complement_rule] at hright
  change M.P (a ⊔ b) ⊤ = M.P a ⊤ + M.P b ⊤
  nlinarith

instance (M : CoxProbabilityModel α) :
    KnuthSkilling.Probability.ProbabilityCalculus.ProbabilityCalculusClass α
      M.valuation where
  sum_rule' := fun {a b} h => M.sum_rule_disjoint h
  complement_rule' := by
    intro a b h_disj h_top
    have hsum := M.sum_rule_disjoint h_disj
    have htop : (M.valuation).val (a ⊔ b) = 1 := by
      simpa [valuation, h_top] using (M.P_top ⊤)
    linarith

end CoxProbabilityModel

end ProbabilityTheory.Cox
