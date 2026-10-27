/-
# Separation consequences and a sufficient representation hypothesis

Sandwich separation yields commutativity and Archimedean consequences under
the stated monoid/algebra premises. Conversely an additive order isomorphism
onto the reals gives the positive sandwich by rational density. The latter
hypothesis is stronger than an additive embedding; this file does not assert
an equivalence with every weaker representation interface.
-/

import KnuthSkilling.Additive.Axioms.SandwichSeparation
import KnuthSkilling.Literature.FunctionalEquations

namespace KnuthSkilling

open Classical

namespace AxiomSystemEquivalence

open KnuthSkillingMonoidBase
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation

/-- `KSSeparation` gives an Archimedean-style bound: `x < a^n` for some `n`. -/
theorem archimedean_of_ksSeparation
    {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparation α]
    (a x : α) (ha : ident < a) :
    ∃ n : ℕ, x < Nat.iterate (op a) n a :=
  SandwichSeparation.SeparationToArchimedean.op_archimedean_of_separation (α := α) a x ha

/-- `KSSeparation` forces commutativity on the positive cone. -/
theorem comm_pos_of_ksSeparation
    {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparation α]
    (x y : α) (hx : ident < x) (hy : ident < y) :
    op x y = op y x :=
  SandwichSeparation.ThetaAdditivity.ksSeparation_implies_comm (α := α) x y hx hy

/-- `KSSeparation` forces global commutativity of `op`. -/
theorem comm_of_ksSeparation
    {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α] (x y : α) :
    op x y = op y x :=
  SandwichSeparation.ksSeparation_implies_commutative (α := α) x y

/-- The separation property holds in (ℝ, +) due to rational density.

For any a, x, y > 0 with x < y, there exist n, m ∈ ℕ⁺ such that m·x < n·a ≤ m·y.

Proof idea: Choose m large enough that m·(y - x) > a, then find n with m·x < n·a ≤ m·y. -/
theorem real_separation (a x y : ℝ) (ha : 0 < a) (_hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧ (m : ℝ) * x < (n : ℝ) * a ∧ (n : ℝ) * a ≤ (m : ℝ) * y := by
  have hgap : 0 < y - x := sub_pos.mpr hxy
  obtain ⟨m, hm⟩ := exists_nat_gt (a / (y - x))
  have hm_pos : 0 < m := by
    exact_mod_cast lt_trans (div_pos ha hgap) hm
  have hwide : a < (m : ℝ) * (y - x) := (div_lt_iff₀ hgap).mp hm
  let n := Nat.floor ((m : ℝ) * y / a)
  have hu : (n : ℝ) * a ≤ (m : ℝ) * y :=
    (le_div_iff₀ ha).mp (Nat.floor_le (by positivity))
  have hl : (m : ℝ) * y < ((n : ℝ) + 1) * a :=
    (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one _)
  exact ⟨n, m, hm_pos, by nlinarith, hu⟩

/-- An additive order isomorphism implies the separation sandwich.

If Θ : α ≃o ℝ is an order isomorphism with Θ(x ⊕ y) = Θ(x) + Θ(y), then the separation sandwich holds.
This is because the separation property holds in ℝ (rational density). -/
theorem ksSeparation_of_additiveOrderIsoRep
    {α : Type*} [LinearOrder α] {op : α → α → α}
    (h : Literature.AdditiveOrderIsoRep α op)
    (ident : α)
    (h_ident_zero : h.Θ ident = 0)
    (iterate_op : α → ℕ → α)
    (h_iterate_zero : ∀ x, iterate_op x 0 = ident)
    (h_iterate_succ : ∀ x n, iterate_op x (n + 1) = op x (iterate_op x n)) :
    ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
      ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  intro a x y ha hx hy hxy
  have ha' : 0 < h.Θ a := by
    calc 0 = h.Θ ident := h_ident_zero.symm
      _ < h.Θ a := h.Θ.strictMono ha
  have hx' : 0 < h.Θ x := by
    calc 0 = h.Θ ident := h_ident_zero.symm
      _ < h.Θ x := h.Θ.strictMono hx
  have hy' : 0 < h.Θ y := by
    calc 0 = h.Θ ident := h_ident_zero.symm
      _ < h.Θ y := h.Θ.strictMono hy
  have hxy' : h.Θ x < h.Θ y := h.Θ.strictMono hxy
  have h_iterate_Theta : ∀ z : α, ∀ k : ℕ, h.Θ (iterate_op z k) = k * h.Θ z := by
    intro z k
    induction k with
    | zero => simp [h_iterate_zero, h_ident_zero]
    | succ n ih =>
      rw [h_iterate_succ, h.map_op, ih]
      simp only [Nat.cast_succ]
      ring
  obtain ⟨n, m, hm_pos, h_lower, h_upper⟩ := real_separation (h.Θ a) (h.Θ x) (h.Θ y) ha' hx' hy' hxy'
  refine ⟨n, m, hm_pos, ?_, ?_⟩
  ·
    apply h.Θ.lt_iff_lt.mp
    simp only [h_iterate_Theta]
    exact h_lower
  ·
    apply h.Θ.le_iff_le.mp
    simp only [h_iterate_Theta]
    exact h_upper

end AxiomSystemEquivalence

end KnuthSkilling
