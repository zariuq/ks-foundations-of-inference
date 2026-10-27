import KnuthSkilling.Probability.ProbabilityDerivation
import KnuthSkilling.Multiplicative.DirectProduct
import Mathlib.Data.Set.Card

/-!
# Distributivity at attained event values

Normalized valuations are bounded by one. Global preimages of every positive
real are therefore impossible. Actual disjoint events and rectangle-compatible
valuations instead give a distributivity equation at their attained values.
The finite example uses distinct masses one third and two thirds and a half-mass
right event; it does not extrapolate this equation to all positive scalars.
-/

namespace KnuthSkilling.Multiplicative
open KnuthSkilling

/-- A global preimage condition, incompatible with a normalized valuation. -/
def HasDisjointPreimages {α : Type*} [PlausibilitySpace α] (v : Valuation α) : Prop :=
  ∀ x y : PosReal, ∃ a₁ a₂ : α,
    Disjoint a₁ a₂ ∧ v.val a₁ = (x : ℝ) ∧ v.val a₂ = (y : ℝ) ∧
      0 < v.val a₁ ∧ 0 < v.val a₂

/-- Surjectivity onto every positive real is a boundary condition, not a probability model. -/
def ValuationSurjective {α : Type*} [PlausibilitySpace α] (v : Valuation α) : Prop :=
  ∀ t : PosReal, ∃ a : α, v.val a = (t : ℝ) ∧ 0 < v.val a

/-- Both historical global-preimage conditions fail already at the value two. -/
theorem normalized_global_preimages_impossible {α : Type*} [PlausibilitySpace α]
    (v : Valuation α) : ¬ValuationSurjective v ∧ ¬HasDisjointPreimages v := by
  constructor
  · intro h
    obtain ⟨a, ha, _⟩ := h ⟨2, by norm_num⟩
    have := v.le_one a
    norm_num at ha
    linarith
  · intro h
    obtain ⟨a, _, _, ha, _, _, _⟩ := h ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
    have := v.le_one a
    norm_num at ha
    linarith

/-- Actual preimages transport disjoint event additivity to one scalar equation. -/
theorem distributes_over_add_from_lattice
    {α β γ : Type*} [PlausibilitySpace α] [PlausibilitySpace β] [PlausibilitySpace γ]
    (P : DirectProduct α β γ) (vα : Valuation α) (vβ : Valuation β) (vγ : Valuation γ)
    (hAddα : ∀ {a b}, Disjoint a b → vα.val (a ⊔ b) = vα.val a + vα.val b)
    (hAddγ : ∀ {a b}, Disjoint a b → vγ.val (a ⊔ b) = vγ.val a + vγ.val b)
    {tensor : PosReal → PosReal → PosReal}
    (hCompat : KnuthSkilling.Probability.AppendixB.RectTensorCompatible P vα vβ vγ tensor)
    (x y t : PosReal)
    (hDisjoint : ∃ a₁ a₂, Disjoint a₁ a₂ ∧ vα.val a₁ = (x : ℝ) ∧ vα.val a₂ = (y : ℝ))
    (hAttained : ∃ b, vβ.val b = (t : ℝ)) :
    tensor (addPos x y) t = addPos (tensor x t) (tensor y t) := by
  obtain ⟨a₁, a₂, hd, hx, hy⟩ := hDisjoint
  obtain ⟨b, ht⟩ := hAttained
  have ha₁ : 0 < vα.val a₁ := hx.symm ▸ x.2
  have ha₂ : 0 < vα.val a₂ := hy.symm ▸ y.2
  have hb : 0 < vβ.val b := ht.symm ▸ t.2
  have hs := hAddα hd
  have hsup : 0 < vα.val (a₁ ⊔ a₂) := by rw [hs]; exact add_pos ha₁ ha₂
  have xeq : (⟨vα.val a₁, ha₁⟩ : PosReal) = x := Subtype.ext hx
  have yeq : (⟨vα.val a₂, ha₂⟩ : PosReal) = y := Subtype.ext hy
  have teq : (⟨vβ.val b, hb⟩ : PosReal) = t := Subtype.ext ht
  have sum_eq : (⟨vα.val (a₁ ⊔ a₂), hsup⟩ : PosReal) = addPos x y :=
    Subtype.ext (by simpa only [coe_addPos, hx, hy] using hs)
  apply Subtype.ext
  change (tensor (addPos x y) t : ℝ) = (tensor x t : ℝ) + (tensor y t : ℝ)
  calc
    _ = vγ.val (P.prod (a₁ ⊔ a₂) b) := by
      simpa only [sum_eq, teq] using (hCompat (a₁ ⊔ a₂) b hsup hb).symm
    _ = vγ.val (P.prod a₁ b) + vγ.val (P.prod a₂ b) := by
      rw [P.prod_sup_left, hAddγ (P.disjoint_prod_left hd)]
    _ = _ := by rw [hCompat a₁ b ha₁ hb, hCompat a₂ b ha₂ hb, xeq, yeq, teq]

private noncomputable def uniformValuation (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    Valuation (Set Ω) where
  val A := (A.ncard : ℝ) / Fintype.card Ω
  monotone := by
    intro A B h
    exact div_le_div_of_nonneg_right (by exact_mod_cast Set.ncard_mono h) (Nat.cast_nonneg _)
  val_bot := by simp
  val_top := by simp [Nat.card_eq_fintype_card, Fintype.card_ne_zero]

private theorem uniform_add {Ω : Type*} [Fintype Ω] [Nonempty Ω] {A B : Set Ω}
    (h : Disjoint A B) :
    (uniformValuation Ω).val (A ⊔ B) =
      (uniformValuation Ω).val A + (uniformValuation Ω).val B := by
  change ((A ∪ B).ncard : ℝ) / _ = _
  rw [Set.ncard_union_eq h, Nat.cast_add, add_div]
  rfl

private theorem uniform_rect (Ω Λ : Type*) [Fintype Ω] [Nonempty Ω]
    [Fintype Λ] [Nonempty Λ] :
    KnuthSkilling.Probability.AppendixB.RectTensorCompatible (SetModel.setDirectProduct Ω Λ)
      (uniformValuation Ω) (uniformValuation Λ) (uniformValuation (Ω × Λ)) mulPos := by
  intro A B hA hB
  change ((A ×ˢ B).ncard : ℝ) / Fintype.card (Ω × Λ) =
    ((A.ncard : ℝ) / Fintype.card Ω) * ((B.ncard : ℝ) / Fintype.card Λ)
  rw [Set.ncard_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

namespace FiniteExample
private def A : Set (Fin 3) := {0}
private def B : Set (Fin 3) := {1, 2}
private def T : Set Bool := {true}
private noncomputable def left := uniformValuation (Fin 3)
private noncomputable def right := uniformValuation Bool

/-- Independent finite counting gives the three attained values used below. -/
theorem attained_values : left.val A = 1 / 3 ∧ left.val B = 2 / 3 ∧ right.val T = 1 / 2 ∧
    left.val A ≠ left.val B := by
  have hA : A.ncard = 1 := by simp [A]
  have hB : B.ncard = 2 := by simp [B, show (1 : Fin 3) ≠ 2 by decide]
  have hT : T.ncard = 1 := by simp [T]
  norm_num [left, right, uniformValuation, hA, hB, hT]

/-- The finite event model instantiates the attained-value bridge. -/
theorem distributivity :
    mulPos (addPos ⟨1 / 3, by norm_num⟩ ⟨2 / 3, by norm_num⟩) ⟨1 / 2, by norm_num⟩ =
      addPos (mulPos ⟨1 / 3, by norm_num⟩ ⟨1 / 2, by norm_num⟩)
        (mulPos ⟨2 / 3, by norm_num⟩ ⟨1 / 2, by norm_num⟩) := by
  apply distributes_over_add_from_lattice (SetModel.setDirectProduct (Fin 3) Bool)
    left right (uniformValuation (Fin 3 × Bool)) uniform_add uniform_add (uniform_rect _ _)
  · refine ⟨A, B, ?_, attained_values.1, attained_values.2.1⟩
    simp [A, B]
  · exact ⟨T, attained_values.2.2.1⟩
end FiniteExample
end KnuthSkilling.Multiplicative
