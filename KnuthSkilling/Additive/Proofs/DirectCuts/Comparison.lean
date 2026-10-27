import KnuthSkilling.Additive.Proofs.GridInduction.Main
import KnuthSkilling.Additive.Proofs.DirectCuts.Main

namespace KnuthSkilling.Additive.Proofs.DirectCuts

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# Grid vs Cuts: Agreement up to Scale

This file proves that any two additive order embeddings `Θ : α → ℝ` satisfying the K&S
representation conclusion agree up to multiplication by a positive constant.

In particular, the `Θ` produced by the grid/induction globalization proof
(`Additive/Proofs/GridInduction/Main.lean`) and the `Θ` produced by the Dedekind-cuts proof
(`Additive/Proofs/DirectCuts/Main.lean`) coincide up to a positive scalar.

The key bridge is the characterization lemma in `DirectCuts.lean`:
`Θ_cuts_eq_div_of_representation`.
-/

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-!
## Any two representations differ by a positive scalar
-/

theorem representation_unique_up_to_posScale
    (a : α) (ha : ident < a)
    (Θ₁ Θ₂ : α → ℝ)
    (hΘ₁_order : ∀ u v : α, u ≤ v ↔ Θ₁ u ≤ Θ₁ v)
    (hΘ₁_ident : Θ₁ ident = 0)
    (hΘ₁_add : ∀ x y : α, Θ₁ (op x y) = Θ₁ x + Θ₁ y)
    (hΘ₂_order : ∀ u v : α, u ≤ v ↔ Θ₂ u ≤ Θ₂ v)
    (hΘ₂_ident : Θ₂ ident = 0)
    (hΘ₂_add : ∀ x y : α, Θ₂ (op x y) = Θ₂ x + Θ₂ y) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, Θ₂ x = c * Θ₁ x := by
  let r : NormalizedRepresentationResult α := ⟨⟨Θ₁, hΘ₁_order, hΘ₁_add⟩, hΘ₁_ident⟩
  let t : NormalizedRepresentationResult α := ⟨⟨Θ₂, hΘ₂_order, hΘ₂_add⟩, hΘ₂_ident⟩
  exact r.toRepresentationResult.unique_up_to_posScale t.toRepresentationResult a
    ((isPositive_iff_ident_lt a).mpr ha)

/-!
## Corollary: grid Θ and cuts Θ agree up to scale
-/

theorem associativity_representation_grid_and_cuts_agree_up_to_scale
    (α : Type*) [KnuthSkillingAlgebraBase α] [KSSeparationStrict α] :
    ∃ (Θ_grid Θ_cuts : α → ℝ) (c : ℝ),
      0 < c ∧
      (∀ u v : α, u ≤ v ↔ Θ_grid u ≤ Θ_grid v) ∧
      Θ_grid ident = 0 ∧
      (∀ x y : α, Θ_grid (op x y) = Θ_grid x + Θ_grid y) ∧
      (∀ u v : α, u ≤ v ↔ Θ_cuts u ≤ Θ_cuts v) ∧
      Θ_cuts ident = 0 ∧
      (∀ x y : α, Θ_cuts (op x y) = Θ_cuts x + Θ_cuts y) ∧
      (∀ x : α, Θ_cuts x = c * Θ_grid x) := by
  classical
  -- Trivial algebra: everything is ident.
  by_cases htriv : ∀ x : α, x = ident
  · refine ⟨(fun _ => 0), (fun _ => 0), 1, by norm_num, ?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
    · intro u v; simp [htriv u, htriv v]
    · intro x y; simp
    · intro u v; simp [htriv u, htriv v]
    · intro x y; simp
    · intro x; simp

  -- Nontrivial: pick any `a₀ > ident` to define the scaling constant.
  push Not at htriv
  obtain ⟨a₀, ha₀_ne⟩ := htriv
  have ha₀ : ident < a₀ := lt_of_le_of_ne (ident_le a₀) (Ne.symm ha₀_ne)

  -- Grid/the-mainline witness.
  obtain ⟨Θg, hΘg_order, hΘg_ident, hΘg_add⟩ :=
    KnuthSkilling.Additive.associativity_representation (α := α)

  -- Cuts witness.
  obtain ⟨Θc, hΘc_order, hΘc_ident, hΘc_add⟩ :=
    associativity_representation_cuts (α := α)

  -- Compare via `representation_unique_up_to_posScale`.
  rcases representation_unique_up_to_posScale (a := a₀) ha₀
      (Θ₁ := Θg) (Θ₂ := Θc)
      hΘg_order hΘg_ident hΘg_add
      hΘc_order hΘc_ident hΘc_add with
    ⟨c, hc_pos, hc_mul⟩

  refine ⟨Θg, Θc, c, hc_pos, hΘg_order, hΘg_ident, hΘg_add, hΘc_order, hΘc_ident, hΘc_add, ?_⟩
  intro x
  exact hc_mul x

end KnuthSkilling.Additive.Proofs.DirectCuts
