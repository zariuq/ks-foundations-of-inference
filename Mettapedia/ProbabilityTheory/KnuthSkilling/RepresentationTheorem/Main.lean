import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Globalization

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# K&S Representation Theorem: Main Theorem (Public API)

This file is intentionally short: it exposes the representation theorem statement and the main
corollary (commutativity), assuming the globalization class.

For the globalization construction itself (the “triple family trick”), see:
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Globalization.lean`.

Paper cross-reference:
- `paper/ks-formalization.tex`, Subsection “The Representation Theorem” (inside Section `sec:main`).
- Background statement “KS Representation” (label `thm:ks-main`).
- Section “Commutativity from Separation” (label `sec:commutativity`) for the separation ⇒ commutativity story.
-/

/-- **K&S Appendix A main theorem**: existence of an order embedding `Θ : α → ℝ` turning `op` into `+`.

Lean architecture note:
- In the paper, the theorem is presented as a single statement about `KnuthSkillingAlgebra` +
  separation assumptions.
- In Lean, the substantive Appendix A induction is packaged as the typeclass
  `RepresentationGlobalization`, and this theorem simply exposes the `exists_Theta` field as the public
  API. -/
theorem associativity_representation
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  exact RepresentationGlobalization.exists_Theta (α := α)

/-- Convenience wrapper: with `[KSSeparation α]` and dense order, the globalization instance is
automatic, so the representation theorem can be used without mentioning `RepresentationGlobalization`. -/
theorem associativity_representation_of_KSSeparation_of_denselyOrdered
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [DenselyOrdered α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  -- `KSSeparation` upgrades to `KSSeparationStrict` under density, which provides globalization.
  exact associativity_representation (α := α)

/-- Convenience wrapper: a weaker “density above `ident`” hypothesis also suffices to upgrade
`KSSeparation` to `KSSeparationStrict`, and thus obtain the representation theorem. -/
theorem associativity_representation_of_KSSeparation_of_exists_between_pos
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α]
    (hBetween : ∀ {x y : α}, ident < x → x < y → ∃ z, x < z ∧ z < y) :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  letI : KSSeparationStrict α :=
    KSSeparation.toKSSeparationStrict_of_exists_between_pos (α := α) (hBetween := hBetween)
  exact associativity_representation (α := α)

/-- Commutativity as a corollary of the representation theorem. -/
theorem op_comm_of_associativity
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α] :
    ∀ x y : α, op x y = op y x := by
  classical
  obtain ⟨Θ, hΘ_order, _, hΘ_add⟩ := associativity_representation (α := α)
  exact commutativity_from_representation Θ hΘ_order hΘ_add

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
