import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Alternative.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding

/-!
This module is the public entry point for the Knuth–Skilling (Appendix A) *representation theorem*.

## Design note (keep the API light)

The grid/induction proof path (`...RepresentationTheorem/Main.lean`) is large and may be expensive to
compile. This entrypoint therefore exposes a small, proof-agnostic interface
`HasRepresentationTheorem` whose instances can be provided by different proof paths.

Included here (lightweight):
- Hölder embedding (`...Separation.HolderEmbedding`): assumes `NoAnomalousPairs`.
- Dedekind cuts (`...RepresentationTheorem.Alternative.Main`): assumes `KSSeparationStrict`.

For the full “three-path” comparison (including the grid/induction instance), import:
`Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Comparison`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs
open Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding

/-- Proof-agnostic interface for the Appendix A representation theorem. -/
class HasRepresentationTheorem (α : Type*) [KnuthSkillingAlgebraBase α] : Prop where
  exists_representation :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- Hölder proof path: `NoAnomalousPairs` gives a representation via `OrderedSemigroups`. -/
instance holder_hasRepresentationTheorem
    (α : Type*) [KnuthSkillingAlgebraBase α] [NoAnomalousPairs α] :
    HasRepresentationTheorem α where
  exists_representation := representation_from_noAnomalousPairs (α := α)

/-- Cuts proof path: Dedekind cuts on the `KSSeparationStrict` grid. -/
instance cuts_hasRepresentationTheorem
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [KSSeparationStrict α] :
    HasRepresentationTheorem α where
  exists_representation := Alternative.associativity_representation_cuts α

/-- Unified entry point: any instantiation of `HasRepresentationTheorem α` yields a K&S additive
order representation `Θ : α → ℝ`. -/
theorem exists_Theta_of_hasRepresentationTheorem
    (α : Type*) [KnuthSkillingAlgebraBase α] [HasRepresentationTheorem α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  simpa using (HasRepresentationTheorem.exists_representation (α := α))

/-- Commutativity follows from any additive order representation. -/
theorem op_comm_of_hasRepresentationTheorem
    (α : Type*) [KnuthSkillingAlgebraBase α] [HasRepresentationTheorem α] :
    ∀ x y : α, op x y = op y x := by
  obtain ⟨Θ, hΘ_order, _, hΘ_add⟩ := HasRepresentationTheorem.exists_representation (α := α)
  intro x y
  have h1 : Θ (op x y) = Θ x + Θ y := hΘ_add x y
  have h2 : Θ (op y x) = Θ y + Θ x := hΘ_add y x
  have h3 : Θ x + Θ y = Θ y + Θ x := add_comm (Θ x) (Θ y)
  have h4 : Θ (op x y) = Θ (op y x) := by rw [h1, h2, h3]
  have hΘ_inj : Function.Injective Θ := by
    intro a b hab
    have ha : a ≤ b := (hΘ_order a b).mpr (le_of_eq hab)
    have hb : b ≤ a := (hΘ_order b a).mpr (le_of_eq hab.symm)
    exact le_antisymm ha hb
  exact hΘ_inj h4

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

