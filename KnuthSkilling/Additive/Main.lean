import KnuthSkilling.Core.Algebra
import KnuthSkilling.Additive.Representation
import KnuthSkilling.Additive.Proofs.DirectCuts.Main
import KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.Main

/-!
This module is the public entry point for the Knuth–Skilling (Appendix A) *representation theorem*.

## Primary Assumption: NoAnomalousPairs (NAP)

The **canonical proof path** uses `NoAnomalousPairs` from the 1950s ordered-semigroup literature
(Alimov 1950, Fuchs 1963), implemented via Eric Luap's OrderedSemigroups library.

**Why NAP is primary**:
- Historical precedent: NAP (1950s) predates K&S's `KSSeparation` (2012) by 60+ years
- Identity-free: NAP is defined on semigroups; `KSSeparation` requires identity
- The relationship: `KSSeparation + IdentIsMinimum ⇒ NoAnomalousPairs` (proven)

## Design note (keep the API light)

The grid/induction proof path (`...Additive/Proofs/GridInduction/Main.lean`) is large and may be expensive to
compile. This entrypoint therefore exposes a small, proof-agnostic interface
`HasRepresentationTheorem` whose instances can be provided by different proof paths.

Proof paths (in order of precedence):
1. **Hölder/Alimov** (`...Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean`):
   assumes `NoAnomalousPairs` — **CANONICAL**
2. **Dedekind cuts** (`...Additive/Proofs/DirectCuts/Main.lean`):
   assumes `KSSeparationStrict` — alternative

For the full "three-path" comparison (including the grid/induction instance), import:
`KnuthSkilling.Additive.Proofs.GridInduction.Comparison`.
-/

namespace KnuthSkilling.Additive

open Classical
open KSSemigroupBase
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open KnuthSkilling.Additive.Axioms.AnomalousPairs
open KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

/-- Hölder proof path: `NoAnomalousPairs` gives a representation via `OrderedSemigroups`. -/
instance holder_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [NoAnomalousPairs α] :
    HasRepresentationTheorem α where
  exists_representation := representation_semigroup (α := α)

/-- Cuts proof path: Dedekind cuts on the `KSSeparationStrict` grid. -/
instance cuts_hasRepresentationTheorem
    (α : Type*) [KnuthSkillingAlgebraBase α] [KSSeparationStrict α] :
    HasRepresentationTheorem α where
  exists_representation := by
    obtain ⟨Θ, hΘ_order, _hΘ_ident, hΘ_add⟩ :=
      KnuthSkilling.Additive.Proofs.DirectCuts.associativity_representation_cuts (α := α)
    exact ⟨Θ, hΘ_order, hΘ_add⟩

/-- Commutativity follows from any additive order representation. -/
theorem op_comm_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∀ x y : α, op x y = op y x := by
  obtain ⟨Θ, ho, ha⟩ := HasRepresentationTheorem.exists_representation (α := α)
  exact (RepresentationResult.mk Θ ho ha).op_comm

end KnuthSkilling.Additive
