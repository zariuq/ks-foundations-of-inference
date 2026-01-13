import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.SandwichSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# `KSSeparation` implies commutativity

This file is a thin bridge that re-exports the main result from
`Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.SandwichSeparation` in a stable
“Core API” location.

Paper cross-reference:
- `paper/ks-formalization.tex`, Section “Commutativity from Separation” (label `sec:commutativity`).
- Theorem “Separation Implies Commutativity” (label `thm:sep-comm`).
-/

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-- Proposition packaging global commutativity for `op`. -/
def SeparationImpliesCommutative : Prop :=
  ∀ x y : α, op x y = op y x

/-!
## Theorem: `KSSeparation` forces commutativity
-/

theorem separationImpliesCommutative_of_KSSeparation [KSSeparation α] :
    SeparationImpliesCommutative (α := α) := by
  simpa [SeparationImpliesCommutative] using
    (Mettapedia.ProbabilityTheory.KnuthSkilling.SandwichSeparation.ksSeparation_implies_commutative (α := α))

/-- Convenience lemma: under `KSSeparation`, `op` commutes.

Paper cross-reference:
- `paper/ks-formalization.tex`, Theorem “Separation Implies Commutativity” (label `thm:sep-comm`). -/
theorem op_comm_of_KSSeparation [KSSeparation α] (x y : α) : op x y = op y x :=
  separationImpliesCommutative_of_KSSeparation (α := α) x y

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core
