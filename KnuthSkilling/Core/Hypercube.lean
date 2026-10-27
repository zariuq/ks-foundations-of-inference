/-
# Labels for logic and observation choices

This two-axis vocabulary labels Boolean/Heyting logic and point/bounds readouts.
The labels alone supply neither models nor translations. In particular,
`plnEvidence` does not prove that evidence counts form a Heyting algebra.

For a supplied modular valuation, Boolean complement intervals are points;
Heyting complement intervals may have positive width. A zero numerical width
can also occur on a non-Boolean algebra when the valuation loses distinctions.
See `HeytingBounds` for the three-chain controls and interval interpretation.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.HeytingValuation
import KnuthSkilling.Core.HeytingBounds

namespace KnuthSkilling.Hypercube

open KnuthSkilling.Heyting

/-- The logic axis: Boolean vs Heyting algebra.
    The key difference is complement behavior. -/
inductive LogicAxis
  | boolean
  | heyting
  deriving DecidableEq, Repr

/-- The representation axis: point-valued vs bounds/2D-valued.
    Independent of the logic axis! -/
inductive RepresentationAxis
  | point
  | bounds
  deriving DecidableEq, Repr

/-- A pair of structural labels, without a model interpretation. -/
structure HypercubeVertex where
  logic : LogicAxis
  representation : RepresentationAxis
  deriving DecidableEq, Repr

/-- In Boolean algebras, the complement rule gives ν(a) + ν(¬a) = 1. -/
theorem boolean_complement_equality {α : Type*} [BooleanAlgebra α]
    (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ = 1 :=
  ModularValuation.boolean_complement_rule ν a

/-- In Heyting algebras, we only have ν(a) + ν(¬a) ≤ 1. -/
theorem heyting_complement_inequality {α : Type*} [HeytingAlgebra α]
    (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ ≤ 1 :=
  heyting_not_boolean_complement ν a

/-- The excluded middle gap measures how far a ⊔ ¬a is from ⊤.
    - Zero for Boolean algebras
    - Potentially positive for Heyting algebras -/
theorem boolean_em_gap_zero {α : Type*} [BooleanAlgebra α]
    (ν : ModularValuation α) (a : α) :
    excludedMiddleGap ν a = 0 := by
  exact excludedMiddleGap_eq_zero_of_em ν a sup_compl_eq_top

/-- In Heyting algebras, the gap is always non-negative. -/
theorem heyting_em_gap_nonneg {α : Type*} [HeytingAlgebra α]
    (ν : ModularValuation α) (a : α) :
    excludedMiddleGap ν a ≥ 0 :=
  excludedMiddleGap_nonneg ν a

/-- Standard Bayesian probability sits at the Boolean + Point vertex. -/
def classicalProbability : HypercubeVertex :=
  ⟨.boolean, .point⟩

/-- A vocabulary label for a Heyting/bounds interpretation of evidence. -/
def plnEvidence : HypercubeVertex :=
  ⟨.heyting, .bounds⟩

/-- Imprecise probability on Boolean events uses Boolean + Bounds. -/
def impreciseProbability : HypercubeVertex :=
  ⟨.boolean, .bounds⟩

/-- K&S on Heyting algebras with point valuations. -/
def heytingPointKS : HypercubeVertex :=
  ⟨.heyting, .point⟩

/-- The Heyting bounds width equals the excluded middle gap. -/
theorem heyting_bounds_width_eq_em_gap {α : Type*} [HeytingAlgebra α]
    (ν : ModularValuation α) (a : α) :
    heytingWidth ν a = excludedMiddleGap ν a :=
  heytingWidth_eq_em_gap ν a

/-- Boolean algebras have zero width (points). -/
theorem boolean_bounds_collapse {α : Type*} [BooleanAlgebra α]
    (ν : ModularValuation α) (a : α) :
    upperBound ν a = lowerBound ν a :=
  boolean_collapse ν a

end KnuthSkilling.Hypercube
