/-
# Ordinary probability rules and lightweight Cox bundles

The concrete product and complement satisfy the displayed identities. General
conjunction generators are constructed in `ProductRuleDerivation`; associativity
alone does not supply additivity, normalization or imprecise-probability semantics.
`associativityGap` observes a single triple of the supplied operation.
-/

import ProbabilityTheory.Cox.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProbabilityTheory.Cox

open Real

/-- The product rule is associative. -/
theorem productRule_assoc : AssociativityEquation standardProductRule := by
  intro x y z
  simp only [standardProductRule]
  ring

/-- The product rule satisfies F(1,y) = y. -/
theorem productRule_one_left : ∀ y, standardProductRule 1 y = y := by
  intro y
  simp [standardProductRule]

/-- The product rule satisfies F(x,1) = x. -/
theorem productRule_one_right : ∀ x, standardProductRule x 1 = x := by
  intro x
  simp [standardProductRule]

/-- The product rule is commutative. -/
theorem productRule_comm : ∀ x y, standardProductRule x y = standardProductRule y x := by
  intro x y
  simp only [standardProductRule]
  ring

/-- The negation rule is an involution: G(G(x)) = x. -/
theorem negationRule_involution : ∀ x, standardNegationRule (standardNegationRule x) = x := by
  intro x
  simp only [standardNegationRule]
  ring

/-- The negation rule satisfies G(0) = 1. -/
theorem negationRule_zero : standardNegationRule 0 = 1 := by
  simp [standardNegationRule]

/-- The negation rule satisfies G(1) = 0. -/
theorem negationRule_one : standardNegationRule 1 = 0 := by
  simp [standardNegationRule]

/-- G and F together satisfy the sum rule:
    F(x, G(y)) + F(x, y) = x  (i.e., P(A∧¬B|C) + P(A∧B|C) = P(A|C))
    when F is product and G is 1-x. -/
theorem sum_rule_from_product_negation (x y : ℝ) :
    standardProductRule x (standardNegationRule y) +
    standardProductRule x y = x := by
  simp only [standardProductRule, standardNegationRule]
  ring

/-- A ConjunctionRule with associativity equation. -/
structure AssociativeConjunction extends ConjunctionRule where
  /-- F satisfies the associativity equation -/
  assoc : AssociativityEquation F

/-- Key lemma: If F has the zero axioms (F(0,y) = 0 and F(x,0) = 0),
    then F(x,0) = F(0,x) for all x.

    This follows immediately from the zero axioms: both sides equal 0. -/
lemma assoc_conj_zero_comm (C : AssociativeConjunction) (x : ℝ) :
    C.F x 0 = C.F 0 x := by
  rw [C.F_zero_right, C.F_zero_left]

/-- The Cox axioms as a complete package. -/
structure CoxAxioms (Prop' : Type*) extends PlausibilityFunction Prop' where
  /-- The conjunction rule -/
  conjunction : ConjunctionRule
  /-- The negation rule -/
  negation : NegationRule
  /-- F satisfies associativity -/
  F_assoc : AssociativityEquation conjunction.F
  /-- G is an involution: G(G(x)) = x -/
  G_involution : ∀ x, negation.G (negation.G x) = x

/-- For disjoint events, F(x,0) = 0 (conjunction with impossible is impossible). -/
theorem productRule_zero_right : ∀ x, standardProductRule x 0 = 0 := by
  intro x
  simp [standardProductRule]

/-- For disjoint events, F(0,y) = 0. -/
theorem productRule_zero_left : ∀ y, standardProductRule 0 y = 0 := by
  intro y
  simp [standardProductRule]

/-- Associativity defect at one supplied triple. -/
def associativityGap (F : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  F (F x y) z - F x (F y z)

/-- Associativity is equivalent to zero gap everywhere. -/
theorem assoc_iff_zero_gap (F : ℝ → ℝ → ℝ) :
    AssociativityEquation F ↔ ∀ x y z, associativityGap F x y z = 0 := by
  simp only [AssociativityEquation, associativityGap, sub_eq_zero]

end ProbabilityTheory.Cox
