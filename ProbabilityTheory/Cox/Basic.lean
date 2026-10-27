import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Supplied plausibility and scalar-rule data

The records package conditional plausibility, conjunction and negation data.
Functional-equation results require the stronger hypotheses in
`ProductRuleDerivation`. Rule packaging alone does not construct an event model
or identify an arbitrary authored operation with ordinary multiplication.
-/

namespace ProbabilityTheory.Cox

/-- A plausibility function assigns real numbers to pairs of propositions.
    p A B represents the plausibility of A given B. -/
structure PlausibilityFunction (Prop' : Type*) where
  /-- The plausibility function p(A|B) -/
  p : Prop' → Prop' → ℝ
  /-- Plausibilities are in [0,1] -/
  p_nonneg : ∀ A B, 0 ≤ p A B
  p_le_one : ∀ A B, p A B ≤ 1

/-- The conjunction function F determines p(A ∧ B | C) from p(A|C) and p(B|A ∧ C).
    This is the key to Cox's theorem - what must F be? -/
structure ConjunctionRule where
  /-- The product function F(x,y) = p(A ∧ B | C) when p(A|C) = x and p(B|A ∧ C) = y -/
  F : ℝ → ℝ → ℝ
  /-- F preserves the unit interval -/
  F_range : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ F x y ∧ F x y ≤ 1
  /-- F is continuous (needed for functional equation analysis) -/
  F_continuous : Continuous (Function.uncurry F)
  /-- F(1,y) = y (certainty of A doesn't affect B) -/
  F_one_left : ∀ y, F 1 y = y
  /-- F(x,1) = x (certainty of B doesn't affect A) -/
  F_one_right : ∀ x, F x 1 = x
  /-- F(0,y) = 0 (conjunction with impossibility is impossible) -/
  F_zero_left : ∀ y, F 0 y = 0
  /-- F(x,0) = 0 (conjunction with impossibility is impossible) -/
  F_zero_right : ∀ x, F x 0 = 0

/-- The negation function G determines p(¬A | B) from p(A|B). -/
structure NegationRule where
  /-- The negation function G(x) = p(¬A | B) when p(A|B) = x -/
  G : ℝ → ℝ
  /-- G preserves the unit interval -/
  G_range : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ G x ∧ G x ≤ 1
  /-- G is continuous -/
  G_continuous : Continuous G
  /-- G is strictly decreasing (more plausible A means less plausible ¬A) -/
  G_strictAnti : StrictAnti G
  /-- G(0) = 1 (impossible A means certain ¬A) -/
  G_zero : G 0 = 1
  /-- G(1) = 0 (certain A means impossible ¬A) -/
  G_one : G 1 = 0

/-- The associativity equation that F must satisfy.
    This comes from the fact that (A ∧ B) ∧ C and A ∧ (B ∧ C) are the same. -/
def AssociativityEquation (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y z : ℝ, F (F x y) z = F x (F y z)

/-- Ordinary multiplication on the chosen probability scale. -/
def standardProductRule : ℝ → ℝ → ℝ := fun x y => x * y

/-- The standard negation rule. -/
def standardNegationRule : ℝ → ℝ := fun x => 1 - x

end ProbabilityTheory.Cox
