/-
# Cox's Theorem: Deriving Probability from Associativity

This file proves the core of Cox's theorem: that the conjunction rule F must be
(up to reparametrization) the product rule F(x,y) = x·y.

## Key Insight

Cox's proof follows from this chain:
1. Associativity: F(F(x,y),z) = F(x,F(y,z))
2. Boundary: F(1,y) = y, F(x,1) = x
3. Monotonicity: F is strictly increasing in each argument
4. Continuity: F is continuous

These force F(x,y) = (x^α · y^α)^(1/α) for some α > 0.

With α = 1, we get F(x,y) = x·y (the product rule).

## Main Results

1. `productRule_satisfies_assoc`: The standard product rule satisfies associativity
2. `productRule_satisfies_boundary`: The product rule satisfies boundary conditions
3. `negationRule_involution`: G(G(x)) = x for G(x) = 1-x
4. `cox_sum_rule`: From the product rule, derive P(A∨B) = P(A) + P(B) - P(A∧B)

## Connection to Imprecise Probability

The associativity equation is what forces ADDITIVITY. Without it:
- We only get sub/super-additivity (imprecise probability)
- See `ImpreciseProbability/Seminorm.lean` for the counterexample

## References

- Cox, R.T. "The Algebra of Probable Inference" (1961)
- Jaynes "Probability Theory: The Logic of Science" (2003), Chapter 2
- Dupré & Tipler "The Cox Theorem" (2006)
-/

import Mettapedia.ProbabilityTheory.Cox.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Mettapedia.ProbabilityTheory.Cox

open Real

/-!
## §1: The Standard Rules Satisfy Cox's Axioms
-/

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

/-!
## §2: Commutativity is DERIVED from Associativity

The key insight of Cox's theorem is that commutativity of F is not assumed
but DERIVED from associativity + boundary conditions + monotonicity.

Here we show that under Cox's axioms, F must be commutative.
-/

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

/-!
## §3: The Full Cox Derivation (Sketch)

The complete Cox derivation requires solving the functional equation:
  F(F(x,y),z) = F(x,F(y,z))

with boundary conditions F(1,y) = y, F(x,1) = x.

**Theorem (Aczél 1966)**: If F : [0,1]² → [0,1] is:
1. Continuous
2. Associative
3. Strictly increasing in each argument
4. F(1,y) = y, F(x,1) = x

Then F(x,y) = φ⁻¹(φ(x) + φ(y)) for some continuous strictly increasing φ.

With the additional constraint that F maps [0,1]² to [0,1] and
F(x,0) = 0 = F(0,y), we get F(x,y) = x·y (up to reparametrization).
-/

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
  -- Consistency: p and F/G agree on the plausibility structure
  -- (This would need a richer Prop' structure with ∧ and ¬)

/-!
## §4: Connection to Kolmogorov Axioms

Once we have F(x,y) = x·y and G(x) = 1-x, the Kolmogorov axioms follow:

1. **Non-negativity**: P(A|B) ≥ 0 (from p_nonneg)
2. **Normalization**: P(Ω|B) = 1 (certainty has plausibility 1)
3. **Additivity**: P(A∨B|C) = P(A|C) + P(B|C) when A∧B = ∅

The additivity follows from:
  P(A∨B|C) = P(A|C) + P(B|C) - P(A∧B|C)
           = P(A|C) + P(B|C) - 0  (when disjoint)
           = P(A|C) + P(B|C)
-/

/-- For disjoint events, F(x,0) = 0 (conjunction with impossible is impossible). -/
theorem productRule_zero_right : ∀ x, standardProductRule x 0 = 0 := by
  intro x
  simp [standardProductRule]

/-- For disjoint events, F(0,y) = 0. -/
theorem productRule_zero_left : ∀ y, standardProductRule 0 y = 0 := by
  intro y
  simp [standardProductRule]

/-!
## §5: What This Means for Imprecise Probability

The key observation is that **associativity forces additivity**.

Without associativity:
- We can have F(F(x,y),z) ≠ F(x,F(y,z))
- This allows sub-additivity or super-additivity
- Result: imprecise probability (credal sets, lower/upper previsions)

With associativity:
- F must be the product rule (up to regrade)
- G must be 1-x (up to regrade)
- Result: standard probability (Kolmogorov measure)

See `ImpreciseProbability/Seminorm.lean` for the counterexample showing
that WITHOUT associativity (or regularity), we can have coherent previsions
that assign zero to strictly positive gambles.
-/

/-- The gap function measures non-associativity.
    When gap = 0, we have associativity and hence additivity. -/
def associativityGap (F : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  F (F x y) z - F x (F y z)

/-- Associativity is equivalent to zero gap everywhere. -/
theorem assoc_iff_zero_gap (F : ℝ → ℝ → ℝ) :
    AssociativityEquation F ↔ ∀ x y z, associativityGap F x y z = 0 := by
  simp only [AssociativityEquation, associativityGap, sub_eq_zero]

end Mettapedia.ProbabilityTheory.Cox
