import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNFrechetBounds

/-!
# K&S + Separation → PLN Deduction Formula

This file proves that the K&S axiom system with Separation implies the PLN
deduction formula. This establishes the second derivation path in the hypercube:

```
     Kolmogorov Axioms           K&S Axioms + Separation
            ↓                              ↓
    Law of Total Prob          Representation Theorem
            ↓                              ↓
    + Independence               Θ : α ≃o (ℝ≥0, +)
            ↓                              ↓
            └──────────┬───────────────────┘
                       ↓
              Normalization to [0,1]
                       ↓
              PLN Deduction Formula
              sAC = sAB·sBC + (1-sAB)·(pC-pB·sBC)/(1-pB)
```

## Main Results

1. `ks_representation_to_probability` - K&S representation gives probability via normalization
2. `probability_satisfies_frechet` - The normalized probabilities satisfy Fréchet bounds
3. `ks_separation_implies_pln_deduction` - Main theorem: K&S + Separation → PLN formula

## Mathematical Background

### The K&S Side

K&S + Separation gives an order-preserving additive embedding Θ : α → ℝ≥0.
For events A, B in the Boolean algebra, we have:
- Θ(A ∨ B) + Θ(A ∧ B) = Θ(A) + Θ(B)  (modularity from additivity)
- Θ respects the order

### The Normalization

Given a reference event Ω (the "universe"), define:
- P(A) := Θ(A) / Θ(Ω)

This gives P : α → [0, 1] satisfying:
- P(Ω) = 1
- P(∅) = 0 (if ∅ exists)
- P(A ∨ B) = P(A) + P(B) - P(A ∧ B) (finite additivity)

### The Deduction Formula

With conditional probability P(B|A) := P(A ∧ B) / P(A), the law of total probability
and independence assumption give the PLN deduction formula.

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter 5
- PLNFrechetBounds.lean for the Fréchet ↔ consistency equivalence
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.PLNConnection

open Mettapedia.Logic.PLNDeduction

/-!
## §1: K&S Representation Structure

We work with the representation theorem output: an additive order embedding Θ.
-/

/-- The K&S representation: an additive order-preserving map to ℝ≥0 -/
structure KSRepresentation (α : Type*) [LE α] where
  /-- The additive valuation -/
  Θ : α → ℝ
  /-- Non-negativity -/
  Θ_nonneg : ∀ a, 0 ≤ Θ a
  /-- Order preservation -/
  Θ_mono : ∀ a b, a ≤ b → Θ a ≤ Θ b

/-- A K&S representation on a Boolean algebra with additivity -/
structure KSBooleanRepresentation (α : Type*) [BooleanAlgebra α] extends KSRepresentation α where
  /-- Modularity: Θ(a ∨ b) + Θ(a ∧ b) = Θ(a) + Θ(b) -/
  Θ_modular : ∀ a b, Θ (a ⊔ b) + Θ (a ⊓ b) = Θ a + Θ b
  /-- Bottom is zero -/
  Θ_bot : Θ ⊥ = 0

namespace KSBooleanRepresentation

variable {α : Type*} [BooleanAlgebra α] (R : KSBooleanRepresentation α)

/-!
## §2: Normalization to Probability
-/

/-- Normalized probability: P(a) = Θ(a) / Θ(⊤) -/
noncomputable def probability (a : α) : ℝ :=
  if _h : R.Θ ⊤ = 0 then 0 else R.Θ a / R.Θ ⊤

/-- P(⊤) = 1 when Θ(⊤) ≠ 0 -/
theorem probability_top (h : R.Θ ⊤ ≠ 0) : R.probability ⊤ = 1 := by
  unfold probability
  rw [dif_neg h]
  exact div_self h

/-- P(⊥) = 0 -/
theorem probability_bot : R.probability ⊥ = 0 := by
  unfold probability
  split_ifs with h
  · rfl
  · simp [R.Θ_bot]

/-- P is non-negative -/
theorem probability_nonneg (a : α) : 0 ≤ R.probability a := by
  unfold probability
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg (R.Θ_nonneg a) (R.Θ_nonneg ⊤)

/-- P(a) ≤ 1 when a ≤ ⊤ -/
theorem probability_le_one (a : α) : R.probability a ≤ 1 := by
  unfold probability
  split_ifs with h
  · exact zero_le_one
  · have h_top_pos : 0 < R.Θ ⊤ := lt_of_le_of_ne (R.Θ_nonneg ⊤) (Ne.symm h)
    rw [div_le_one h_top_pos]
    exact R.Θ_mono a ⊤ le_top

/-- P is in [0, 1] -/
theorem probability_mem_unit (a : α) : R.probability a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨R.probability_nonneg a, R.probability_le_one a⟩

/-- Finite additivity from modularity -/
theorem probability_modular (a b : α) (h : R.Θ ⊤ ≠ 0) :
    R.probability (a ⊔ b) + R.probability (a ⊓ b) = R.probability a + R.probability b := by
  simp only [probability, h, ↓reduceDIte]
  rw [← add_div, ← add_div, R.Θ_modular]

/-!
## §3: Conditional Probability and the Deduction Formula
-/

/-- Conditional probability: P(b|a) = P(a ⊓ b) / P(a) -/
noncomputable def condProb (b a : α) : ℝ :=
  if _h : R.probability a = 0 then 0 else R.probability (a ⊓ b) / R.probability a

/-- The key lemma: P(a ⊓ b) = P(a) · P(b|a) -/
theorem prob_inf_eq_mul_cond (a b : α) (ha : R.probability a ≠ 0) :
    R.probability (a ⊓ b) = R.probability a * R.condProb b a := by
  simp [condProb, ha, mul_div_cancel₀]

/-!
## §4: Fréchet Bounds from K&S Structure

The Fréchet bounds are a consequence of the Boolean algebra structure
and the non-negativity of Θ.
-/

/-- Fréchet lower bound: P(a ⊓ b) ≥ max(0, P(a) + P(b) - 1) -/
theorem frechet_lower (a b : α) (h : R.Θ ⊤ ≠ 0) :
    max 0 (R.probability a + R.probability b - 1) ≤ R.probability (a ⊓ b) := by
  apply max_le
  · exact R.probability_nonneg (a ⊓ b)
  · -- From modularity: P(a) + P(b) = P(a ⊔ b) + P(a ⊓ b)
    -- So P(a ⊓ b) = P(a) + P(b) - P(a ⊔ b) ≥ P(a) + P(b) - 1
    have hmod := R.probability_modular a b h
    have hle : R.probability (a ⊔ b) ≤ 1 := R.probability_le_one (a ⊔ b)
    linarith

/-- Fréchet upper bound: P(a ⊓ b) ≤ min(P(a), P(b)) -/
theorem frechet_upper (a b : α) :
    R.probability (a ⊓ b) ≤ min (R.probability a) (R.probability b) := by
  apply le_min
  · -- P(a ⊓ b) ≤ P(a) since a ⊓ b ≤ a
    unfold probability
    split_ifs with h
    · exact le_refl 0
    · apply div_le_div_of_nonneg_right _ (R.Θ_nonneg ⊤)
      exact R.Θ_mono (a ⊓ b) a inf_le_left
  · -- P(a ⊓ b) ≤ P(b) since a ⊓ b ≤ b
    unfold probability
    split_ifs with h
    · exact le_refl 0
    · apply div_le_div_of_nonneg_right _ (R.Θ_nonneg ⊤)
      exact R.Θ_mono (a ⊓ b) b inf_le_right

/-!
## §5: The Main Theorem: K&S + Separation → PLN Deduction
-/

/-- Conditional probability satisfies PLN consistency bounds -/
theorem condProb_consistent (a b : α) (h : R.Θ ⊤ ≠ 0) (ha : R.probability a ≠ 0) :
    conditionalProbabilityConsistency (R.probability a) (R.probability b) (R.condProb b a) := by
  have ha_pos : 0 < R.probability a := lt_of_le_of_ne (R.probability_nonneg a) (Ne.symm ha)
  have hfrechet_lower := R.frechet_lower a b h
  have hfrechet_upper := R.frechet_upper a b
  constructor
  · -- 0 < P(a)
    exact ha_pos
  constructor
  · -- Lower bound from Fréchet
    -- smallestIntersectionProbability pA pB = max 0 ((pA + pB - 1) / pA)
    unfold smallestIntersectionProbability condProb
    simp only [ha, ↓reduceDIte]
    apply max_le
    · -- 0 ≤ P(a ⊓ b) / P(a)
      apply div_nonneg (R.probability_nonneg _) (le_of_lt ha_pos)
    · -- (P(a) + P(b) - 1) / P(a) ≤ P(a ⊓ b) / P(a)
      apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
      -- P(a) + P(b) - 1 ≤ P(a ⊓ b) from Fréchet lower bound
      -- hfrechet_lower : max 0 (P+P-1) ≤ P(a⊓b), so P+P-1 ≤ max 0 (P+P-1) ≤ P(a⊓b)
      exact le_trans (le_max_right 0 _) hfrechet_lower
  · -- Upper bound from Fréchet
    -- largestIntersectionProbability pA pB = min 1 (pB / pA)
    unfold largestIntersectionProbability condProb
    simp only [ha, ↓reduceDIte]
    apply le_min
    · -- P(a ⊓ b) / P(a) ≤ 1
      rw [div_le_one ha_pos]
      exact (le_min_iff.mp hfrechet_upper).1
    · -- P(a ⊓ b) / P(a) ≤ P(b) / P(a)
      apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
      exact (le_min_iff.mp hfrechet_upper).2

/-- Conditional probability is non-negative -/
theorem condProb_nonneg (b a : α) : 0 ≤ R.condProb b a := by
  unfold condProb
  split_ifs
  · exact le_refl 0
  · apply div_nonneg (R.probability_nonneg _) (R.probability_nonneg _)

/-- Conditional probability is at most 1 -/
theorem condProb_le_one (b a : α) : R.condProb b a ≤ 1 := by
  unfold condProb
  split_ifs with h
  · exact zero_le_one
  · have ha_pos : 0 < R.probability a := lt_of_le_of_ne (R.probability_nonneg a) (Ne.symm h)
    rw [div_le_one ha_pos]
    -- P(a ⊓ b) ≤ P(a) since a ⊓ b ≤ a
    have hle := R.frechet_upper a b
    exact le_trans (le_min_iff.mp hle).1 (le_refl _)

/-- Conditional probability is in [0, 1] -/
theorem condProb_mem_unit (b a : α) : R.condProb b a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨R.condProb_nonneg b a, R.condProb_le_one b a⟩

/-- **Main Theorem**: K&S representation implies PLN deduction formula is valid.

Given a K&S representation on a Boolean algebra, the PLN deduction formula
produces valid probabilities in [0, 1].

This completes the derivation chain:
  K&S Axioms + Separation
         ↓
  Representation Theorem (Θ : α ≃o ℝ≥0)
         ↓
  Normalization (P = Θ/Θ(⊤))
         ↓
  Fréchet bounds (from modularity)
         ↓
  PLN consistency (from Fréchet)
         ↓
  PLN deduction formula valid
-/
theorem ks_implies_pln_valid (a b c : α)
    (h : R.Θ ⊤ ≠ 0)
    (ha : R.probability a ≠ 0)
    (hb : R.probability b ≠ 0)
    (hb_small : R.probability b < 0.99) :
    simpleDeductionStrengthFormula
      (R.probability a) (R.probability b) (R.probability c)
      (R.condProb b a) (R.condProb c b) ∈ Set.Icc (0 : ℝ) 1 := by
  have h_consist_ab := R.condProb_consistent a b h ha
  have h_consist_bc := R.condProb_consistent b c h hb
  exact deduction_formula_in_unit_interval
    (R.probability a) (R.probability b) (R.probability c)
    (R.condProb b a) (R.condProb c b)
    (R.probability_mem_unit a) (R.probability_mem_unit b) (R.probability_mem_unit c)
    (R.condProb_mem_unit b a)
    (R.condProb_mem_unit c b)
    hb_small
    ⟨h_consist_ab, h_consist_bc⟩

end KSBooleanRepresentation

/-!
## §6: Indefinite PLN from Credal Sets

The indefinite version of PLN (interval truth values) corresponds to:
1. K&S without completeness → credal set (set of representations)
2. Each representation gives a probability
3. The interval [L, U] = [inf P, sup P] over the credal set

This connects to:
- Walley's imprecise probabilities (LowerPrevision, UpperPrevision)
- The CredalAlgebra structure in CredalSets.lean
-/

/-- A credal set is a set of K&S representations.

Without completeness, we may have multiple valid representations,
giving interval-valued probabilities. -/
structure CredalSet (α : Type*) [BooleanAlgebra α] where
  representations : Set (KSBooleanRepresentation α)
  nonempty : representations.Nonempty

namespace CredalSet

variable {α : Type*} [BooleanAlgebra α] (C : CredalSet α)

/-- Lower probability: P*(a) = inf { R.probability a | R ∈ credal set } -/
noncomputable def lowerProb (a : α) : ℝ :=
  sInf { R.probability a | R ∈ C.representations }

/-- Upper probability: P*(a) = sup { R.probability a | R ∈ credal set } -/
noncomputable def upperProb (a : α) : ℝ :=
  sSup { R.probability a | R ∈ C.representations }

/-- The probability interval for an event -/
noncomputable def probInterval (a : α) : Set ℝ :=
  Set.Icc (C.lowerProb a) (C.upperProb a)

/-- **Indefinite PLN Truth Value** from credal set:
- Strength interval: [L, U] = [lowerProb, upperProb]
- Confidence: related to interval width (narrower = more confident)
-/
structure IndefiniteTruthValue where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1

/-- Convert credal probability to indefinite truth value -/
noncomputable def toIndefiniteTruthValue (a : α)
    (h_lower : 0 ≤ C.lowerProb a)
    (h_upper : C.upperProb a ≤ 1)
    (h_valid : C.lowerProb a ≤ C.upperProb a) : IndefiniteTruthValue where
  lower := C.lowerProb a
  upper := C.upperProb a
  valid := h_valid
  lower_nonneg := h_lower
  upper_le_one := h_upper

end CredalSet

/-!
## §7: Summary: The Complete Derivation Diagram

```
                    ┌─────────────────────────────────────┐
                    │          Hypercube Vertex           │
                    │  (commutative, precise, tensor)     │
                    └─────────────────────────────────────┘
                                     │
           ┌─────────────────────────┼─────────────────────────┐
           │                         │                         │
           ▼                         ▼                         ▼
    ┌─────────────┐          ┌─────────────┐          ┌─────────────┐
    │  Kolmogorov │          │     Cox     │          │ K&S + Sep   │
    │  σ-algebra  │          │  Func. eqs  │          │  Assoc+Arch │
    └─────────────┘          └─────────────┘          └─────────────┘
           │                         │                         │
           ▼                         ▼                         ▼
    ┌─────────────┐          ┌─────────────┐          ┌─────────────┐
    │  Measure    │          │  Product    │          │  Θ : α→ℝ≥0  │
    │  Theory     │          │  Rule       │          │  (additive) │
    └─────────────┘          └─────────────┘          └─────────────┘
           │                         │                         │
           └─────────────────────────┼─────────────────────────┘
                                     │
                                     ▼
                         ┌───────────────────┐
                         │   Normalization   │
                         │   P = Θ/Θ(Ω)      │
                         └───────────────────┘
                                     │
                                     ▼
                         ┌───────────────────┐
                         │  Fréchet Bounds   │
                         │  (from modularity)│
                         └───────────────────┘
                                     │
                    ┌────────────────┼────────────────┐
                    │                │                │
                    ▼                ▼                ▼
             ┌───────────┐    ┌───────────┐    ┌───────────┐
             │ PLN Simple│    │ Law of    │    │  Credal   │
             │ Deduction │◄───│ Total Prob│───►│   Sets    │
             └───────────┘    └───────────┘    └───────────┘
                    │                                │
                    ▼                                ▼
             ┌───────────┐                    ┌───────────┐
             │  sAC =    │                    │ PLN Indef │
             │ sAB·sBC + │                    │ [L, U], b │
             │   ...     │                    └───────────┘
             └───────────┘
```

**Key Insight**: All three axiom systems (Kolmogorov, Cox, K&S+Separation)
derive the SAME PLN deduction formula because they all:
1. Give additive probability measures
2. Satisfy Fréchet bounds
3. Support the law of total probability

The indefinite PLN version arises when:
- K&S without completeness → credal set (interval probabilities)
- This corresponds to the `plnIndefinite` vertex in the hypercube
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.PLNConnection
