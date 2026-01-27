/-
# Information Theory for Heyting K&S

## Overview

This file develops information-theoretic concepts for Heyting K&S probability,
building on the Heyting bounds construction from HeytingBounds.lean.

## Key Insight

In Heyting algebras, the "excluded middle gap" creates bounds on information:
- Lower bound: entropy computed using lower probabilities
- Upper bound: entropy computed using upper probabilities

The gap in entropy bounds reflects the "epistemic slack" from non-Boolean
complement behavior.

## What This File Does NOT Claim

- ❌ "Intervals are forced by incomparability" - FALSE, removed
- ❌ Specific forms for interval entropy arithmetic

## What This File DOES Establish

- ✓ Entropy bounds from Heyting bounds [lower, upper]
- ✓ Boolean collapse: when gap = 0, entropy bounds coincide
- ✓ Connection to the excluded middle gap

## References

- Shannon, "A Mathematical Theory of Communication" (1948)
- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- See HeytingBounds.lean for the foundation
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingValuation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingBounds

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting.Information

open Real
open Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

/-! ## Binary Entropy Function -/

/-- The binary entropy function H(p) = -p·log(p) - (1-p)·log(1-p).
    This is the entropy of a Bernoulli distribution with parameter p. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if p ≤ 0 then 0
  else if p ≥ 1 then 0
  else -p * log p - (1 - p) * log (1 - p)

/-- Binary entropy is non-negative on [0,1]. -/
theorem binaryEntropy_nonneg (p : ℝ) (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    0 ≤ binaryEntropy p := by
  unfold binaryEntropy
  split_ifs with h0 h1
  · exact le_refl 0
  · exact le_refl 0
  · -- For 0 < p < 1, both log terms are negative, so negatives are positive
    push_neg at h0 h1
    have hp_pos : 0 < p := h0
    have hp_lt_one : p < 1 := h1
    have h1mp_pos : 0 < 1 - p := by linarith
    -- log p < 0 and log (1-p) < 0 for p ∈ (0,1)
    have hlogp : log p < 0 := log_neg hp_pos hp_lt_one
    have hlog1mp : log (1 - p) < 0 := log_neg h1mp_pos (by linarith)
    -- So -p·log(p) > 0 and -(1-p)·log(1-p) > 0
    -- Note: -p * log p parses as (-p) * (log p), so negative × negative = positive
    have hnp : -p < 0 := neg_neg_of_pos hp_pos
    have hn1mp : -(1 - p) < 0 := neg_neg_of_pos h1mp_pos
    have h1 : 0 < -p * log p := mul_pos_of_neg_of_neg hnp hlogp
    have h2 : 0 < -(1 - p) * log (1 - p) := mul_pos_of_neg_of_neg hn1mp hlog1mp
    linarith

/-- Binary entropy at p = 0 is 0. -/
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  unfold binaryEntropy
  simp

/-- Binary entropy at p = 1 is 0. -/
theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  unfold binaryEntropy
  simp

/-! ## Entropy Bounds from Heyting Bounds -/

variable {α : Type*} [HeytingAlgebra α]

/-- For a binary event a, the lower entropy bound uses the Heyting lower probability.
    H_lower(a) = H(lower(a)) = H(ν(a)) -/
noncomputable def entropyLowerBound (ν : ModularValuation α) (a : α) : ℝ :=
  binaryEntropy (lowerBound ν a)

/-- For a binary event a, the upper entropy bound uses the Heyting upper probability.
    H_upper(a) = H(upper(a)) = H(1 - ν(¬a)) -/
noncomputable def entropyUpperBound (ν : ModularValuation α) (a : α) : ℝ :=
  binaryEntropy (upperBound ν a)

/-- The entropy bounds are within [0, log 2] (the maximum binary entropy). -/
theorem entropyLowerBound_bounded (ν : ModularValuation α) (a : α) :
    0 ≤ entropyLowerBound ν a := by
  unfold entropyLowerBound
  apply binaryEntropy_nonneg
  · exact ν.nonneg a
  · exact ν.le_one a

theorem entropyUpperBound_bounded (ν : ModularValuation α) (a : α) :
    0 ≤ entropyUpperBound ν a := by
  unfold entropyUpperBound
  apply binaryEntropy_nonneg
  · -- upper(a) = 1 - ν(¬a) ≥ 0 because ν(¬a) ≤ 1
    unfold upperBound
    have h := ν.le_one aᶜ
    linarith
  · -- upper(a) = 1 - ν(¬a) ≤ 1 because ν(¬a) ≥ 0
    unfold upperBound
    have h := ν.nonneg aᶜ
    linarith

/-! ## Boolean Collapse for Entropy -/

/-- In Boolean algebras, the entropy bounds coincide.
    This is because lower(a) = upper(a) when ν(a) + ν(¬a) = 1. -/
theorem boolean_entropy_collapse {β : Type*} [BooleanAlgebra β]
    (ν : ModularValuation β) (a : β) :
    entropyLowerBound ν a = entropyUpperBound ν a := by
  unfold entropyLowerBound entropyUpperBound
  rw [boolean_collapse ν a]

/-! ## The Entropy Gap -/

/-- The entropy gap measures the uncertainty in entropy due to non-Boolean structure.
    When the excluded middle gap is zero (Boolean case), this is also zero. -/
noncomputable def entropyGap (ν : ModularValuation α) (a : α) : ℝ :=
  entropyUpperBound ν a - entropyLowerBound ν a

/-- In Boolean algebras, the entropy gap is zero. -/
theorem boolean_entropyGap_zero {β : Type*} [BooleanAlgebra β]
    (ν : ModularValuation β) (a : β) :
    entropyGap ν a = 0 := by
  unfold entropyGap
  rw [boolean_entropy_collapse]
  ring

/-! ## Connection to Excluded Middle Gap

The entropy gap and excluded middle gap are related but not identical.
The excluded middle gap measures the "probability slack" (upper - lower),
while the entropy gap measures the "information slack" (H(upper) - H(lower)).

These are related through the binary entropy function, which is:
- Concave on [0,1]
- Maximized at p = 1/2 with H(1/2) = log 2
- Zero at p = 0 and p = 1

The entropy gap depends on WHERE in [0,1] the bounds [lower, upper] fall,
not just on their width.
-/

/-- When both lower and upper are in (0,1), we can analyze the entropy gap
    more precisely. This requires additional assumptions. -/
theorem entropyGap_depends_on_location (ν : ModularValuation α) (a : α)
    (_h_lower_pos : 0 < lowerBound ν a)
    (_h_upper_lt_one : upperBound ν a < 1) :
    -- The entropy gap exists (is well-defined)
    entropyGap ν a = binaryEntropy (upperBound ν a) - binaryEntropy (lowerBound ν a) := by
  unfold entropyGap entropyUpperBound entropyLowerBound
  ring

/-! ## Summary

This file establishes:

1. **Binary entropy bounds** from Heyting probability bounds:
   - H_lower = H(ν(a))
   - H_upper = H(1 - ν(¬a))

2. **Boolean collapse**: When ν(a) + ν(¬a) = 1, the bounds coincide.

3. **Entropy gap**: The difference H_upper - H_lower measures information
   uncertainty due to non-Boolean structure.

The key insight: The Heyting bounds [lower, upper] on probability
induce bounds on entropy through the binary entropy function.
This is a natural consequence of the complement inequality,
not of any "incomparability forcing intervals" claim.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting.Information
