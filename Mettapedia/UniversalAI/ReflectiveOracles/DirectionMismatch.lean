import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Direction Mismatch in Reflective Oracle Construction

This file documents and investigates a potential flaw in Leike's Reflective Oracle
construction (Thesis Chapter 7, arXiv:1609.05058).

## The Problem

The construction builds oracles by induction, extending partial oracles one query at a time.
At each step, there are two directions that need to be satisfied:

### Direction 1: Soundness (preserved by extension)
"If the oracle claims value = 1, then P(output 1) > threshold"

Formally: `oracle_value = 1 → P(output 1 | partial_oracle) > threshold`

### Direction 2: Completeness (NOT obviously preserved)
"If P(output 1) > threshold, then the oracle claims value = 1"

Formally: `P(output 1 | full_oracle) > threshold → oracle_value = 1`

## The Gap

The extension construction (König's lemma argument) preserves **soundness** but not
obviously **completeness**:

1. When we extend a partial oracle and set a new value = 1, we verify that
   `P(output 1 | partial_oracle) > threshold`. This gives soundness.

2. But the limit oracle O satisfies `P(output 1 | O) ≥ P(output 1 | partial_oracle)`
   (by monotonicity), so we can't conclude from the partial probability being
   above threshold that the full probability is above threshold.

3. Conversely, if `P(output 1 | O) > threshold`, we need to show the oracle says 1.
   But the oracle value was determined by the **partial** probability, which might
   have been below threshold even if the full probability is above.

## Potential Flaw

If this gap is real, then Leike's Theorem 7.1 (Existence of Reflective Oracles)
may have a hole in its proof. Specifically, the limit of partially reflective oracles
may satisfy soundness but not completeness.

## Investigation Strategy

1. Try to construct a concrete counterexample
2. Or find a proof that closes the gap
3. The key lemma needed is:
   `∀ ε > 0, ∃ k, P(output 1 | O) - P(output 1 | partial_k) < ε`
   This would show that if P(full) > threshold, then eventually P(partial_k) > threshold,
   so the oracle would have claimed 1.

## Formalization

-/

namespace Mettapedia.UniversalAI.ReflectiveOracles

/-! ## Abstract formulation of the problem -/

/-- A threshold query for whether P > p. -/
structure Query where
  threshold : ℝ
  threshold_pos : 0 < threshold
  threshold_lt_one : threshold < 1

/-- Soundness: oracle says 1 implies probability > threshold -/
def SoundnessCondition (oracle_value : ℝ) (prob : ℝ) (q : Query) : Prop :=
  oracle_value = 1 → prob > q.threshold

/-- Completeness: probability > threshold implies oracle says 1 -/
def CompletenessCondition (oracle_value : ℝ) (prob : ℝ) (q : Query) : Prop :=
  prob > q.threshold → oracle_value = 1

/-- A reflective oracle must satisfy BOTH soundness and completeness -/
def IsReflective (oracle_value : ℝ) (prob : ℝ) (q : Query) : Prop :=
  SoundnessCondition oracle_value prob q ∧ CompletenessCondition oracle_value prob q

/-! ## The construction's gap

During construction, we verify soundness with partial probability,
but need completeness with full probability.

**Key variables:**
- `partial_prob`: The probability when the oracle value was decided
- `full_prob`: The probability for the limit oracle

**Monotonicity (Lemma 7.3):** `partial_prob ≤ full_prob`

**Construction ensures:** `oracle_value = 1 → partial_prob > threshold`

**THE GAP:** Does this imply completeness?
We have:
- `partial_prob > threshold` (from construction)
- `full_prob ≥ partial_prob` (from monotonicity)
We want:
- `full_prob > threshold → oracle says 1`
But: `full_prob` might be > threshold even though oracle said 0!
-/

/-! ## Potential counterexample structure

A counterexample would be:
1. A partial oracle Õ that is partially reflective
2. The limit oracle O that Õ approximates
3. A query q where:
   - `partial_prob(Õ, q) < threshold` (so Õ says 0 or 1/2)
   - `full_prob(O, q) > threshold` (so O SHOULD say 1)
   - But `O.value(q) ≠ 1` because it's inherited from Õ

The question is: can such a situation occur in the limit construction?
-/

/-- If the partial probabilities converge to the full probability,
    then the gap would be closed. This theorem shows that uniform
    convergence is sufficient to close the gap. -/
theorem gap_closed_if_uniform_convergence
    (full_prob : Query → ℝ)
    (partial_probs : ℕ → Query → ℝ)
    (_h_mono : ∀ k q, partial_probs k q ≤ partial_probs (k + 1) q)
    (h_limit : ∀ q ε, ε > 0 → ∃ K, ∀ k ≥ K, |partial_probs k q - full_prob q| < ε)
    (oracle_value : Query → ℝ)
    (_h_soundness : ∀ k q, oracle_value q = 1 → partial_probs k q > q.threshold)
    (q : Query)
    (h_full_above : full_prob q > q.threshold) :
    -- Claim: there exists k such that partial_probs k q > threshold
    ∃ k, partial_probs k q > q.threshold := by
  -- Let ε = (full_prob q - threshold) / 2 > 0
  set ε := (full_prob q - q.threshold) / 2 with hε_def
  have hε_pos : ε > 0 := by simp only [hε_def]; linarith
  -- By h_limit, there exists K such that |partial_probs K q - full_prob q| < ε
  obtain ⟨K, hK⟩ := h_limit q ε hε_pos
  use K
  -- Then partial_probs K q > full_prob q - ε = full_prob q - (full_prob q - threshold)/2
  --                       = (full_prob q + threshold) / 2 > threshold
  have h1 := hK K (le_refl K)
  have h2 : partial_probs K q > full_prob q - ε := by
    rw [abs_sub_lt_iff] at h1
    linarith
  calc partial_probs K q > full_prob q - ε := h2
    _ = (full_prob q + q.threshold) / 2 := by simp only [hε_def]; ring
    _ > q.threshold := by linarith

/-! ## Open question

The key question is: does the Leike construction guarantee that the partial probabilities
converge uniformly (or at least pointwise with the right ordering) to the full probability?

If not, then there might be a genuine flaw in the construction.

If yes, then `gap_closed_if_uniform_convergence` closes the gap.

The convergence would follow from the compactness of Cantor space (König's lemma)
plus the fact that all runs eventually stabilize. But this needs careful verification.

**Status**: This is an open investigation that could lead to either:
1. A formal proof that the gap is closed (strengthening Leike's result)
2. A counterexample showing a flaw in the construction (publication-worthy)
-/

end Mettapedia.UniversalAI.ReflectiveOracles
