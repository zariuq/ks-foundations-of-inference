import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.FiniteProbability

/-!
# Coin Flip and Die Roll (`ProbDist` examples)

This file provides small, concrete examples of finite probability distributions (`ProbDist`)
and a basic notion of event probability for `Finset` events.

These are hand-constructed distributions meant as lightweight sanity checks and usage examples.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.CoinDie

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Finset BigOperators

/-! ## §1: Fair Coin Flip -/

/-- The fair coin probability distribution.

This is `ProbDist 2` with P(heads) = P(tails) = 1/2.
-/
noncomputable def fairCoin : ProbDist 2 where
  p := fun _ => 1/2
  nonneg := by intro _; linarith
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

@[simp] theorem fairCoin_apply (i : Fin 2) : fairCoin.p i = 1/2 := rfl

/-- Fair coin: both outcomes have equal probability -/
theorem fairCoin_symmetric : fairCoin.p 0 = fairCoin.p 1 := rfl

/-! ## §2: Fair Die Roll -/

/-- The fair 6-sided die probability distribution.

This is `ProbDist 6` with P(i) = 1/6 for all faces. -/
noncomputable def fairDie : ProbDist 6 where
  p := fun _ => 1/6
  nonneg := by intro _; linarith
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

@[simp] theorem fairDie_apply (i : Fin 6) : fairDie.p i = 1/6 := rfl

/-- Fair die: all outcomes have equal probability -/
theorem fairDie_uniform (i j : Fin 6) : fairDie.p i = fairDie.p j := rfl

/-! ## §3: Probability of Events -/

/-- Probability of an event (subset of outcomes) under a distribution.

For `ProbDist n`, an event is a `Finset (Fin n)` and its probability
is the sum of individual outcome probabilities. -/
noncomputable def eventProb {n : ℕ} (P : ProbDist n) (E : Finset (Fin n)) : ℝ :=
  ∑ i ∈ E, P.p i

/-- Event probability is non-negative -/
theorem eventProb_nonneg {n : ℕ} (P : ProbDist n) (E : Finset (Fin n)) :
    0 ≤ eventProb P E := by
  apply Finset.sum_nonneg
  intro i _
  exact P.nonneg i

/-- Probability of the entire sample space is 1 -/
theorem eventProb_univ {n : ℕ} (P : ProbDist n) :
    eventProb P Finset.univ = 1 := P.sum_one

/-- Probability of empty event is 0 -/
theorem eventProb_empty {n : ℕ} (P : ProbDist n) :
    eventProb P ∅ = 0 := Finset.sum_empty

/-- Finite additivity: P(A ∪ B) = P(A) + P(B) for disjoint A, B -/
theorem eventProb_union_disjoint {n : ℕ} (P : ProbDist n)
    (A B : Finset (Fin n)) (hDisj : Disjoint A B) :
    eventProb P (A ∪ B) = eventProb P A + eventProb P B := by
  unfold eventProb
  exact Finset.sum_union hDisj

/-! ## §4: Summary

Defined `fairCoin`, `fairDie`, and `eventProb`, and proved basic properties:
nonnegativity, normalization on `univ`, and finite additivity for disjoint unions.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.CoinDie
