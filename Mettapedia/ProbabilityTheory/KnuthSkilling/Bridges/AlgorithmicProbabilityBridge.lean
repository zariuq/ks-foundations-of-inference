import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.KLDivergenceBridge
import Mettapedia.Logic.SolomonoffPrior

/-!
# K&S <-> Solomonoff: a careful bridge for "well-founded universal inference"

## What this file is (and is not)

Knuth--Skilling (K&S) and Solomonoff address *different* parts of the "foundations of inference"
story:

* **K&S**: derives the *structure* of probability / information calculus (sum/product rules,
  KL divergence / entropy) from symmetries and variational principles.
* **Solomonoff**: provides a canonical *assignment* of prior weight via algorithmic probability.

The connection point is **information theory**: both frameworks naturally meet at
Gibbs' inequality / KL nonnegativity.

Crucially, the raw Solomonoff object `M` is (in general) a **semimeasure** rather than a
probability measure: totals are `≤ 1`, not `= 1`. So we do **not** claim that "Solomonoff is a
K&S probability distribution" on its native domain. Instead we provide a small, honest
normalization construction:

> Restrict any nonnegative weight function to a *finite* domain and normalize it to a `ProbDist`.

Once normalized, the K&S information layer (and its UAI likelihood-ratio bridge) applies
directly.

## Existing heavy lifting elsewhere

The real theorem-level meeting point is already formalized as a KL identity/inequality bridge:

* `Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/KLDivergenceBridge.lean`

which connects:

* UAI step log-likelihood sums
* K&S `klDivergence` on `ProbDist`
* (and the measure-theoretic `klDiv` through the ShannonEntropy interface layer)

This file packages just enough plumbing so future work can cleanly say:
"use Solomonoff(-style) weights, normalize on a finite domain, then apply K&S KL facts."
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges

open Classical
open Finset
open scoped BigOperators

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy

/-! ## Normalizing weights on a finite domain -/

/-- Normalize nonnegative weights on `Fin n` into a `ProbDist n`.

This is the minimal construction needed to turn a semimeasure-like assignment into an honest
finite probability distribution (the K&S object used throughout Section 8 / KL divergence).
-/
noncomputable def normalizeWeights {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum_pos : 0 < ∑ i, w i) : ProbDist n :=
  let Z : ℝ := ∑ i, w i
  { p := fun i => w i / Z
    nonneg := fun i => div_nonneg (hw i) (le_of_lt hsum_pos)
    sum_one := by
      classical
      have hZ : Z ≠ 0 := ne_of_gt hsum_pos
      -- `∑ (w i / Z) = (∑ w i) / Z = 1`.
      -- We do it as `w i * (1/Z)` so `Finset.sum_mul` applies.
      calc
        (∑ i : Fin n, w i / Z) = ∑ i : Fin n, w i * (1 / Z) := by
          simp [div_eq_mul_inv]
        _ = (∑ i : Fin n, w i) * (1 / Z) := by
          simp [Finset.sum_mul]
        _ = Z * (1 / Z) := by
          simp [Z]
        _ = 1 := by
          field_simp [hZ] }

/-! ## Normalizing a Solomonoff semimeasure on a finite set of strings -/

namespace Solomonoff

open Mettapedia.Logic.SolomonoffPrior

/-- Normalize a Solomonoff-style semimeasure `μ` on a finite set of strings.

This is the honest way to get a `ProbDist` from algorithmic probability: restrict to a finite
"hypothesis class" (a finset) and renormalize.
-/
noncomputable def normalizeSemimeasureOnFinset
    (sm : Semimeasure) (s : Finset BinString)
    (hsum_pos : 0 < Finset.sum s (fun x => sm.μ x)) : ProbDist (#s) := by
  classical
  -- Enumerate the finset by `Fin #s`.
  let e := s.equivFin
  let w : Fin #s → ℝ := fun i => sm.μ (e.symm i).1
  have hw : ∀ i, 0 ≤ w i := fun i => sm.nonneg (e.symm i).1

  -- Convert the finset sum hypothesis into the corresponding `Fin #s` sum.
  have hsum_pos' : 0 < ∑ i : Fin #s, w i := by
    have hsum_eq :
        (∑ i : Fin #s, w i) = Finset.sum s (fun x => sm.μ x) := by
      -- Reindex the `Fin #s` sum along `e.symm : Fin #s ≃ s`.
      have h1 :
          (∑ i : Fin #s, sm.μ (e.symm i).1) = ∑ x : s, sm.μ x.1 := by
        simpa using (Equiv.sum_comp e.symm (fun x : s => sm.μ x.1))
      -- Convert the subtype sum to a finset sum.
      have h2 : (∑ x : s, sm.μ x.1) = Finset.sum s (fun x => sm.μ x) := by
        -- `∑ x : s, f x` is a sum over `Finset.univ : Finset s`, which is definitionally `s.attach`.
        -- Then `Finset.sum_attach` converts it back to a sum over `s`.
        simpa [Finset.univ_eq_attach] using (Finset.sum_attach (s := s) (f := sm.μ))
      simpa [w] using h1.trans h2
    simpa [hsum_eq] using hsum_pos

  exact normalizeWeights w hw hsum_pos'

end Solomonoff

/-! ## Infinite-domain prediction from cylinder measures -/

namespace Solomonoff

open Mettapedia.Logic.SolomonoffPrior

namespace Prediction

/-- The Solomonoff-style "next-bit" conditional from a cylinder semimeasure.

For a semimeasure, this is generally a **subprobability**: the two outcomes can sum to `≤ 1`,
with the missing mass corresponding to programs that produce no next bit after `x`.
-/
noncomputable def cylinderConditional (U : MonotoneMachine) (programs : Finset BinString)
    (x : BinString) (b : Bool) (_hx : 0 < U.cylinderMeasure programs x) : ℝ :=
  U.cylinderMeasure programs (x ++ [b]) / U.cylinderMeasure programs x

/-- Cylinder conditional probabilities are nonnegative. -/
theorem cylinderConditional_nonneg (U : MonotoneMachine) (programs : Finset BinString)
    (x : BinString) (b : Bool) (hx : 0 < U.cylinderMeasure programs x) :
    0 ≤ cylinderConditional U programs x b hx := by
  unfold cylinderConditional
  exact div_nonneg (U.cylinderMeasure_nonneg programs (x ++ [b])) (le_of_lt hx)

/-- The two cylinder conditionals sum to at most `1` (subprobability), by subadditivity. -/
theorem cylinderConditional_sum_le_one (U : MonotoneMachine) (programs : Finset BinString)
    (x : BinString) (hx : 0 < U.cylinderMeasure programs x) :
    cylinderConditional U programs x false hx +
        cylinderConditional U programs x true hx ≤ 1 := by
  have hsub :
      U.cylinderMeasure programs (x ++ [false]) + U.cylinderMeasure programs (x ++ [true])
        ≤ U.cylinderMeasure programs x := by
    simpa using (cylinderMeasure_subadditive (U := U) programs x)
  have hdiv :
      (U.cylinderMeasure programs (x ++ [false]) + U.cylinderMeasure programs (x ++ [true])) /
          U.cylinderMeasure programs x ≤ 1 :=
    (div_le_one hx).2 hsub
  simpa [cylinderConditional, add_div] using hdiv

/-- Weights on `Fin 2` corresponding to the two successor cylinders `x++0` and `x++1`. -/
noncomputable def nextBitWeights (U : MonotoneMachine) (programs : Finset BinString) (x : BinString) :
    Fin 2 → ℝ :=
  fun i =>
    Fin.cases (U.cylinderMeasure programs (x ++ [false]))
      (fun _ => U.cylinderMeasure programs (x ++ [true])) i

theorem nextBitWeights_nonneg (U : MonotoneMachine) (programs : Finset BinString) (x : BinString) :
    ∀ i, 0 ≤ nextBitWeights U programs x i := by
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact U.cylinderMeasure_nonneg programs (x ++ [false])
  · exact U.cylinderMeasure_nonneg programs (x ++ [true])

/-- Normalize the two successor-cylinder weights into a `ProbDist 2`.

This is the conditional distribution on `{0,1}` **conditioned on continuation** (i.e. after
renormalizing away any "halt" mass). It is only defined when the two-cylinder total is positive.
-/
noncomputable def normalizedNextBitDist (U : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hsum_pos : 0 < ∑ i : Fin 2, nextBitWeights U programs x i) : ProbDist 2 :=
  normalizeWeights (nextBitWeights U programs x) (nextBitWeights_nonneg U programs x) hsum_pos

/-- Example: after normalizing the next-bit weights, KL against itself is nonnegative. -/
theorem normalizedNextBitDist_kl_self_nonneg
    (U : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hsum_pos : 0 < ∑ i : Fin 2, nextBitWeights U programs x i) :
    let P := normalizedNextBitDist U programs x hsum_pos
    0 ≤
      klDivergence P P (fun i hi =>
        lt_of_le_of_ne (P.nonneg i) (by
          intro h0
          exact hi (by simpa [eq_comm] using h0))) := by
  intro P
  exact klDivergence_nonneg' P P (fun i hi =>
    lt_of_le_of_ne (P.nonneg i) (by
      intro h0
      exact hi (by simpa [eq_comm] using h0)))

/-- A 3-outcome distribution for the next observation: `0`, `1`, or `halt`.

This distribution exists under the single assumption `0 < μ([x])`, and makes the semimeasure
"missing mass" explicit as a third outcome.

Indexing convention:
* `0 ↦ 0` (next bit is `false`)
* `1 ↦ 1` (next bit is `true`)
* `2 ↦ halt` (no next bit produced after `x`)
-/
noncomputable def nextBitHaltDist (U : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hx : 0 < U.cylinderMeasure programs x) : ProbDist 3 :=
  let p0 := cylinderConditional U programs x false hx
  let p1 := cylinderConditional U programs x true hx
  { p := fun i =>
      match (i : ℕ) with
      | 0 => p0
      | 1 => p1
      | _ => 1 - p0 - p1
    nonneg := by
      intro i
      have hp0 : 0 ≤ p0 := cylinderConditional_nonneg U programs x false hx
      have hp1 : 0 ≤ p1 := cylinderConditional_nonneg U programs x true hx
      have hp2 : 0 ≤ 1 - p0 - p1 := by
        have hsum : p0 + p1 ≤ 1 := cylinderConditional_sum_le_one U programs x hx
        linarith
      fin_cases i
      · simpa [p0, p1] using hp0
      · simpa [p0, p1] using hp1
      · simpa [p0, p1] using hp2
    sum_one := by
      -- `p0 + p1 + (1 - p0 - p1) = 1`.
      have h : p0 + p1 + (1 - p0 - p1) = (1 : ℝ) := by
        ring_nf
      simp [Fin.sum_univ_three, p0, p1, h] }

end Prediction
end Solomonoff

/-! ## The shared gate: Gibbs' inequality / KL nonnegativity -/

open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.KLDivergenceBridge

/-- Package the "shared gate" fact:

* K&S: `klDivergence P Q ≥ 0` (Gibbs' inequality) for finite distributions, and
* UAI: `∑ P * log(Q/P) ≤ 0`, i.e. `-KL(P||Q) ≤ 0`, derived via the K&S Gibbs inequality bridge.

This is the clean mathematical meeting point between algebraic and algorithmic views. -/
theorem gibbs_inequality_shared_gate :
    (∀ {n : ℕ} (P Q : ProbDist n) (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i),
        0 ≤ klDivergence P Q hQ_pos) ∧
    (∀ {n : ℕ} (_hn : 0 < n) (P Q : Fin n → ℝ)
        (_hP_nonneg : ∀ i, 0 ≤ P i) (_hQ_nonneg : ∀ i, 0 ≤ Q i)
        (_hP_sum : ∑ i, P i = 1) (_hQ_sum : ∑ i, Q i = 1)
        (_hQ_pos : ∀ i, P i ≠ 0 → 0 < Q i),
        ∑ i, P i * Real.log (Q i / P i) ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro n P Q hQ_pos
    exact klDivergence_nonneg' P Q hQ_pos
  · intro n hn P Q hP_nonneg hQ_nonneg hP_sum hQ_sum hQ_pos
    exact stepLogLikelihood_sum_nonpos_via_gibbs (n := n) hn P Q hP_nonneg hQ_nonneg hP_sum hQ_sum hQ_pos

/-! ## Specialization: cylinder prediction distributions -/

namespace Solomonoff

open Mettapedia.Logic.SolomonoffPrior

namespace Prediction

/-- Gibbs' inequality for the normalized two-outcome cylinder prediction distributions of two machines.

This is the clean "infinite-domain" link: from a monotone machine's cylinder semimeasure, build
the next-bit distribution (conditioned on continuation), then apply the K&S KL gate.
-/
theorem klDivergence_normalizedNextBitDist_nonneg
    (U V : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hU : 0 < ∑ i : Fin 2, nextBitWeights U programs x i)
    (hV : 0 < ∑ i : Fin 2, nextBitWeights V programs x i)
    (hQ_pos :
      ∀ i,
        (normalizedNextBitDist U programs x hU).p i ≠ 0 → 0 < (normalizedNextBitDist V programs x hV).p i) :
    0 ≤
      klDivergence (normalizedNextBitDist U programs x hU) (normalizedNextBitDist V programs x hV) hQ_pos := by
  exact (gibbs_inequality_shared_gate).1 _ _ hQ_pos

end Prediction
end Solomonoff

/-! ## Example: normalize then apply the KL gate -/

/-- Example usage: a Solomonoff semimeasure, normalized on a finite domain, satisfies
Gibbs' inequality against itself (hence KL ≥ 0). -/
theorem solomonoff_normalize_kl_self_nonneg
    (sm : Mettapedia.Logic.SolomonoffPrior.Semimeasure)
    (s : Finset Mettapedia.Logic.SolomonoffPrior.BinString)
    (hsum_pos : 0 < Finset.sum s (fun x => sm.μ x)) :
    let P := Solomonoff.normalizeSemimeasureOnFinset sm s hsum_pos
    0 ≤
      klDivergence P P (fun i hi =>
        lt_of_le_of_ne (P.nonneg i) (by
          intro h0
          exact hi (by simpa [eq_comm] using h0))) := by
  intro P
  exact (gibbs_inequality_shared_gate).1 P P (fun i hi =>
    lt_of_le_of_ne (P.nonneg i) (by
      intro h0
      exact hi (by simpa [eq_comm] using h0)))

end Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges
