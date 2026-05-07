import KnuthSkilling.ShoreJohnson.AppendixTheoremI
import KnuthSkilling.ShoreJohnson.Bridge
import KnuthSkilling.ShoreJohnson.KL
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Shore–Johnson Appendix regularity: KL stationarity ⇒ minimizer

This file provides a **concrete discharge** of the Appendix-style "stationarity ⇒ minimizer"
regularity assumption for the KL/cross-entropy objective.

We work in the interior regime `p_i > 0` and `q_i > 0` where the gradient is well-defined, and we
use a standard Bregman / KL identity:

`D(q'‖p) = D(q‖p) + D(q'‖q) + Σ (q'_i - q_i) * log(q_i / p_i)`.

If `q` satisfies a Lagrange-multiplier stationarity condition for expected-value constraints, the
linear term vanishes on all feasible `q'`, leaving `D(q'‖q) ≥ 0` as the certificate of optimality.
-/

namespace KnuthSkilling.ShoreJohnson.AppendixKL

open Classical
open Real
open Finset BigOperators
open Filter
open scoped Topology

open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.AppendixTheoremI
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.KL
open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.Bridge

/-! ## KL gradient kernel -/

/-- The KL/cross-entropy coordinate kernel in log form: `gKL(w,u) = log(w/u)`.

**Boundary behavior (Lean conventions)**:
- `gKL 0 u = log(0/u) = log 0 = 0` (Lean: `log 0 = 0`)
- `gKL w 0 = log(w/0) = log 0 = 0` (Lean: `x/0 = 0`, `log 0 = 0`)

These are "junk values" outside the intended domain `w > 0`, `u > 0`. The main theorems
restrict to the positive regime where `gKL(w,u) = log(w) - log(u)` is well-defined.

**Relationship to klAtom**: `klAtom w u = w * gKL w u` for `w,u > 0`. -/
noncomputable def gKL (w u : ℝ) : ℝ :=
  Real.log (w / u)

/-! ### Boundary lemmas for `gKL` -/

lemma gKL_zero_left (u : ℝ) : gKL 0 u = 0 := by simp [gKL, zero_div, Real.log_zero]

lemma gKL_zero_right (w : ℝ) : gKL w 0 = 0 := by simp [gKL, div_zero, Real.log_zero]

lemma gKL_eq_log_div (w u : ℝ) : gKL w u = Real.log (w / u) := rfl

/-- On the positive domain, `gKL` decomposes as `log w - log u`. -/
lemma gKL_pos_pos (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    gKL w u = Real.log w - Real.log u := by
  simp [gKL, Real.log_div (ne_of_gt hw) (ne_of_gt hu)]

/-- Relationship between `gKL` and `klAtom` on the positive domain. -/
lemma klAtom_eq_mul_gKL (w u : ℝ) (_hw : 0 < w) (_hu : 0 < u) :
    klAtom w u = w * gKL w u := rfl

/-! ## Algebraic identities -/

lemma mul_log_div_sub_log_div_eq_mul_log_div {w u v : ℝ}
    (hw : 0 ≤ w) (hu : 0 < u) (hv : 0 < v) :
    w * (Real.log (w / u) - Real.log (v / u)) = w * Real.log (w / v) := by
  by_cases hw0 : w = 0
  · subst hw0
    simp
  · have hw' : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    -- Reduce to `log(w/u) - log(v/u) = log(w/v)` in the positive regime.
    have hpos_wu : 0 < w / u := div_pos hw' hu
    have hpos_vu : 0 < v / u := div_pos hv hu
    have hpos_wv : 0 < w / v := div_pos hw' hv
    -- Expand each log-div as `log w - log u`, etc.
    have h1 : Real.log (w / u) = Real.log w - Real.log u := by
      simpa [div_eq_mul_inv] using (Real.log_div (ne_of_gt hw') (ne_of_gt hu))
    have h2 : Real.log (v / u) = Real.log v - Real.log u := by
      simpa [div_eq_mul_inv] using (Real.log_div (ne_of_gt hv) (ne_of_gt hu))
    have h3 : Real.log (w / v) = Real.log w - Real.log v := by
      simpa [div_eq_mul_inv] using (Real.log_div (ne_of_gt hw') (ne_of_gt hv))
    -- Now it is linear algebra.
    simp [h1, h2, h3, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add]

lemma sum_mul_log_div_sub_log_div_eq_sum_mul_log_div {n : ℕ}
    (P Q R : ProbDist n)
    (hQpos : ∀ i, 0 < Q.p i)
    (hRpos : ∀ i, 0 < R.p i) :
    (∑ i : Fin n, P.p i * (Real.log (P.p i / R.p i) - Real.log (Q.p i / R.p i))) =
      ∑ i : Fin n, P.p i * Real.log (P.p i / Q.p i) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _
  have hPi : 0 ≤ P.p i := P.nonneg i
  have hQi : 0 < Q.p i := hQpos i
  have hRi : 0 < R.p i := hRpos i
  -- Apply the scalar identity at each coordinate.
  simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (mul_log_div_sub_log_div_eq_mul_log_div (w := P.p i) (u := R.p i) (v := Q.p i) hPi hRi hQi)

lemma sum_sub_mul_gKL_eq_zero_of_stationaryEV {n : ℕ}
    (p q q' : ProbDist n) (cs : EVConstraintSet n)
    (hq : q ∈ toConstraintSet cs) (hq' : q' ∈ toConstraintSet cs)
    (hstat : StationaryEV gKL p q cs) :
    (∑ i : Fin n, (q'.p i - q.p i) * gKL (q.p i) (p.p i)) = 0 := by
  classical
  rcases hstat with ⟨β, lam, hβ⟩
  -- Expand `gKL(q_i,p_i)` using stationarity.
  have hsum :
      (∑ i : Fin n, (q'.p i - q.p i) * gKL (q.p i) (p.p i)) =
        ∑ i : Fin n, (q'.p i - q.p i) * (β + ∑ k : Fin cs.length, lam k * (cs.get k).coeff i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    -- Avoid `simp` rewriting `a * b = a * c` into a disjunction; we just rewrite the kernel.
    simpa using congrArg (fun x => (q'.p i - q.p i) * x) (hβ i)
  -- Reduce to the stationarity-expanded sum.
  rw [hsum]
  -- Split into the `β` term and the constraint terms.
  have hsplit :
      (∑ i : Fin n, (q'.p i - q.p i) * (β + ∑ k : Fin cs.length, lam k * (cs.get k).coeff i)) =
        (∑ i : Fin n, (q'.p i - q.p i) * β) +
          ∑ i : Fin n, (q'.p i - q.p i) * (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) := by
    classical
    -- Expand `a * (β + s)` pointwise.
    calc
      (∑ i : Fin n, (q'.p i - q.p i) * (β + ∑ k : Fin cs.length, lam k * (cs.get k).coeff i)) =
          ∑ i : Fin n, ((q'.p i - q.p i) * β +
            (q'.p i - q.p i) * (∑ k : Fin cs.length, lam k * (cs.get k).coeff i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
      _ = (∑ i : Fin n, (q'.p i - q.p i) * β) +
            ∑ i : Fin n, (q'.p i - q.p i) * (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) := by
              simp [Finset.sum_add_distrib]
  -- `β * Σ(q' - q)` vanishes since both are distributions.
  have hsum_one : (∑ i : Fin n, (q'.p i - q.p i)) = 0 := by
    simp [Finset.sum_sub_distrib, q'.sum_one, q.sum_one]
  have hβterm : (∑ i : Fin n, (q'.p i - q.p i) * β) = 0 := by
    -- Pull out `β` on the right.
    have : (∑ i : Fin n, (q'.p i - q.p i) * β) = (∑ i : Fin n, (q'.p i - q.p i)) * β := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (q'.p i - q.p i)) (a := β)).symm
    simp [this, hsum_one]
  -- Each constraint term vanishes because `q` and `q'` satisfy the same constraints.
  have hk0 : ∀ k : Fin cs.length,
      (∑ i : Fin n, (q'.p i - q.p i) * (cs.get k).coeff i) = 0 := by
    intro k
    let c := cs.get k
    have hqk : satisfies c q := by
      exact hq c (List.get_mem cs k)
    have hq'k : satisfies c q' := by
      exact hq' c (List.get_mem cs k)
    -- Subtract the two equalities.
    dsimp [satisfies] at hqk hq'k
    have :
        (∑ i : Fin n, (q'.p i - q.p i) * c.coeff i) =
          (∑ i : Fin n, q'.p i * c.coeff i) - ∑ i : Fin n, q.p i * c.coeff i := by
      simp [Finset.sum_sub_distrib, sub_mul]
    rw [this]
    simp [hq'k, hqk]
  have hcterm :
      (∑ i : Fin n, (q'.p i - q.p i) * (∑ k : Fin cs.length, lam k * (cs.get k).coeff i)) = 0 := by
    classical
    -- Swap sums: first expand the inner sum.
    have hswap :
        (∑ i : Fin n, (q'.p i - q.p i) * (∑ k : Fin cs.length, lam k * (cs.get k).coeff i)) =
          ∑ k : Fin cs.length, lam k * (∑ i : Fin n, (q'.p i - q.p i) * (cs.get k).coeff i) := by
      -- Expand, commute, and factor `lam k`.
      calc
        (∑ i : Fin n, (q'.p i - q.p i) * (∑ k : Fin cs.length, lam k * (cs.get k).coeff i)) =
            ∑ i : Fin n, ∑ k : Fin cs.length, (q'.p i - q.p i) * (lam k * (cs.get k).coeff i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              -- Pull the outer factor into the finite sum over `k`.
              simp [Finset.mul_sum, mul_left_comm]
        _ = ∑ k : Fin cs.length, ∑ i : Fin n, (q'.p i - q.p i) * (lam k * (cs.get k).coeff i) := by
              -- Avoid `simp` loops: use the commutation lemma directly.
              simpa using (Finset.sum_comm :
                (∑ i : Fin n, ∑ k : Fin cs.length, (q'.p i - q.p i) * (lam k * (cs.get k).coeff i)) =
                  ∑ k : Fin cs.length, ∑ i : Fin n, (q'.p i - q.p i) * (lam k * (cs.get k).coeff i))
        _ = ∑ k : Fin cs.length, lam k * (∑ i : Fin n, (q'.p i - q.p i) * (cs.get k).coeff i) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              -- Factor `lam k` out of the sum over `i`.
              calc
                (∑ i : Fin n, (q'.p i - q.p i) * (lam k * (cs.get k).coeff i)) =
                    ∑ i : Fin n, lam k * ((q'.p i - q.p i) * (cs.get k).coeff i) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _
                      ring
                _ = lam k * (∑ i : Fin n, (q'.p i - q.p i) * (cs.get k).coeff i) := by
                      simp [Finset.mul_sum]
    -- Each inner sum is zero, so the whole weighted sum is zero.
    rw [hswap]
    refine Finset.sum_eq_zero ?_
    intro k _
    -- Avoid `simp` turning `a * b = 0` into a disjunction; rewrite the inner sum to `0` first.
    have hk : (∑ i : Fin n, (q'.p i - q.p i) * (cs.get k).coeff i) = 0 := hk0 k
    -- Now the goal is `lam k * 0 = 0`.
    -- Use `rw` (not `simp`) to ensure the rewrite happens before any `mul_eq_zero` lemmas fire.
    rw [hk]
    simp
  -- Combine the pieces.
  have :
      (∑ i : Fin n, (q'.p i - q.p i) * (β + ∑ k : Fin cs.length, lam k * (cs.get k).coeff i)) = 0 := by
    -- Avoid `simp` rewriting list indexing in ways that block rewriting by `hsplit`.
    rw [hsplit, hβterm, hcterm]
    simp
  exact this

/-! ## Stationary ⇒ minimizer for KL objective -/

theorem isMinimizer_ofAtom_klAtom_of_stationaryEV {n : ℕ}
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (q : ProbDist n) (hq : q ∈ toConstraintSet cs)
    (hqPos : ∀ i, 0 < q.p i)
    (hstat : StationaryEV gKL p q cs) :
    IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q := by
  refine ⟨hq, ?_⟩
  intro q' hq'
  -- Use the Bregman identity:
  --   D(q'‖p) = D(q‖p) + D(q'‖q) + Σ (q'_i - q_i) * log(q_i/p_i).
  have hBreg :
      (∑ i : Fin n, klAtom (q'.p i) (p.p i)) =
        (∑ i : Fin n, klAtom (q.p i) (p.p i)) +
          (∑ i : Fin n, klAtom (q'.p i) (q.p i)) +
          (∑ i : Fin n, (q'.p i - q.p i) * gKL (q.p i) (p.p i)) := by
    -- Work in the positive regime for `q` and `p`.
    have hpPos : ∀ i, 0 < p.p i := hp
    have hqPos' : ∀ i, 0 < q.p i := hqPos
    -- Core coordinatewise log identity: after multiplying by `q'`, subtraction of `log(·/p)`
    -- collapses to `log(·/q)`.
    have hlog :
        (∑ i : Fin n, q'.p i * (Real.log (q'.p i / p.p i) - Real.log (q.p i / p.p i))) =
          ∑ i : Fin n, q'.p i * Real.log (q'.p i / q.p i) := by
      simpa using
        (sum_mul_log_div_sub_log_div_eq_sum_mul_log_div (P := q') (Q := q) (R := p)
          (hQpos := hqPos') (hRpos := hpPos))
    -- First split `∑ q' log(q'/p)` into `∑ q' log(q/p)` plus the difference term.
    have hsplit₁ :
        (∑ i : Fin n, q'.p i * Real.log (q'.p i / p.p i)) =
          (∑ i : Fin n, q'.p i * Real.log (q.p i / p.p i)) +
            ∑ i : Fin n, q'.p i * (Real.log (q'.p i / p.p i) - Real.log (q.p i / p.p i)) := by
      classical
      calc
        (∑ i : Fin n, q'.p i * Real.log (q'.p i / p.p i)) =
            ∑ i : Fin n,
              (q'.p i * Real.log (q.p i / p.p i) +
                q'.p i * (Real.log (q'.p i / p.p i) - Real.log (q.p i / p.p i))) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ = (∑ i : Fin n, q'.p i * Real.log (q.p i / p.p i)) +
              ∑ i : Fin n, q'.p i * (Real.log (q'.p i / p.p i) - Real.log (q.p i / p.p i)) := by
              simp [Finset.sum_add_distrib]
    -- Replace the difference term using `hlog`.
    have hsplit₂ :
        (∑ i : Fin n, q'.p i * Real.log (q'.p i / p.p i)) =
          (∑ i : Fin n, q'.p i * Real.log (q.p i / p.p i)) +
            (∑ i : Fin n, q'.p i * Real.log (q'.p i / q.p i)) := by
      simpa [hsplit₁] using congrArg (fun x => (∑ i : Fin n, q'.p i * Real.log (q.p i / p.p i)) + x) hlog
    -- Rewrite `∑ q' log(q/p)` as `∑ q log(q/p)` plus `∑ (q' - q) log(q/p)`.
    have hsplit₃ :
        (∑ i : Fin n, q'.p i * Real.log (q.p i / p.p i)) =
          (∑ i : Fin n, q.p i * Real.log (q.p i / p.p i)) +
            ∑ i : Fin n, (q'.p i - q.p i) * Real.log (q.p i / p.p i) := by
      classical
      calc
        (∑ i : Fin n, q'.p i * Real.log (q.p i / p.p i)) =
            ∑ i : Fin n, (q.p i + (q'.p i - q.p i)) * Real.log (q.p i / p.p i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ = ∑ i : Fin n, (q.p i * Real.log (q.p i / p.p i) + (q'.p i - q.p i) * Real.log (q.p i / p.p i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ = (∑ i : Fin n, q.p i * Real.log (q.p i / p.p i)) +
              ∑ i : Fin n, (q'.p i - q.p i) * Real.log (q.p i / p.p i) := by
              simp [Finset.sum_add_distrib]
    -- Put the pieces together and return to `klAtom` / `gKL` notation.
    -- `klAtom w u = w * log(w/u)` and `gKL(w,u) = log(w/u)`.
    have :
        (∑ i : Fin n, q'.p i * Real.log (q'.p i / p.p i)) =
          (∑ i : Fin n, q.p i * Real.log (q.p i / p.p i)) +
            (∑ i : Fin n, q'.p i * Real.log (q'.p i / q.p i)) +
            (∑ i : Fin n, (q'.p i - q.p i) * Real.log (q.p i / p.p i)) := by
      -- Combine `hsplit₂` and `hsplit₃`.
      calc
        (∑ i : Fin n, q'.p i * Real.log (q'.p i / p.p i)) =
            (∑ i : Fin n, q'.p i * Real.log (q.p i / p.p i)) +
              (∑ i : Fin n, q'.p i * Real.log (q'.p i / q.p i)) := hsplit₂
        _ = (∑ i : Fin n, q.p i * Real.log (q.p i / p.p i)) +
              (∑ i : Fin n, (q'.p i - q.p i) * Real.log (q.p i / p.p i)) +
              (∑ i : Fin n, q'.p i * Real.log (q'.p i / q.p i)) := by
              simp [hsplit₃, add_assoc]
        _ = (∑ i : Fin n, q.p i * Real.log (q.p i / p.p i)) +
              (∑ i : Fin n, q'.p i * Real.log (q'.p i / q.p i)) +
              (∑ i : Fin n, (q'.p i - q.p i) * Real.log (q.p i / p.p i)) := by
              ac_rfl
    -- Finally, rewrite to the goal statement.
    simpa [klAtom, gKL, ofAtom, mul_assoc, add_assoc, add_left_comm, add_comm] using this
  -- Cancel the linear term using stationarity + feasibility.
  have hlin : (∑ i : Fin n, (q'.p i - q.p i) * gKL (q.p i) (p.p i)) = 0 :=
    sum_sub_mul_gKL_eq_zero_of_stationaryEV (p := p) (q := q) (q' := q') (cs := cs) hq hq' hstat
  -- Non-negativity of `D(q'‖q)` (requires `q` positive).
  have hnonneg :
      0 ≤ ∑ i : Fin n, klAtom (q'.p i) (q.p i) := by
    have hQpos : ∀ i, q'.p i ≠ 0 → 0 < q.p i := fun i _ => hqPos i
    -- Identify the sum with the project's KL divergence and reuse Gibbs' inequality.
    have hsum : (∑ i : Fin n, klAtom (q'.p i) (q.p i)) = klDivergence q' q hQpos := by
      simpa using sum_klAtom_eq_klDivergence (P := q') (Q := q) hQpos
    have : 0 ≤ klDivergence q' q hQpos := klDivergence_nonneg' (P := q') (Q := q) hQpos
    simpa [hsum] using this
  -- Conclude `D(q‖p) ≤ D(q'‖p)`.
  -- From `hBreg`: D(q') = D(q) + D(q'‖q) + 0.
  have hge :
      (∑ i : Fin n, klAtom (q.p i) (p.p i)) ≤ ∑ i : Fin n, klAtom (q'.p i) (p.p i) := by
    -- Rearranged inequality from `hBreg`.
    -- `D(q') = D(q) + D(q'‖q)`.
    have : (∑ i : Fin n, klAtom (q'.p i) (p.p i)) =
        (∑ i : Fin n, klAtom (q.p i) (p.p i)) + (∑ i : Fin n, klAtom (q'.p i) (q.p i)) := by
      simpa [hlin, add_assoc, add_left_comm, add_comm] using hBreg
    -- Now use `hnonneg`.
    linarith
  simpa [ofAtom] using hge

/-! ## Minimizer ⇒ StationaryEV for KL objective -/

namespace KLStationary

open scoped BigOperators

/-- Derivative of the KL atom in the positive regime. -/
lemma hasDerivAt_klAtom (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    HasDerivAt (fun x => klAtom x u) (Real.log (w / u) + 1) w := by
  -- Use `klAtom x u = x * log (x/u)` and differentiate by product/chain rule.
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hdiv : HasDerivAt (fun x => x / u) (1 / u) w := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id w).mul_const (u⁻¹)
  have hlog' : HasDerivAt Real.log ((w / u)⁻¹) (w / u) :=
    Real.hasDerivAt_log (ne_of_gt (div_pos hw hu))
  have hlogcomp : HasDerivAt (fun x => Real.log (x / u)) ((w / u)⁻¹ * (1 / u)) w := by
    have := hlog'.comp w hdiv
    simpa [Function.comp] using this
  -- Now product rule for `x * log(x/u)`.
  have hmul :
      HasDerivAt (fun x => x * Real.log (x / u))
        (Real.log (w / u) + w * ((w / u)⁻¹ * (1 / u))) w := by
    have hid : HasDerivAt (fun x => x) 1 w := hasDerivAt_id w
    have := hid.mul hlogcomp
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using this
  have hwcoef : w * (u / w * u⁻¹) = (1 : ℝ) := by
    calc
      w * (u / w * u⁻¹) = w * ((u * w⁻¹) * u⁻¹) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = (u * (w * w⁻¹)) * u⁻¹ := by
        ac_rfl
      _ = (u : ℝ) * u⁻¹ := by
        simp [hw0]
      _ = (1 : ℝ) := by
        simp [hu0]
  have hmul' :
      HasDerivAt (fun x => x * Real.log (x / u)) (Real.log (w / u) + 1) w := by
    -- `hmul` may have simplified the coefficient to `w * (u / w * u⁻¹)`.
    simpa [hwcoef] using hmul
  -- Rewrite in terms of `klAtom`.
  simpa [klAtom] using hmul'

/-- The linear functional (gradient) at `q` for the KL objective. -/
noncomputable def gradAt {n : ℕ} (p q : ProbDist n) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun v => ∑ i : Fin n, v i * (gKL (q.p i) (p.p i) + 1)
    map_add' := by
      intro v w
      classical
      simp [Finset.sum_add_distrib, add_mul, mul_add, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro c v
      classical
      -- Pull out the scalar from the finite sum.
      simp [Finset.mul_sum, mul_assoc] }

noncomputable def constraintForm {n : ℕ} (cs : EVConstraintSet n) :
    Option (Fin cs.length) → (Fin n → ℝ) →ₗ[ℝ] ℝ
  | none =>
      { toFun := fun v => ∑ i : Fin n, v i
        map_add' := by
          intro v w
          classical
          simp [Finset.sum_add_distrib]
        map_smul' := by
          intro c v
          classical
          simp [Finset.mul_sum] }
  | some k =>
      { toFun := fun v => ∑ i : Fin n, v i * (cs.get k).coeff i
        map_add' := by
          intro v w
          classical
          simp [Finset.sum_add_distrib, add_mul]
        map_smul' := by
          intro c v
          classical
          simp [Finset.mul_sum, mul_assoc] }

lemma constraintForm_none_apply {n : ℕ} (cs : EVConstraintSet n) (v : Fin n → ℝ) :
    constraintForm (n := n) cs none v = ∑ i : Fin n, v i := rfl

lemma constraintForm_some_apply {n : ℕ} (cs : EVConstraintSet n) (k : Fin cs.length) (v : Fin n → ℝ) :
    constraintForm (n := n) cs (some k) v = ∑ i : Fin n, v i * (cs.get k).coeff i := rfl

lemma gradAt_apply_single {n : ℕ} (p q : ProbDist n) (i : Fin n) :
    gradAt p q (Pi.single i (1 : ℝ) : Fin n → ℝ) = gKL (q.p i) (p.p i) + 1 := by
  classical
  -- Only `i` contributes in the sum.
  have :
      (∑ j : Fin n, ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) * (gKL (q.p j) (p.p j) + 1)) =
        (Pi.single i (1 : ℝ) : Fin n → ℝ) i * (gKL (q.p i) (p.p i) + 1) := by
    refine Fintype.sum_eq_single i ?_
    intro j hji
    simp [Pi.single, hji]
  simpa [gradAt, Pi.single, this] using this

lemma constraintForm_apply_single_none {n : ℕ} (cs : EVConstraintSet n) (i : Fin n) :
    constraintForm (n := n) cs none (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
  classical
  -- The sum of a standard basis vector is `1`.
  have :
      (∑ j : Fin n, ((Pi.single i (1 : ℝ) : Fin n → ℝ) j)) =
        (Pi.single i (1 : ℝ) : Fin n → ℝ) i := by
    refine Fintype.sum_eq_single i ?_
    intro j hji
    simp [Pi.single, hji]
  simpa [constraintForm_none_apply, Pi.single, this] using this

lemma constraintForm_apply_single_some {n : ℕ} (cs : EVConstraintSet n) (k : Fin cs.length) (i : Fin n) :
    constraintForm (n := n) cs (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ) = (cs.get k).coeff i := by
  classical
  have :
      (∑ j : Fin n, ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) * (cs.get k).coeff j) =
        (Pi.single i (1 : ℝ) : Fin n → ℝ) i * (cs.get k).coeff i := by
    refine Fintype.sum_eq_single i ?_
    intro j hji
    simp [Pi.single, hji]
  simpa [constraintForm_some_apply, this] using this

end KLStationary

open KLStationary

theorem stationaryEV_of_isMinimizer_ofAtom_klAtom {n : ℕ}
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs)
    (hqPos : ∀ i, 0 < q.p i)
    (hmin : IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q) :
    StationaryEV gKL p q cs := by
  classical
  -- Let `K` be the gradient linear form at `q`, and `L` the family of constraint linear forms.
  let K : (Fin n → ℝ) →ₗ[ℝ] ℝ := gradAt p q
  let L : Option (Fin cs.length) → (Fin n → ℝ) →ₗ[ℝ] ℝ := constraintForm (n := n) cs
  -- Show: every direction that preserves all constraints has zero first-order change.
  have hKer : (⨅ o, LinearMap.ker (L o)) ≤ LinearMap.ker K := by
    intro v hv
    -- Define the 1D perturbation curve.
    let qLine : ℝ → (Fin n → ℝ) := fun t => fun i => q.p i + t * v i
    let φLine : ℝ → ℝ := fun t => ∑ i : Fin n, klAtom (qLine t i) (p.p i)
    have hsumv : (∑ i : Fin n, v i) = 0 := by
      have hv0 : v ∈ LinearMap.ker (L none) := (Submodule.mem_iInf _).1 hv none
      -- `L none v = 0`.
      have : L none v = 0 := hv0
      simpa [L, constraintForm_none_apply] using this
    have hvCoeff : ∀ k : Fin cs.length, (∑ i : Fin n, v i * (cs.get k).coeff i) = 0 := by
      intro k
      have hvk : v ∈ LinearMap.ker (L (some k)) := (Submodule.mem_iInf _).1 hv (some k)
      have : L (some k) v = 0 := hvk
      simpa [L, constraintForm_some_apply] using this
    -- Show `φLine` has a local minimum at `0` using positivity + global optimality.
    have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Fin n, 0 < qLine t i := by
      -- Coordinatewise positivity persists for small `t`; use finiteness to combine.
      have hpos_i : ∀ i : Fin n, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < qLine t i := by
        intro i
        have hcont : Continuous (fun t : ℝ => qLine t i) := by
          -- `t ↦ q_i + t*v_i`.
          simpa [qLine] using (continuous_const.add (continuous_id.mul continuous_const))
        have h0 : 0 < qLine 0 i := by simpa [qLine] using hqPos i
        -- Preimage of `Ioi 0` is a neighborhood.
        have : ∀ᶠ t in 𝓝 (0 : ℝ), qLine t i ∈ Set.Ioi (0 : ℝ) :=
          hcont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h0)
        simpa [Set.mem_Ioi] using this
      -- Combine the finitely many `Eventually` statements.
      simpa using (Filter.eventually_all.2 hpos_i)
    have hloc : IsLocalMin φLine 0 := by
      -- Use the neighborhood where `qLine t` is a valid probability distribution satisfying `cs`.
      refine (hpos.mono ?_)
      intro t htpos
      -- Build a `ProbDist` from the positive vector `qLine t`.
      have ht_nonneg : ∀ i, 0 ≤ qLine t i := fun i => le_of_lt (htpos i)
      have ht_sum : (∑ i : Fin n, qLine t i) = 1 := by
        -- `∑ (q_i + t*v_i) = 1 + t*∑ v_i`.
        calc
          (∑ i : Fin n, qLine t i) = (∑ i : Fin n, q.p i) + t * (∑ i : Fin n, v i) := by
            simp [qLine, Finset.sum_add_distrib, Finset.mul_sum]
          _ = 1 + t * (∑ i : Fin n, v i) := by simp [q.sum_one]
          _ = 1 := by simp [hsumv]
      let qT : ProbDist n :=
        { p := fun i => qLine t i
          nonneg := ht_nonneg
          sum_one := ht_sum }
      have hqT_mem : qT ∈ toConstraintSet cs := by
        -- Each expected-value constraint stays satisfied because `v` is in every kernel.
        have hq_sat : satisfiesSet cs q := (mem_toConstraintSet cs q).1 hq
        have hsat : satisfiesSet cs qT := by
          intro c hc
          -- Choose an index `k` with `c = cs.get k`.
          obtain ⟨k, rfl⟩ := List.get_of_mem hc
          -- Expand the constraint sum at `qT` and compare to `q`.
          have hk : (∑ i : Fin n, v i * (cs.get k).coeff i) = 0 := hvCoeff k
          -- Use `q`'s satisfaction to pin the RHS.
          have hqk : satisfies (cs.get k) q := hq_sat (cs.get k) (List.get_mem cs k)
          dsimp [satisfies] at hqk
          -- Compute `satisfies` at `qT`.
          dsimp [satisfies]
          calc
            (∑ i : Fin n, qT.p i * (cs.get k).coeff i)
                = (∑ i : Fin n, q.p i * (cs.get k).coeff i) +
                    t * (∑ i : Fin n, v i * (cs.get k).coeff i) := by
                      simp [qT, qLine, Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]
            _ = (cs.get k).rhs + t * (∑ i : Fin n, v i * (cs.get k).coeff i) := by
              simp [hqk]
            _ = (cs.get k).rhs + t * 0 := by
              rw [hk]
            _ = (cs.get k).rhs := by
              simp
        exact (mem_toConstraintSet cs qT).2 hsat
      -- Apply global optimality.
      have hle := hmin.2 qT hqT_mem
      -- Rewrite as `φLine 0 ≤ φLine t`.
      -- At `t=0`, `qLine 0 = q`.
      have h0 : φLine 0 = ∑ i : Fin n, klAtom (q.p i) (p.p i) := by
        simp [φLine, qLine]
      have ht : φLine t = ∑ i : Fin n, klAtom (qT.p i) (p.p i) := by
        simp [φLine, qLine, qT]
      -- Now `hle` is exactly the inequality.
      simpa [ofAtom, h0, ht] using hle
    -- Differentiate `φLine` at `0`.
    have hderiv_i : ∀ i : Fin n,
        HasDerivAt (fun t : ℝ => klAtom (qLine t i) (p.p i))
          (v i * (gKL (q.p i) (p.p i) + 1)) 0 := by
      intro i
      -- Use chain rule with the derivative of `klAtom` at `q_i`.
      have hAff : HasDerivAt (fun t : ℝ => qLine t i) (v i) 0 := by
        -- derivative of `t ↦ q_i + t*v_i` is `v_i`.
        have ht : HasDerivAt (fun t : ℝ => t * v i) (v i) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).mul_const (v i)
        simpa [qLine] using ht.const_add (q.p i)
      have hkl : HasDerivAt (fun x => klAtom x (p.p i)) (gKL (q.p i) (p.p i) + 1) (q.p i) :=
        hasDerivAt_klAtom (w := q.p i) (u := p.p i) (hqPos i) (hp i)
      -- Compose and simplify.
      have hkl' :
          HasDerivAt (fun x => klAtom x (p.p i)) (gKL (q.p i) (p.p i) + 1) (qLine 0 i) := by
        simpa [qLine] using hkl
      simpa [Function.comp, qLine, gKL, mul_assoc, mul_left_comm, mul_comm] using
        (hkl'.comp (0 : ℝ) hAff)
    have hderiv :
        HasDerivAt φLine (∑ i : Fin n, v i * (gKL (q.p i) (p.p i) + 1)) 0 := by
      -- Derivative of a finite sum.
      simpa [φLine] using
        (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
          (A := fun i : Fin n => fun t : ℝ => klAtom (qLine t i) (p.p i))
          (A' := fun i : Fin n => v i * (gKL (q.p i) (p.p i) + 1))
          (x := (0 : ℝ))
          (by
            intro i hi
            simpa using hderiv_i i))
    -- Fermat: local min implies derivative 0.
    have : (∑ i : Fin n, v i * (gKL (q.p i) (p.p i) + 1)) = 0 := by
      exact hloc.hasDerivAt_eq_zero hderiv
    -- This is exactly the membership in `ker K`.
    have : K v = 0 := by
      simpa [K, gradAt, gKL, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, add_assoc,
        add_left_comm, add_comm] using this
    exact this
  -- Use linear algebra: `K` lies in the span of the constraint forms.
  have hKspan : K ∈ Submodule.span ℝ (Set.range L) :=
    mem_span_of_iInf_ker_le_ker (L := L) (K := K) hKer
  -- Extract coefficients `c`.
  rcases (Submodule.mem_span_range_iff_exists_fun ℝ).1 hKspan with ⟨c, hc⟩
  -- Use `c` to build the StationaryEV witness.
  refine ⟨c none - 1, fun k => c (some k), ?_⟩
  intro i
  -- Evaluate the linear identity `hc` on the basis vector `e_i`.
  have hci :=
    congrArg (fun (K' : (Fin n → ℝ) →ₗ[ℝ] ℝ) => K' (Pi.single i (1 : ℝ) : Fin n → ℝ)) hc
  -- Compute both sides.
  have hK :
      K (Pi.single i (1 : ℝ) : Fin n → ℝ) = gKL (q.p i) (p.p i) + 1 := by
    simp [K, gradAt_apply_single]
  -- The RHS is a sum of constraint forms.
  have hL :
      (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) =
        c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := by
    -- Split the sum over `Option` into `none` and `some`.
    classical
    -- Convert the `Option` sum to `none + sum some`.
    have hsum :
        (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) =
          c none * (L none (Pi.single i (1 : ℝ) : Fin n → ℝ)) +
            ∑ k : Fin cs.length, c (some k) * (L (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      -- Expand and use `Fintype.sum_option`.
      simp [Fintype.sum_option, Finset.sum_apply, LinearMap.smul_apply]
    -- Evaluate the constraint forms on the basis vector.
    have hnone : L none (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
      simp [L, constraintForm_apply_single_none]
    have hsome : ∀ k : Fin cs.length, L (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ) = (cs.get k).coeff i := by
      intro k
      simp [L, constraintForm_apply_single_some]
    -- Substitute.
    simp [hnone, hsome]
  -- Combine to solve for `gKL`.
  -- From `K(e_i) = ...` we get `gKL(q_i/p_i) = β + Σ lam_k*coeff`.
  -- We use `hci` with computed `hK` and `hL`.
  have : gKL (q.p i) (p.p i) + 1 = c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := by
    -- Avoid `simp` expanding the `Option` sum; rewrite in small steps.
    calc
      gKL (q.p i) (p.p i) + 1 = K (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        simpa using hK.symm
      _ = (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        simpa using hci.symm
      _ = c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := hL
  -- Rearrange constants.
  linarith

/-- **Key KL stationarity theorem**.

For the KL atom objective, first-order stationarity is equivalent to being a minimizer
on expected-value constraint sets (in the positive interior regime).

This theorem addresses the concern that `SJAppendixAssumptions.stationary_iff_isMinimizer_ofAtom`
is an *assumed* structure field. For KL specifically, the equivalence is DERIVED:
- Forward (stat → min): Via Bregman identity + non-negativity of KL divergence
- Backward (min → stat): Via Fermat's theorem + linear algebra on the constraint kernel

**Note on `SJAppendixAssumptions.ofKL`**: To fully construct an `SJAppendixAssumptions` instance
for KL, one also needs `F_shift2_deriv` showing the derivative has the form `scale * (g_i - g_j)`.
This is provable via `hasDerivAt_klAtom` and `hasDerivAt_ofAtom_shift2_coord`, but requires
connecting `shift2ProbClamp` (clamped curves) with the calculus infrastructure. The theorem
below is the core result that matters for the KL uniqueness story. -/
theorem stationaryEV_iff_isMinimizer_ofAtom_klAtom {n : ℕ}
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (q : ProbDist n) (hq : q ∈ toConstraintSet cs)
    (hqPos : ∀ i, 0 < q.p i) :
    StationaryEV gKL p q cs ↔ IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q := by
  constructor
  · intro hstat
    exact isMinimizer_ofAtom_klAtom_of_stationaryEV (p := p) hp (cs := cs) (q := q) hq hqPos hstat
  · intro hmin
    exact stationaryEV_of_isMinimizer_ofAtom_klAtom (p := p) hp (cs := cs) (q := q) hq hqPos hmin

end KnuthSkilling.ShoreJohnson.AppendixKL
