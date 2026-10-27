import KnuthSkilling.ShoreJohnson.TheoremI
import KnuthSkilling.ShoreJohnson.Bridge
import KnuthSkilling.ShoreJohnson.KL
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# KL: convexity, stationarity and the exact optimality gap

The real atom is used only with positive reference masses. Zero source entries
are allowed. Extended KL outside this domain belongs to the measure-theoretic
bridge, not to the total-real logarithm used for differentiation.

The affine stationarity argument is shared with arbitrary convex objectives.
For KL the remaining gap is itself a KL divergence, giving an independent
certificate of global optimality.
-/
namespace KnuthSkilling.ShoreJohnson.AppendixKL
open Classical Real Finset
open scoped BigOperators
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.AppendixTheoremI
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.KL
open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.TheoremI
open KnuthSkilling.ShoreJohnson.Bridge

/-- The log-ratio covector; its boundary values are not analytic derivatives. -/
noncomputable def gKL (w u : ℝ) : ℝ := Real.log (w/u)
lemma gKL_zero_left (u : ℝ) : gKL 0 u = 0 := by simp [gKL]
lemma gKL_zero_right (w : ℝ) : gKL w 0 = 0 := by simp [gKL]
lemma gKL_eq_log_div (w u : ℝ) : gKL w u = Real.log (w/u) := rfl
lemma gKL_pos_pos (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    gKL w u = Real.log w - Real.log u := Real.log_div hw.ne' hu.ne'
lemma klAtom_eq_mul_gKL (w u : ℝ) (_hw : 0 < w) (_hu : 0 < u) :
    klAtom w u = w*gKL w u := rfl

/-- The zero source case is retained in the continuous real extension. -/
lemma klAtom_eq_mul_log_sub (w u : ℝ) (hu : 0 < u) :
    klAtom w u = w*Real.log w - w*Real.log u := by
  by_cases hw : w = 0
  · simp [hw, klAtom]
  · rw [klAtom, Real.log_div hw hu.ne', mul_sub]

/-- Homogeneity is an algebraic identity for the total-real atom. Probability
applications separately require nonnegative mixture coefficients. -/
theorem klAtom_scale (c w u : ℝ) : klAtom (c*w) (c*u) = c*klAtom w u := by
  by_cases hc : c = 0
  · simp [hc, klAtom]
  · simp only [klAtom, mul_div_mul_left _ _ hc]
    ring

theorem strictConvexOn_klAtom (u : ℝ) (hu : 0 < u) :
    StrictConvexOn ℝ (Set.Ici 0) (fun w => klAtom w u) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have h := Real.strictConvexOn_mul_log.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  simp_rw [klAtom_eq_mul_log_sub _ u hu]
  nlinarith

lemma mul_log_div_sub_log_div_eq_mul_log_div {w u v : ℝ}
    (_hw : 0 ≤ w) (hu : 0 < u) (hv : 0 < v) :
    w*(Real.log (w/u) - Real.log (v/u)) = w*Real.log (w/v) := by
  rw [mul_sub]
  change klAtom w u - w*gKL v u = klAtom w v
  rw [klAtom_eq_mul_log_sub w u hu, klAtom_eq_mul_log_sub w v hv,
    gKL_pos_pos v u hv hu]
  ring

lemma sum_mul_log_div_sub_log_div_eq_sum_mul_log_div {n : ℕ}
    (P Q R : ProbDist n) (hQpos : ∀ i, 0 < Q.p i) (hRpos : ∀ i, 0 < R.p i) :
    (∑ i, P.p i*(Real.log (P.p i/R.p i) - Real.log (Q.p i/R.p i))) =
      ∑ i, P.p i*Real.log (P.p i/Q.p i) :=
  Finset.sum_congr rfl fun i _ =>
    mul_log_div_sub_log_div_eq_mul_log_div (P.nonneg i) (hRpos i) (hQpos i)

lemma sum_sub_mul_gKL_eq_zero_of_stationaryEV {n : ℕ}
    (p q q' : ProbDist n) (cs : EVConstraintSet n)
    (hq : q ∈ toConstraintSet cs) (hq' : q' ∈ toConstraintSet cs)
    (hs : StationaryEV gKL p q cs) :
    (∑ i, (q'.p i-q.p i)*gKL (q.p i) (p.p i)) = 0 :=
  stationaryEV_feasible_difference hs hq q' hq'

/-- The exact three-point identity retains the competing posterior, not merely its support. -/
theorem kl_optimality_gap {n : ℕ} (p q r : ProbDist n)
    (hp : ∀ i, 0 < p.p i) (hq : ∀ i, 0 < q.p i) :
    (∑ i, klAtom (r.p i) (p.p i)) =
      (∑ i, klAtom (q.p i) (p.p i)) + (∑ i, klAtom (r.p i) (q.p i)) +
        ∑ i, (r.p i-q.p i)*gKL (q.p i) (p.p i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [klAtom_eq_mul_log_sub _ _ (hp i), klAtom_eq_mul_log_sub _ _ (hp i),
    klAtom_eq_mul_log_sub _ _ (hq i), gKL_pos_pos _ _ (hq i) (hp i)]
  ring

namespace KLStationary
lemma hasDerivAt_klAtom (w u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    HasDerivAt (fun t => klAtom t u) (gKL w u + 1) w := by
  have h := (Real.hasDerivAt_mul_log hw.ne').sub ((hasDerivAt_id w).mul_const (Real.log u))
  have he : (fun t => klAtom t u) = (fun t => t*Real.log t - t*Real.log u) :=
    funext fun t => klAtom_eq_mul_log_sub t u hu
  rw [he]
  convert h using 1 <;> first | rfl | (rw [gKL_pos_pos w u hw hu]; ring)

/-- The general affine Fermat theorem specializes to KL; normalization absorbs `+1`. -/
theorem stationaryEV_of_isMinimizer_ofAtom_klAtom {n : ℕ}
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i)
    (hm : IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q) : StationaryEV gKL p q cs :=
  (stationaryEV_add_const gKL 1 p q cs).mp
    (stationaryEV_of_isMinimizer_ofAtom_general klAtom (fun x y => gKL x y + 1)
      hasDerivAt_klAtom p hp cs q hq hpos hm)
end KLStationary

theorem isMinimizer_ofAtom_klAtom_of_stationaryEV {n : ℕ}
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i)
    (hs : StationaryEV gKL p q cs) : IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q :=
  isMinimizer_ofAtom_of_stationaryEV_convex klAtom (fun x y => gKL x y + 1)
    (fun u hu => (strictConvexOn_klAtom u hu).convexOn) KLStationary.hasDerivAt_klAtom
    p hp cs q hq hpos ((stationaryEV_add_const gKL 1 p q cs).mpr hs)

theorem stationaryEV_iff_isMinimizer_ofAtom_klAtom {n : ℕ}
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i) :
    StationaryEV gKL p q cs ↔ IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q :=
  ⟨isMinimizer_ofAtom_klAtom_of_stationaryEV p hp cs q hq hpos,
    KLStationary.stationaryEV_of_isMinimizer_ofAtom_klAtom p hp cs q hq hpos⟩
end KnuthSkilling.ShoreJohnson.AppendixKL
