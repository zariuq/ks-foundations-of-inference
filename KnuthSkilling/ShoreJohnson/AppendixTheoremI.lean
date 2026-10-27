import KnuthSkilling.ShoreJohnson.AppendixMinimizer
import KnuthSkilling.ShoreJohnson.AppendixObjective
import KnuthSkilling.ShoreJohnson.Objective

/-!
# Separable stationarity certificates

A certificate supplies a coordinate-gradient formula and stationarity criteria
for the original objective and an atom sum. The resulting comparison theorem is
conditional on those certificates. The general affine calculus is proved in
`TheoremI`; its KL specialization constructs the concrete criteria.
-/

namespace KnuthSkilling.ShoreJohnson.AppendixTheoremI

open Classical

open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.AppendixMinimizer
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.Objective

/-! ## Pairwise coefficient equality and stationarity condition -/

def PairwiseCoeffEq {n : ℕ} (cs : EVConstraintSet n) (i j : Fin n) : Prop :=
  ∀ c ∈ cs, c.coeff i = c.coeff j

def GEqualOnCoeffs {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (cs : EVConstraintSet n) : Prop :=
  ∀ i j : Fin n, i ≠ j → PairwiseCoeffEq cs i j →
    g (q.p i) (p.p i) = g (q.p j) (p.p j)

/-!
`StationaryEV` is a Lean-friendly first-order condition for expected-value constraints:
there exist Lagrange multipliers such that the coordinate kernel `g(q_i,p_i)` is affine in the
constraint coefficient vectors.

This is the correct replacement for “all feasible shift2 derivatives vanish”, which is too weak
to characterize minimizers for general expected-value constraints.
-/

def StationaryEV {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (cs : EVConstraintSet n) : Prop :=
  ∃ (β : ℝ) (lam : Fin cs.length → ℝ),
    ∀ i : Fin n, g (q.p i) (p.p i) = β + ∑ k : Fin cs.length, (lam k) * (cs.get k).coeff i

/-- A Lagrange-stationary covector annihilates every feasible affine direction. -/
theorem stationaryEV_annihilates {n : ℕ} {g : ℝ → ℝ → ℝ} {p q : ProbDist n}
    {cs : EVConstraintSet n} (h : StationaryEV g p q cs) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) (hc : ∀ c ∈ cs, c.linearForm v = 0) :
    (∑ i, v i * g (q.p i) (p.p i)) = 0 := by
  obtain ⟨β, lam, he⟩ := h
  calc
    (∑ i, v i * g (q.p i) (p.p i)) =
        (∑ i, v i) * β + ∑ k : Fin cs.length, lam k * (cs.get k).linearForm v := by
      simp_rw [he, mul_add, Finset.sum_add_distrib]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_mul, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      simp only [EVConstraint.linearForm, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      rw [hv, zero_mul, zero_add]
      apply Finset.sum_eq_zero
      intro k _
      rw [hc _ (List.get_mem cs k), mul_zero]

theorem stationaryEV_feasible_difference {n : ℕ} {g : ℝ → ℝ → ℝ} {p q : ProbDist n}
    {cs : EVConstraintSet n} (h : StationaryEV g p q cs)
    (hq : q ∈ toConstraintSet cs) (q' : ProbDist n) (hq' : q' ∈ toConstraintSet cs) :
    (∑ i, (q'.p i - q.p i) * g (q.p i) (p.p i)) = 0 := by
  apply stationaryEV_annihilates h
  · simp [Finset.sum_sub_distrib, q'.sum_one, q.sum_one]
  · intro c hc
    change (∑ i, (q'.p i - q.p i) * c.coeff i) = 0
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hq' c hc).trans (hq c hc).symm)

theorem stationaryEV_add_const {n : ℕ} (g : ℝ → ℝ → ℝ) (a : ℝ)
    (p q : ProbDist n) (cs : EVConstraintSet n) :
    StationaryEV (fun x y => g x y + a) p q cs ↔ StationaryEV g p q cs := by
  constructor
  · rintro ⟨β, lam, he⟩
    refine ⟨β-a, lam, fun i => ?_⟩
    have := he i
    linarith
  · rintro ⟨β, lam, he⟩
    refine ⟨β+a, lam, fun i => ?_⟩
    have := he i
    linarith

theorem stationaryEV_const_mul {n : ℕ} {g : ℝ → ℝ → ℝ} {p q : ProbDist n}
    {cs : EVConstraintSet n} (h : StationaryEV g p q cs) (s : ℝ) :
    StationaryEV (fun x y => s * g x y) p q cs := by
  obtain ⟨β, lam, he⟩ := h
  refine ⟨s*β, fun k => s*lam k, fun i => ?_⟩
  dsimp only
  rw [he, mul_add, Finset.mul_sum]
  simp_rw [mul_assoc]

theorem stationaryEV_const_mul_iff {n : ℕ} (g : ℝ → ℝ → ℝ) (s : ℝ) (hs : s ≠ 0)
    (p q : ProbDist n) (cs : EVConstraintSet n) :
    StationaryEV (fun x y => s*g x y) p q cs ↔ StationaryEV g p q cs := by
  exact ⟨fun h => by simpa [mul_assoc, hs] using stationaryEV_const_mul h s⁻¹,
    fun h => stationaryEV_const_mul h s⟩

theorem gEqualOnCoeffs_of_stationaryEV {n : ℕ}
    {g : ℝ → ℝ → ℝ} {p q : ProbDist n} {cs : EVConstraintSet n}
    (h : StationaryEV g p q cs) :
    GEqualOnCoeffs g p q cs := by
  rcases h with ⟨β, lam, hβ⟩
  intro i j hij hcoeff
  have hi := hβ i
  have hj := hβ j
  -- The constraint sums agree since every coefficient agrees on `i` and `j`.
  have hsum :
      (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) =
        ∑ k : Fin cs.length, lam k * (cs.get k).coeff j := by
    refine Finset.sum_congr rfl ?_
    intro k _
    have hk : (cs.get k).coeff i = (cs.get k).coeff j := by
      -- `List.get` always yields an element of the list.
      exact hcoeff (cs.get k) (List.get_mem cs k)
    -- Rewrite the `i` coefficient to the `j` coefficient.
    rw [hk]
  -- Transport the equality through the `β + sum` representations.
  calc
    g (q.p i) (p.p i) = β + (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) := hi
    _ = β + (∑ k : Fin cs.length, lam k * (cs.get k).coeff j) := by rw [hsum]
    _ = g (q.p j) (p.p j) := hj.symm

/-! ## Appendix-style regularity/richness assumptions -/

structure SJAppendixAssumptions (F : ObjectiveFunctional) (d : ℝ → ℝ → ℝ) where
  /-- Coordinate kernel in the Appendix-style gradient representation. -/
  g : ℝ → ℝ → ℝ
  /-- (Optional bookkeeping) a scalar multiplier depending on `(p,q)` but not on coordinates,
  matching Shore–Johnson’s projected-gradient discussion. -/
  scale : ∀ {n : ℕ}, ProbDist n → ProbDist n → ℝ
  /-- The multiplier is never zero (so it can be cancelled). -/
  scale_ne : ∀ {n : ℕ} (p q : ProbDist n), scale p q ≠ 0
  /-- Shift2 derivative for the objective `F` (Appendix A1, *difference* form). -/
  F_shift2_deriv :
    ∀ {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j),
      (∀ k, 0 < p.p k) → (∀ k, 0 < q.p k) →
      HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p)
        (scale p q * (g (q.p i) (p.p i) - g (q.p j) (p.p j))) (q.p i)
  /-- Certificate: for expected-value constraint sets, first-order stationarity
  is equivalent to being a minimizer of `F`. -/
  stationary_iff_isMinimizer_F :
    ∀ {n : ℕ} (p : ProbDist n) (_hp : ∀ i, 0 < p.p i)
      (cs : EVConstraintSet n) (q : ProbDist n),
      q ∈ toConstraintSet cs →
      (∀ i, 0 < q.p i) →
        (StationaryEV g p q cs ↔ IsMinimizer F p (toConstraintSet cs) q)
  /-- Same stationarity characterization for the sum-form objective `ofAtom d`. -/
  stationary_iff_isMinimizer_ofAtom :
    ∀ {n : ℕ} (p : ProbDist n) (_hp : ∀ i, 0 < p.p i)
      (cs : EVConstraintSet n) (q : ProbDist n),
      q ∈ toConstraintSet cs →
      (∀ i, 0 < q.p i) →
        (StationaryEV g p q cs ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q)

/-! ## From Appendix shift2 calculus to equal-coordinate kernels -/

theorem gEqualOnCoeffs_of_isMinimizer_F {F : ObjectiveFunctional} {d : ℝ → ℝ → ℝ}
    (h : SJAppendixAssumptions F d) {n : ℕ} (p q : ProbDist n) (cs : EVConstraintSet n)
    (hp : ∀ k, 0 < p.p k) (hqPos : ∀ k, 0 < q.p k)
    (hq : IsMinimizer F p (toConstraintSet cs) q) {i j : Fin n} (hij : i ≠ j)
    (hcoeff : PairwiseCoeffEq cs i j) :
    h.g (q.p i) (p.p i) = h.g (q.p j) (p.p j) := by
  -- Apply Fermat along the feasible `shift2ProbClamp` curve.
  have hDeriv :=
    h.F_shift2_deriv (p := p) (q := q) (i := i) (j := j) hij hp hqPos
  have hzero :
      h.scale p q * (h.g (q.p i) (p.p i) - h.g (q.p j) (p.p j)) = 0 := by
    exact
      hasDerivAt_D_eq_zero_of_isMinimizer_shift2ProbClamp
        (F := F) (p := p) (q := q) (cs := cs) hq (i := i) (j := j) hij hcoeff
        (r := h.scale p q * (h.g (q.p i) (p.p i) - h.g (q.p j) (p.p j))) hDeriv
  -- Cancel the nonzero scale factor.
  have hsub :
      h.g (q.p i) (p.p i) - h.g (q.p j) (p.p j) = 0 := by
    rcases mul_eq_zero.1 hzero with hscale0 | hdiff
    · exact False.elim (h.scale_ne p q hscale0)
    · exact hdiff
  exact sub_eq_zero.1 hsub

/-! ## Consequences: `F` and `ofAtom d` agree on *positive* minimizers -/

theorem isMinimizer_iff_isMinimizer_ofAtom_of_pos
    {F : ObjectiveFunctional} {d : ℝ → ℝ → ℝ} (h : SJAppendixAssumptions F d)
    {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (q : ProbDist n)
    (hq : q ∈ toConstraintSet cs) (hqPos : ∀ i, 0 < q.p i) :
    IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q := by
  have hF : StationaryEV h.g p q cs ↔ IsMinimizer F p (toConstraintSet cs) q :=
    h.stationary_iff_isMinimizer_F (p := p) hp (cs := cs) (q := q) hq hqPos
  have hAtom : StationaryEV h.g p q cs ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q :=
    h.stationary_iff_isMinimizer_ofAtom (p := p) hp (cs := cs) (q := q) hq hqPos
  exact hF.symm.trans hAtom

end KnuthSkilling.ShoreJohnson.AppendixTheoremI
