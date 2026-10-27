import KnuthSkilling.Information.InformationEntropy
import KnuthSkilling.Variational.Main
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shore–Johnson “Dirac extraction” → log form on probabilities

This file isolates one Lean-friendly core lemma from Shore–Johnson (1980):

Assuming **sum-level additivity over product distributions**, Dirac delta test distributions force
the **multiplicative Cauchy equation** for `g(q) := d(1, q)`.

We then solve that equation on the probability domain `0 < q ≤ 1` under a minimal regularity gate
(measurability), obtaining `g(q) = C * log q` on that domain.

This is the piece most relevant for comparing Shore–Johnson’s “system independence” intuition with
K&S Appendix C / Path B functional-equation arguments.

This file does **not** attempt a full formalization of Shore–Johnson Theorem 1 (KL uniqueness).
-/

namespace KnuthSkilling.ShoreJohnson.Proof

open Real Finset BigOperators
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.Variational

/-! ## Product distributions on `Fin n × Fin m` -/

/-- A probability distribution on a product space `Fin n × Fin m`. -/
structure ProbDistProd (n m : ℕ) where
  p : Fin n × Fin m → ℝ
  nonneg : ∀ ij, 0 ≤ p ij
  sum_one : ∑ ij : Fin n × Fin m, p ij = 1

/-- The product of two distributions: `(P⊗Q)(i,j) = P(i)·Q(j)`. -/
noncomputable def productDist {n m : ℕ} (P : ProbDist n) (Q : ProbDist m) : ProbDistProd n m where
  p := fun ij => P.p ij.1 * Q.p ij.2
  nonneg := fun ij => mul_nonneg (P.nonneg ij.1) (Q.nonneg ij.2)
  sum_one := by
    have h :
        (∑ ij : Fin n × Fin m, P.p ij.1 * Q.p ij.2) = ∑ i : Fin n, ∑ j : Fin m, P.p i * Q.p j := by
      rw [Fintype.sum_prod_type]
    rw [h]
    calc
      ∑ i : Fin n, ∑ j : Fin m, P.p i * Q.p j
          = ∑ i : Fin n, P.p i * (∑ j : Fin m, Q.p j) := by
              congr 1; ext i; rw [Finset.mul_sum]
      _ = ∑ i : Fin n, P.p i * 1 := by rw [Q.sum_one]
      _ = ∑ i : Fin n, P.p i := by simp
      _ = 1 := P.sum_one

notation:70 P " ⊗ " Q => productDist P Q

/-! ## Dirac delta distributions -/

/-- Dirac delta distribution: all mass on position `a`. -/
def diracDist {n : ℕ} [NeZero n] (a : Fin n) : ProbDist n where
  p := fun i => if i = a then 1 else 0
  nonneg := fun i => by
    split_ifs <;> norm_num
  sum_one := by
    classical
    simp [Finset.sum_ite_eq', Finset.mem_univ]

@[simp] theorem diracDist_at_self {n : ℕ} [NeZero n] (a : Fin n) : (diracDist a).p a = 1 := by
  simp [diracDist]

@[simp] theorem diracDist_at_other {n : ℕ} [NeZero n] (a b : Fin n) (h : b ≠ a) :
    (diracDist a).p b = 0 := by
  simp [diracDist, h]

/-! ## Dirac extraction: sum-additivity ⇒ multiplicative Cauchy for `d(1, ·)` -/

/-- A divergence atom function is regular if `d(0, x) = 0` for all `x`. -/
def RegularAtom (d : ℝ → ℝ → ℝ) : Prop :=
  ∀ x : ℝ, d 0 x = 0

/-- A Dirac source selects one coordinate; only zero-source regularity is used. -/
theorem sum_dirac_atom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℝ → ℝ → ℝ) (hReg : RegularAtom d) (a : ι) (u : ι → ℝ) :
    (∑ i, d (if i = a then 1 else 0) (u i)) = d 1 (u a) := by
  have he (i : ι) : d (if i = a then 1 else 0) (u i) = if i = a then d 1 (u i) else 0 := by
    by_cases hi : i = a
    · simp [hi]
    · simpa only [if_neg hi] using hReg (u i)
  simp_rw [he]
  simp

/-- Extract the coordinate equation from the particular product equality being tested. -/
theorem dirac_extraction_at (d : ℝ → ℝ → ℝ) (hReg : RegularAtom d)
    {n m : ℕ} [NeZero n] [NeZero m] (a : Fin n) (b : Fin m)
    (Q : ProbDist n) (S : ProbDist m)
    (h : (∑ ij, d ((diracDist a ⊗ diracDist b).p ij) ((Q ⊗ S).p ij)) =
      (∑ i, d ((diracDist a).p i) (Q.p i)) + ∑ j, d ((diracDist b).p j) (S.p j)) :
    d 1 (Q.p a * S.p b) = d 1 (Q.p a) + d 1 (S.p b) := by
  have hp (ij : Fin n × Fin m) : (diracDist a ⊗ diracDist b).p ij =
      if ij = (a,b) then 1 else 0 := by
    rcases ij with ⟨i,j⟩
    by_cases hi : i = a <;> by_cases hj : j = b <;> simp [productDist, diracDist, hi, hj]
  simp_rw [hp] at h
  change (∑ ij, d (if ij = (a,b) then 1 else 0) ((Q ⊗ S).p ij)) =
    (∑ i, d (if i = a then 1 else 0) (Q.p i)) + ∑ j, d (if j = b then 1 else 0) (S.p j) at h
  rw [sum_dirac_atom d hReg, sum_dirac_atom d hReg, sum_dirac_atom d hReg] at h
  exact h

theorem dirac_extraction_cauchy
    (d : ℝ → ℝ → ℝ)
    (hd_reg : RegularAtom d)
    (hAdd :
      ∀ {n m : ℕ} [NeZero n] [NeZero m], ∀ P Q : ProbDist n, ∀ R S : ProbDist m,
        (∑ ij : Fin n × Fin m, d ((P ⊗ R).p ij) ((Q ⊗ S).p ij)) =
          (∑ i : Fin n, d (P.p i) (Q.p i)) + (∑ j : Fin m, d (R.p j) (S.p j)))
    {n m : ℕ} [NeZero n] [NeZero m]
    (a : Fin n) (b : Fin m) (Q : ProbDist n) (S : ProbDist m)
    (_hQa : 0 < Q.p a) (_hSb : 0 < S.p b) :
    d 1 (Q.p a * S.p b) = d 1 (Q.p a) + d 1 (S.p b) := by
  exact dirac_extraction_at d hd_reg a b Q S (hAdd (diracDist a) Q (diracDist b) S)

/-! ## Binary test distributions -/

/-- A probability distribution on `Fin 2` with probability `q` at position 0. -/
def binaryDist (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : ProbDist 2 where
  p := fun i => if i = 0 then q else 1 - q
  nonneg := fun i => by
    split_ifs with h
    · exact hq0
    · linarith
  sum_one := by
    have h1ne0 : (1 : Fin 2) ≠ 0 := by decide
    simp only [Fin.sum_univ_two, ↓reduceIte, h1ne0]
    ring

@[simp] theorem binaryDist_at_zero (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (binaryDist q hq0 hq1).p 0 = q := by
  simp [binaryDist]

@[simp] theorem binaryDist_at_one (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (binaryDist q hq0 hq1).p 1 = 1 - q := by
  simp [binaryDist]

/-! ## Cauchy on `(0,1]` and measurable solutions -/

theorem dirac_extraction_cauchy_Ioc
    (d : ℝ → ℝ → ℝ)
    (hReg : RegularAtom d)
    (hAdd :
      ∀ {n m : ℕ} [NeZero n] [NeZero m], ∀ P Q : ProbDist n, ∀ R S : ProbDist m,
        (∑ ij : Fin n × Fin m, d ((P ⊗ R).p ij) ((Q ⊗ S).p ij)) =
          (∑ i : Fin n, d (P.p i) (Q.p i)) + (∑ j : Fin m, d (R.p j) (S.p j))) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₁ ≤ 1 → 0 < q₂ → q₂ ≤ 1 → d 1 (q₁ * q₂) = d 1 q₁ + d 1 q₂ := by
  intro q₁ q₂ hq₁_pos hq₁_le1 hq₂_pos hq₂_le1
  have hq₁_nonneg : 0 ≤ q₁ := le_of_lt hq₁_pos
  have hq₂_nonneg : 0 ≤ q₂ := le_of_lt hq₂_pos
  have h := dirac_extraction_cauchy d hReg hAdd (n := 2) (m := 2) 0 0
      (binaryDist q₁ hq₁_nonneg hq₁_le1)
      (binaryDist q₂ hq₂_nonneg hq₂_le1)
      hq₁_pos hq₂_pos
  simpa using h

theorem mul_cauchy_Ioc_eq_const_mul_log
    (g : ℝ → ℝ)
    (hMul : ∀ q₁ q₂ : ℝ, 0 < q₁ → q₁ ≤ 1 → 0 < q₂ → q₂ ≤ 1 → g (q₁ * q₂) = g q₁ + g q₂)
    (hMeas : Measurable g) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → g q = C * log q := by
  -- Log-coordinates on `q ∈ (0,1]` via `q = exp (-t)` with `t ≥ 0`.
  let φ : ℝ → ℝ := fun t => g (Real.exp (-t))

  have hφ_meas : Measurable φ := by
    have : Measurable (fun t : ℝ => Real.exp (-t)) :=
      (measurable_neg : Measurable fun t : ℝ => -t).exp
    exact hMeas.comp this

  have hφ_add_nonneg :
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → φ (x + y) = φ x + φ y := by
    intro x y hx hy
    have hx_pos : 0 < Real.exp (-x) := by simpa using Real.exp_pos (-x)
    have hy_pos : 0 < Real.exp (-y) := by simpa using Real.exp_pos (-y)
    have hx_le1 : Real.exp (-x) ≤ 1 := by
      have : -x ≤ 0 := by linarith
      simpa [Real.exp_zero] using (Real.exp_le_exp.mpr this)
    have hy_le1 : Real.exp (-y) ≤ 1 := by
      have : -y ≤ 0 := by linarith
      simpa [Real.exp_zero] using (Real.exp_le_exp.mpr this)
    have hMul' := hMul (Real.exp (-x)) (Real.exp (-y)) hx_pos hx_le1 hy_pos hy_le1
    have harg : -(x + y) = (-x) + (-y) := by ring
    have hexp : Real.exp (-(x + y)) = Real.exp (-x) * Real.exp (-y) := by
      simpa [harg] using (Real.exp_add (-x) (-y))
    dsimp [φ]
    rw [hexp]
    exact hMul'

  -- Extend additivity from `t ≥ 0` to all `ℝ` by odd reflection.
  let ψ : ℝ → ℝ := fun t => if 0 ≤ t then φ t else -φ (-t)

  have hψ_meas : Measurable ψ := by
    have hset : MeasurableSet {t : ℝ | 0 ≤ t} := measurableSet_Ici
    have hnegφ : Measurable fun t : ℝ => -φ (-t) := by
      exact (hφ_meas.comp (measurable_neg : Measurable fun t : ℝ => -t)).neg
    exact Measurable.ite hset hφ_meas hnegφ

  have hψ_add : CauchyEquation ψ := by
    intro x y
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · have hxy : 0 ≤ x + y := add_nonneg hx hy
        simp [ψ, hx, hy, hxy, hφ_add_nonneg x y hx hy]
      · have hylt : y < 0 := lt_of_not_ge hy
        by_cases hxy : 0 ≤ x + y
        · -- x ≥ 0, y < 0, x+y ≥ 0
          have h' := hφ_add_nonneg (x + y) (-y) hxy (by linarith)
          have hxy_eq : (x + y) + (-y) = x := by abel
          have hsum : φ (x + y) + φ (-y) = φ x := by
            simpa [hxy_eq] using h'.symm
          have : φ (x + y) = φ x - φ (-y) := eq_sub_of_add_eq hsum
          simp [ψ, hx, hy, hxy, this, sub_eq_add_neg]
        · -- x ≥ 0, y < 0, x+y < 0
          have hxylt : x + y < 0 := lt_of_not_ge hxy
          have hxlt : x < -y := by linarith
          have hsub_nonneg : 0 ≤ (-y) - x := sub_nonneg.mpr (le_of_lt hxlt)
          have h' := hφ_add_nonneg x ((-y) - x) hx hsub_nonneg
          have hx_eq : x + ((-y) - x) = -y := by abel
          have hsum : φ (-y) = φ x + φ ((-y) - x) := by simpa [hx_eq] using h'
          have hsum' : φ x + φ (-(x + y)) = φ (-y) := by
            have : (-(x + y)) = (-y) - x := by ring
            simpa [this] using hsum.symm
          have hsum'' : φ (-(x + y)) + φ x = φ (-y) := by
            simpa [add_comm, add_left_comm, add_assoc] using hsum'
          have hφ_neg : φ (-(x + y)) = φ (-y) - φ x := eq_sub_of_add_eq hsum''
          have hφ_neg' : φ (-y + -x) = φ (-y) - φ x := by
            have h2 : -y + -x = -(x + y) := by ring
            calc
              φ (-y + -x) = φ (-(x + y)) := congrArg φ h2
              _ = φ (-y) - φ x := hφ_neg
          simp [ψ, hx, hy, hxy]
          rw [hφ_neg']
          ring_nf
    · have hxlt : x < 0 := lt_of_not_ge hx
      by_cases hy : 0 ≤ y
      · by_cases hxy : 0 ≤ x + y
        · -- x < 0, y ≥ 0, x+y ≥ 0
          have h' := hφ_add_nonneg (x + y) (-x) hxy (by linarith)
          have hxy_eq : (x + y) + (-x) = y := by abel
          have hsum : φ (x + y) + φ (-x) = φ y := by
            simpa [hxy_eq] using h'.symm
          have : φ (x + y) = φ y - φ (-x) := eq_sub_of_add_eq hsum
          simp [ψ, hx, hy, hxy, this, sub_eq_add_neg, add_comm]
        · -- x < 0, y ≥ 0, x+y < 0
          have hxylt : x + y < 0 := lt_of_not_ge hxy
          have hylt : y < -x := by linarith
          have hsub_nonneg : 0 ≤ (-x) - y := sub_nonneg.mpr (le_of_lt hylt)
          have h' := hφ_add_nonneg y ((-x) - y) hy hsub_nonneg
          have hy_eq : y + ((-x) - y) = -x := by abel
          have hsum : φ (-x) = φ y + φ ((-x) - y) := by simpa [hy_eq] using h'
          have hsum' : φ y + φ (-(x + y)) = φ (-x) := by
            have : (-(x + y)) = (-x) - y := by ring
            simpa [this] using hsum.symm
          have hsum'' : φ (-(x + y)) + φ y = φ (-x) := by
            simpa [add_comm, add_left_comm, add_assoc] using hsum'
          have hφ_neg : φ (-(x + y)) = φ (-x) - φ y := eq_sub_of_add_eq hsum''
          have hφ_neg' : φ (-y + -x) = φ (-x) - φ y := by
            have h2 : -y + -x = -(x + y) := by ring
            calc
              φ (-y + -x) = φ (-(x + y)) := congrArg φ h2
              _ = φ (-x) - φ y := hφ_neg
          simp [ψ, hx, hy, hxy]
          rw [hφ_neg']
          ring_nf
      · -- x < 0, y < 0
        have hylt : y < 0 := lt_of_not_ge hy
        have hxylt : x + y < 0 := by linarith
        have hx' : 0 ≤ -x := le_of_lt (neg_pos.mpr hxlt)
        have hy' : 0 ≤ -y := le_of_lt (neg_pos.mpr hylt)
        have h' := hφ_add_nonneg (-x) (-y) hx' hy'
        simp [ψ, hx, hy, hxylt, h', add_comm]

  obtain ⟨A, hA⟩ := cauchyEquation_measurable_linear ψ hψ_add hψ_meas

  refine ⟨-A, ?_⟩
  intro q hq_pos hq_le1
  have hlog_le : log q ≤ 0 := by
    have := Real.log_le_log hq_pos hq_le1
    simpa using this
  have ht : 0 ≤ -log q := by linarith
  have hψ_nonneg : ψ (-log q) = φ (-log q) := by simp [ψ, ht]
  have hφ_val : φ (-log q) = g q := by
    dsimp [φ]
    simp [Real.exp_log hq_pos]
  calc
    g q = φ (-log q) := by simp [hφ_val]
    _ = ψ (-log q) := by simp [hψ_nonneg]
    _ = A * (-log q) := hA (-log q)
    _ = (-A) * log q := by ring

theorem dirac_extraction_log_of_measurable
    (d : ℝ → ℝ → ℝ)
    (hReg : RegularAtom d)
    (hAdd :
      ∀ {n m : ℕ} [NeZero n] [NeZero m], ∀ P Q : ProbDist n, ∀ R S : ProbDist m,
        (∑ ij : Fin n × Fin m, d ((P ⊗ R).p ij) ((Q ⊗ S).p ij)) =
          (∑ i : Fin n, d (P.p i) (Q.p i)) + (∑ j : Fin m, d (R.p j) (S.p j)))
    (hMeas : Measurable (d 1)) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → d 1 q = C * log q := by
  have hMul := dirac_extraction_cauchy_Ioc d hReg hAdd
  exact mul_cauchy_Ioc_eq_const_mul_log (g := d 1) hMul hMeas

end KnuthSkilling.ShoreJohnson.Proof
