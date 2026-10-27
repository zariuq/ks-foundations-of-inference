import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.Archimedean
import KnuthSkilling.Multiplicative.FunctionalEquation

/-!
# Continuity from order and translated addition

Positivity and the product equation give arbitrarily small dyadic values and
additive closure of the range. Density in the positive reals then lets Mathlib's
monotone-continuity theorem rule out jumps. Continuity is a conclusion here;
Cox's independent generator construction assumes it.
-/

namespace KnuthSkilling.Multiplicative

open Classical
open Set

/-- **Continuity from ProductEquation + StrictMono + Positivity**.

A strictly monotone positive function satisfying the `ProductEquation` is continuous.

Proof idea:
- From the product equation (at `τ = 0`), `range Ψ` is closed under addition.
- From the “doubling” consequence, `range Ψ` contains all dyadic multiples of `Ψ 0`.
- Dyadics are dense in `(0,∞)`, so `range Ψ` is dense in `(0,∞)`.
- A strictly monotone function cannot have a jump discontinuity with dense range. -/
theorem productEquation_strictMono_pos_continuous
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hStrictMono : StrictMono Ψ) :
    Continuous Ψ := by
  let a : ℝ := ζ 0 0
  have hShift : ∀ τ : ℝ, Ψ (τ + a) = 2 * Ψ τ := fun τ => by
    simpa using ProductEquation.shift_two_mul hProd τ
  have ha_ne : a ≠ 0 := by
    intro ha0
    have h := hShift 0
    simp only [ha0, add_zero] at h
    linarith [hPos 0]
  have ha_pos : 0 < a := by
    by_contra h
    push Not at h
    rcases h.lt_or_eq with ha_neg | ha_zero
    · have h1 : Ψ a < Ψ 0 := hStrictMono ha_neg
      have h2 : Ψ a = 2 * Ψ 0 := by
        simpa using hShift 0
      linarith [hPos 0]
    · exact ha_ne ha_zero

  let C := Ψ 0
  have hC_pos : 0 < C := hPos 0
  have hRangeAdd : ∀ u v : ℝ, u ∈ Set.range Ψ → v ∈ Set.range Ψ → (u + v) ∈ Set.range Ψ := by
    intro u v ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨ζ x y, ?_⟩
    have := hProd 0 x y
    simp only [zero_add] at this
    rw [hx, hy] at this
    exact this.symm
  have hHalving_eq : ∀ k : ℕ, Ψ (-(k : ℤ) * a) = C / 2 ^ k := by
    intro k
    induction k with
    | zero =>
      simp [C]
    | succ n ih =>
      have h1 : (-(↑(n + 1) : ℤ) : ℝ) * a = -(n : ℤ) * a - a := by
        push_cast
        ring
      rw [h1]
      have h2 : Ψ (-(n : ℤ) * a - a + a) = 2 * Ψ (-(n : ℤ) * a - a) := hShift _
      simp only [sub_add_cancel] at h2
      have h3 : Ψ (-(n : ℤ) * a - a) = Ψ (-(n : ℤ) * a) / 2 := by
        linarith
      rw [h3, ih]
      have hne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hne]
      ring
  have hHalving : ∀ k : ℕ, C / (2 : ℝ) ^ k ∈ Set.range Ψ := by
    intro k
    exact ⟨-(k : ℤ) * a, hHalving_eq k⟩
  have hDyadicInRange : ∀ m k : ℕ, 1 ≤ m → (m : ℝ) * C / (2 : ℝ) ^ k ∈ Set.range Ψ := by
    intro m k hm
    induction m with
    | zero =>
      omega
    | succ n ih =>
      have heq :
          ((n + 1 : ℕ) : ℝ) * C / (2 : ℝ) ^ k =
            (n : ℝ) * C / (2 : ℝ) ^ k + C / (2 : ℝ) ^ k := by
        have hne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
        field_simp [hne]
        push_cast
        ring
      rw [heq]
      cases n with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, zero_div, zero_add]
        exact hHalving k
      | succ n' =>
        apply hRangeAdd
        · exact ih (by omega)
        · exact hHalving k
  have hDensityInPos : ∀ y : ℝ, 0 < y → ∀ ε > 0, ∃ v ∈ Set.range Ψ, |v - y| < ε := by
    intro y hy ε hε
    have hmin_pos : 0 < min ε y := lt_min hε hy
    have hquot_pos : 0 < C / min ε y := div_pos hC_pos hmin_pos
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (C / min ε y) / Real.log 2)
    let k := n
    have hk_large' : (2 : ℝ) ^ k > C / min ε y := by
      have hlog_k : Real.log (C / min ε y) / Real.log 2 < k := hn
      have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
      rw [gt_iff_lt, ← Real.log_lt_log_iff hquot_pos h2k_pos]
      calc
        Real.log (C / min ε y)
            = Real.log (C / min ε y) / Real.log 2 * Real.log 2 := by
                field_simp [ne_of_gt hlog2_pos]
        _ < k * Real.log 2 := by
              exact mul_lt_mul_of_pos_right hlog_k hlog2_pos
        _ = Real.log (2 ^ k) := by
              rw [Real.log_pow]
    have hk_large : C / (2 : ℝ) ^ k < min ε y := by
      have h2k : (2 : ℝ) ^ k > C / min ε y := hk_large'
      calc
        C / (2 : ℝ) ^ k < C / (C / min ε y) := by
              apply div_lt_div_of_pos_left hC_pos
              · exact div_pos hC_pos hmin_pos
              · exact h2k
        _ = min ε y := by
              field_simp [ne_of_gt hmin_pos]
    let r := y * (2 : ℝ) ^ k / C
    have hr_pos : 0 < r := div_pos (mul_pos hy (pow_pos (by norm_num) k)) hC_pos
    let m := Nat.ceil r
    have hm_ge_1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hr_pos).ne'
    refine ⟨(m : ℝ) * C / (2 : ℝ) ^ k, hDyadicInRange m k hm_ge_1, ?_⟩
    have hceil_bound : r ≤ m := Nat.le_ceil r
    have hne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    rw [abs_lt]
    constructor
    · have h1 : y ≤ (m : ℝ) * C / (2 : ℝ) ^ k := by
        calc
          y = r * C / (2 : ℝ) ^ k := by
                simp only [r]
                field_simp [ne_of_gt hC_pos, hne]
          _ ≤ (m : ℝ) * C / (2 : ℝ) ^ k := by
                apply div_le_div_of_nonneg_right _ (le_of_lt h2k_pos)
                apply mul_le_mul_of_nonneg_right hceil_bound
                exact le_of_lt hC_pos
      linarith
    · have h2 : (m : ℝ) * C / (2 : ℝ) ^ k < y + C / (2 : ℝ) ^ k := by
        have h3 : (m : ℝ) < r + 1 := by
          have h := Nat.ceil_lt_add_one (le_of_lt hr_pos)
          linarith
        calc
          (m : ℝ) * C / (2 : ℝ) ^ k
              < (r + 1) * C / (2 : ℝ) ^ k := by
                    apply div_lt_div_of_pos_right _ h2k_pos
                    apply mul_lt_mul_of_pos_right h3 hC_pos
          _ = y + C / (2 : ℝ) ^ k := by
                simp only [r]
                field_simp [ne_of_gt hC_pos, hne]
      have hstep : C / (2 : ℝ) ^ k < ε := lt_of_lt_of_le hk_large (min_le_left _ _)
      linarith

  let f : ℝ → Set.Ioi (0 : ℝ) := fun x => ⟨Ψ x, hPos x⟩
  have hfmono : Monotone f := fun _ _ h => hStrictMono.monotone h
  have hfdense : DenseRange f := by
    rw [Metric.denseRange_iff]
    intro y ε hε
    obtain ⟨v, ⟨x, hx⟩, hv⟩ := hDensityInPos y.val y.2 ε hε
    refine ⟨x, ?_⟩
    change dist (y : ℝ) (Ψ x) < ε
    simpa only [Real.dist_eq, hx, abs_sub_comm] using hv
  exact continuous_subtype_val.comp (hfmono.continuous_of_denseRange hfdense)

/-- Appendix B exponential solution under `StrictMono` + positivity, with continuity *derived*. -/
theorem productEquation_solution_of_strictMono
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hStrictMono : StrictMono Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  have hCont : Continuous Ψ :=
    productEquation_strictMono_pos_continuous Ψ ζ hProd hPos hStrictMono
  exact productEquation_solution_of_continuous_strictMono hProd hPos hCont hStrictMono

/-- Appendix B exponential solution under `StrictAnti` + positivity. -/
theorem productEquation_solution_of_strictAnti
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hStrictAnti : StrictAnti Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  let Ψ' : ℝ → ℝ := fun x => Ψ (-x)
  let ζ' : ℝ → ℝ → ℝ := fun ξ η => -ζ (-ξ) (-η)
  have hProd' : ProductEquation Ψ' ζ' := by
    intro τ ξ η
    simp only [Ψ', ζ']
    have := hProd (-τ) (-ξ) (-η)
    simp only [neg_add_rev] at this ⊢
    convert this using 2 <;> ring_nf
  have hPos' : ∀ x, 0 < Ψ' x := fun x => hPos (-x)
  have hStrictMono' : StrictMono Ψ' := hStrictAnti.comp (fun _ _ h => neg_lt_neg h)
  obtain ⟨C', A', hC'_pos, hΨ'_eq⟩ :=
    productEquation_solution_of_strictMono Ψ' ζ' hProd' hPos' hStrictMono'
  refine ⟨C', -A', hC'_pos, ?_⟩
  intro x
  have := hΨ'_eq (-x)
  simp only [Ψ', neg_neg] at this
  simp only [mul_neg, neg_mul] at this ⊢
  exact this

end KnuthSkilling.Multiplicative
