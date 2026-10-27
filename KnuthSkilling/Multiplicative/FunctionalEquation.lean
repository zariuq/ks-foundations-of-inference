import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Rat
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Positive additive maps and the KS product equation

Positive-additive maps are linear on `(0,∞)`, by rational scaling and order
density. The translated product equation then forces positive continuous,
strictly monotone solutions to be exponential. `StrictMonoSolution` derives
continuity under its stronger product-equation assumptions. These are functional
equation results; a conjunction generator from Cox has different hypotheses.
-/

namespace KnuthSkilling.Multiplicative

open Classical
open Set
open scoped Topology

/-- A multiplicative observation transports a supplied left fold to a product. -/
theorem observe_foldl {M N : Type*} [Monoid M] [Monoid N] (o : M →* N)
    (s : M) (xs : List M) :
    o (xs.foldl (· * ·) s) = o s * (xs.map o).prod := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih, map_mul, mul_assoc]

/-- A normalized multiplicative map can still erase every input distinction. -/
theorem constant_one_not_faithful : ¬Function.Injective (1 : ℝ →* ℝ) := by
  intro h
  have hc := h (a₁ := (1 / 2 : ℝ)) (a₂ := (1 : ℝ)) rfl
  norm_num at hc

/-- K&S Appendix B product equation (TeX eq. (1972)). -/
def ProductEquation (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ) : Prop :=
  ∀ τ ξ η : ℝ, Ψ (τ + ξ) + Ψ (τ + η) = Ψ (τ + ζ ξ η)

namespace ProductEquation

variable {Ψ : ℝ → ℝ} {ζ : ℝ → ℝ → ℝ}

/-- Special case `τ = 0`: `Ψ ξ + Ψ η = Ψ (ζ ξ η)`. -/
theorem tau0 (h : ProductEquation Ψ ζ) (ξ η : ℝ) :
    Ψ ξ + Ψ η = Ψ (ζ ξ η) := by
  simpa using h 0 ξ η

/-- The “2-term recurrence” extracted from the product equation (TeX eq. (1991)):

for `a := ζ 0 0`, we have `Ψ (τ + a) = 2 * Ψ τ`. -/
theorem shift_two_mul (h : ProductEquation Ψ ζ) (τ : ℝ) :
    Ψ (τ + ζ 0 0) = 2 * Ψ τ := by
  have hτ := h τ 0 0
  simpa [two_mul, add_assoc, add_left_comm, add_comm] using hτ.symm

end ProductEquation

namespace AdditiveOnPos

/-- If `f` is additive on positive reals and maps positive reals to positive reals, then
it is strictly increasing on `(0,∞)`. -/
theorem strictMonoOn_of_add_of_pos
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    (hpos : ∀ {u : ℝ}, 0 < u → 0 < f u) :
    StrictMonoOn f (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have hdiff : 0 < b - a := sub_pos.mpr hab
  have hsplit : f b = f a + f (b - a) := by
    calc
      f b = f (a + (b - a)) := by simp [add_sub_cancel]
      _ = f a + f (b - a) := hadd ha hdiff
  have hf_diff : 0 < f (b - a) := hpos hdiff
  have : f a < f a + f (b - a) := lt_add_of_pos_right _ hf_diff
  simpa [hsplit] using this

/-- If `f` is additive on positive reals, then scaling the input by a positive natural scales
the output by the same natural. -/
theorem map_natMul
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    {u : ℝ} (hu : 0 < u) :
    ∀ n : ℕ, f ((n.succ : ℝ) * u) = (n.succ : ℝ) * f u := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hnpos : 0 < ((n.succ : ℝ) * u) := by
      have : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact mul_pos this hu
    have hmul : ((n.succ.succ : ℝ) * u) = ((n.succ : ℝ) * u + u) := by
      simp [Nat.cast_succ, add_mul, add_assoc, add_left_comm, add_comm]
    calc
      f ((n.succ.succ : ℝ) * u)
          = f (((n.succ : ℝ) * u) + u) := by
              simpa using congrArg f hmul
      _ = f ((n.succ : ℝ) * u) + f u := hadd hnpos hu
      _ = (n.succ : ℝ) * f u + f u := by
          simpa using congrArg (fun t => t + f u) ih
      _ = (n.succ.succ : ℝ) * f u := by
        simp [Nat.cast_succ, add_mul, add_assoc, add_left_comm, add_comm]

/-- `map_natMul` with the natural-multiplier provided explicitly (requiring `0 < n`). -/
theorem map_natMul_pos
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    {u : ℝ} (hu : 0 < u) (n : ℕ) (hn : 0 < n) :
    f ((n : ℝ) * u) = (n : ℝ) * f u := by
  cases n with
  | zero => cases hn
  | succ n =>
    simpa using map_natMul f hadd hu n

/-- **Scaling lemma**: an additive, positive function on `(0,∞)` is multiplication by a constant.

This is a standard “Cauchy + monotone” argument, but restricted to positive reals.
-/
theorem exists_mul_const_of_add_of_pos
    (f : ℝ → ℝ)
    (hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v)
    (hpos : ∀ {u : ℝ}, 0 < u → 0 < f u) :
    ∃ c : ℝ, 0 < c ∧ ∀ {u : ℝ}, 0 < u → f u = c * u := by
  let c := f 1
  have hc : 0 < c := hpos (u := 1) zero_lt_one
  have hmono := strictMonoOn_of_add_of_pos f hadd hpos
  have hrat (q : ℚ) (hq : 0 < (q : ℝ)) : f (q : ℝ) = c * (q : ℝ) := by
    have hqp : 0 < q := by exact_mod_cast hq
    have hn := q.den_pos
    have hm : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hqp))
    have hnum : 0 < (q.num : ℝ) := by exact_mod_cast Rat.num_pos.mpr hqp
    have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    have hcast : (q.den : ℝ) * (q : ℝ) = (q.num.natAbs : ℝ) := by
      have hnat : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hqp).le
      have hnatR : (q.num.natAbs : ℝ) = (q.num : ℝ) := by simpa using congrArg (fun z : ℤ => (z : ℝ)) hnat
      rw [Rat.cast_def, hnatR]
      field_simp
    have hmul := map_natMul_pos f hadd hq q.den hn
    have hnat := map_natMul_pos f hadd (u := 1) zero_lt_one q.num.natAbs hm
    rw [hcast] at hmul
    simp only [mul_one] at hnat
    apply mul_left_cancel₀ hden
    calc (q.den : ℝ) * f (q : ℝ) = (q.num.natAbs : ℝ) * c := hmul.symm.trans hnat
      _ = (q.den : ℝ) * (c * (q : ℝ)) := by rw [← hcast]; ring
  refine ⟨c, hc, fun {u} hu => le_antisymm ?_ ?_⟩
  · by_contra h
    have hlt : u < f u / c := (lt_div_iff₀ hc).mpr (by simpa [mul_comm] using lt_of_not_ge h)
    obtain ⟨q, huq, hqf⟩ := exists_rat_btwn hlt
    have hqpos := hu.trans huq
    have hmono' := hmono hu hqpos huq
    rw [hrat q hqpos] at hmono'
    have hbound := (lt_div_iff₀ hc).mp hqf
    nlinarith
  · by_contra h
    have hlt : f u / c < u := (div_lt_iff₀ hc).mpr (by simpa [mul_comm] using lt_of_not_ge h)
    obtain ⟨q, hfq, hqu⟩ := exists_rat_btwn hlt
    have hqpos := (div_pos (hpos hu) hc).trans hfq
    have hmono' := hmono hqpos hu hqu
    rw [hrat q hqpos] at hmono'
    have hbound := (div_lt_iff₀ hc).mp hfq
    nlinarith

end AdditiveOnPos

open Filter

/-- A convenient Cauchy lemma: a continuous additive `φ : ℝ → ℝ` is linear. -/
theorem continuous_additive_eq_mul (φ : ℝ → ℝ)
    (hadd : ∀ x y : ℝ, φ (x + y) = φ x + φ y)
    (hcont : Continuous φ) :
    ∃ A : ℝ, ∀ x : ℝ, φ x = A * x := by
  let f_add : ℝ →+ ℝ :=
    { toFun := φ
      map_zero' := by
        have h := hadd 0 0
        have : φ 0 + 0 = φ 0 + φ 0 := by simpa using h
        have : 0 = φ 0 := add_left_cancel this
        simpa using this.symm
      map_add' := by intro x y; simpa using hadd x y }
  have hf_add_cont : Continuous f_add := by
    simpa [f_add] using hcont
  let f_lin : ℝ →L[ℝ] ℝ := f_add.toRealLinearMap hf_add_cont
  refine ⟨f_lin 1, ?_⟩
  intro x
  have hsmul := f_lin.map_smul x (1 : ℝ)
  have : f_lin x = x * f_lin 1 := by simpa [smul_eq_mul] using hsmul
  simpa [f_add, f_lin, mul_comm, mul_left_comm, mul_assoc] using this

/-- K&S Appendix B Product Theorem: exponential is the unique solution.

If `Ψ` is positive, continuous, strictly monotone, and satisfies the product equation,
then `Ψ x = C * exp (A * x)` for some `C > 0`.

This is a standard functional equations result. The hypotheses `Continuous Ψ` and
`StrictMono Ψ` are **not** extra assumptions in K&S - they are **derived** from the
order isomorphism `Θ : PosReal ≃o ℝ` established in Appendix A:
- `Psi_continuous`: order isomorphisms on ℝ are continuous
- `Psi_strictMono`: order isomorphisms are strictly monotone

See `Multiplicative.Main` for the assembled result. -/
theorem productEquation_solution_of_continuous_strictMono
    {Ψ : ℝ → ℝ} {ζ : ℝ → ℝ → ℝ}
    (hEq : ProductEquation Ψ ζ)
    (hPos : ∀ x : ℝ, 0 < Ψ x)
    (hCont : Continuous Ψ)
    (hMono : StrictMono Ψ) :
    ∃ (C A : ℝ), 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  classical
  let a : ℝ := ζ 0 0
  have hshift : ∀ τ : ℝ, Ψ (τ + a) = 2 * Ψ τ := by
    intro τ
    simpa [a] using ProductEquation.shift_two_mul (Ψ := Ψ) (ζ := ζ) hEq τ
  have ha_pos : 0 < a := by
    have h0 : 0 < Ψ 0 := hPos 0
    have hΨ0_lt_Ψa : Ψ 0 < Ψ a := by
      have hΨa : Ψ a = 2 * Ψ 0 := by simpa [a, zero_add] using (hshift 0)
      have hlt : Ψ 0 < 2 * Ψ 0 := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa [one_mul] using (mul_lt_mul_of_pos_right this h0)
      simpa [hΨa] using hlt
    exact (hMono.lt_iff_lt).1 hΨ0_lt_Ψa

  let C : ℝ := Ψ 0
  have hC_pos : 0 < C := hPos 0
  have hsurj : Function.Surjective fun x : ℝ => (⟨Ψ x, hPos x⟩ : Ioi (0 : ℝ)) := by
    intro y
    rcases y with ⟨y, hy⟩
    have hN : ∃ N : ℕ, C / (2 : ℝ) ^ N < y := by
      have hx : 0 < y / C := div_pos hy hC_pos
      rcases exists_pow_lt_of_lt_one (x := y / C) hx (y := (1 / 2 : ℝ)) (by norm_num) with
        ⟨N, hN⟩
      refine ⟨N, ?_⟩
      have hpow : (1 / 2 : ℝ) ^ N = 1 / (2 : ℝ) ^ N := by simp [one_div, inv_pow]
      have hC_ne : C ≠ 0 := ne_of_gt hC_pos
      have hN' : (1 / (2 : ℝ) ^ N) < y / C := by simpa [hpow] using hN
      have hmul : (1 / (2 : ℝ) ^ N) * C < y := by
        have h := mul_lt_mul_of_pos_right hN' hC_pos
        simpa [div_mul_cancel, hC_ne] using h
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hM : ∃ M : ℕ, y < (2 : ℝ) ^ M * C := by
      have hx : 0 < y / C := div_pos hy hC_pos
      rcases pow_unbounded_of_one_lt (R := ℝ) (x := y / C) (y := (2 : ℝ)) (by norm_num) with
        ⟨M, hM⟩
      refine ⟨M, ?_⟩
      simpa using (div_lt_iff₀ hC_pos).1 hM

    rcases hN with ⟨N, hN⟩
    rcases hM with ⟨M, hM⟩
    have hC_mul (n : ℕ) : Ψ ((n : ℝ) * a) = (2 : ℝ) ^ n * C := by
      induction n with
      | zero => simp [C, a]
      | succ n ih =>
        have hstep : Ψ (((n : ℝ) * a) + a) = 2 * Ψ ((n : ℝ) * a) := hshift ((n : ℝ) * a)
        have hmul : ((n.succ : ℝ) * a) = (n : ℝ) * a + a := by
          simp [Nat.cast_succ, add_mul, add_comm]
        calc
          Ψ ((n.succ : ℝ) * a)
              = 2 * Ψ ((n : ℝ) * a) := by simpa [hmul.symm] using hstep
          _ = 2 * ((2 : ℝ) ^ n * C) := by simp [ih]
          _ = (2 : ℝ) ^ n.succ * C := by
            simp [pow_succ, mul_left_comm, mul_comm]

    have hC_div (n : ℕ) : Ψ (-(n : ℝ) * a) = C / (2 : ℝ) ^ n := by
      induction n with
      | zero => simp [C]
      | succ n ih =>
        have hrec : Ψ ((-(n.succ : ℝ) * a) + a) = 2 * Ψ (-(n.succ : ℝ) * a) :=
          hshift (-(n.succ : ℝ) * a)
        have hmul : (-(n : ℝ) * a) = (-(n.succ : ℝ) * a) + a := by
          simp [Nat.cast_succ, add_mul, add_comm]
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        have hstep : Ψ (-(n.succ : ℝ) * a) = Ψ (-(n : ℝ) * a) / 2 := by
          have hrec' : Ψ (-(n : ℝ) * a) = 2 * Ψ (-(n.succ : ℝ) * a) := by
            simpa [hmul] using hrec
          apply (eq_div_iff h2).2
          simpa [mul_comm, mul_left_comm, mul_assoc] using hrec'.symm
        calc
          Ψ (-(n.succ : ℝ) * a)
              = Ψ (-(n : ℝ) * a) / 2 := hstep
          _ = (C / (2 : ℝ) ^ n) / 2 := by
            simpa using congrArg (fun t : ℝ => t / 2) ih
          _ = C / (2 : ℝ) ^ n.succ := by
            simp [pow_succ, div_eq_mul_inv, mul_left_comm, mul_comm]

    let xL : ℝ := - (N : ℝ) * a
    let xU : ℝ := (M : ℝ) * a
    have hxL : Ψ xL < y := by
      have hxL_eq : Ψ xL = C / (2 : ℝ) ^ N := by simpa [xL] using hC_div N
      simpa [hxL_eq] using hN
    have hxU : y < Ψ xU := by simpa [xU, hC_mul M] using hM
    have hxL_le_xU : xL ≤ xU := (hMono.lt_iff_lt.mp (hxL.trans hxU)).le
    have hy_mem : y ∈ Icc (Ψ xL) (Ψ xU) := ⟨le_of_lt hxL, le_of_lt hxU⟩
    have hy_img : y ∈ Ψ '' Icc xL xU :=
      (intermediate_value_Icc hxL_le_xU (hCont.continuousOn)) hy_mem
    rcases hy_img with ⟨x, hxIcc, hx⟩
    refine ⟨x, ?_⟩
    ext
    simpa using hx
  let Ψpos : ℝ → Ioi (0 : ℝ) := fun x => ⟨Ψ x, hPos x⟩
  have hΨpos_mono : StrictMono Ψpos := by
    intro x y hxy
    exact hMono hxy
  let ΨIso : ℝ ≃o Ioi (0 : ℝ) := StrictMono.orderIsoOfSurjective _ hΨpos_mono hsurj
  let T : ℝ → ℝ → ℝ := fun τ u =>
    if hu : 0 < u then Ψ (τ + ΨIso.symm ⟨u, hu⟩) else 0

  have hT_pos : ∀ τ u : ℝ, 0 < u → 0 < T τ u := by
    intro τ u hu
    simp [T, hu, hPos]

  have hT_add : ∀ τ : ℝ, ∀ {u v : ℝ}, 0 < u → 0 < v → T τ (u + v) = T τ u + T τ v := by
    intro τ u v hu hv
    have huv : 0 < u + v := add_pos hu hv
    set ξ : ℝ := ΨIso.symm ⟨u, hu⟩
    set η : ℝ := ΨIso.symm ⟨v, hv⟩
    have hξ : Ψ ξ = u := by
      have hsub : ΨIso ξ = ⟨u, hu⟩ := ΨIso.apply_symm_apply ⟨u, hu⟩
      exact congrArg Subtype.val hsub
    have hη : Ψ η = v := by
      have hsub : ΨIso η = ⟨v, hv⟩ := ΨIso.apply_symm_apply ⟨v, hv⟩
      exact congrArg Subtype.val hsub
    have hsum : Ψ (ζ ξ η) = u + v := by
      have := ProductEquation.tau0 (Ψ := Ψ) (ζ := ζ) hEq ξ η
      simpa [hξ, hη, add_comm, add_left_comm, add_assoc] using this.symm
    have hpre : ΨIso.symm ⟨u + v, huv⟩ = ζ ξ η := by
      apply ΨIso.injective
      rw [ΨIso.apply_symm_apply]
      ext
      simpa [Ψpos, ΨIso] using hsum.symm
    simp only [T, hu, hv, huv, dif_pos, ξ, η, hpre]
    exact (hEq τ ξ η).symm
  have hT_scale : ∀ τ : ℝ, ∃ k : ℝ, 0 < k ∧ ∀ {u : ℝ}, 0 < u → T τ u = k * u := by
    intro τ
    exact AdditiveOnPos.exists_mul_const_of_add_of_pos (f := T τ) (hadd := hT_add τ)
      (hpos := fun hu => hT_pos τ _ hu)
  have h_mul : ∀ τ x : ℝ, Ψ (τ + x) = (Ψ τ / C) * Ψ x := by
    intro τ x
    rcases hT_scale τ with ⟨k, hkpos, hk⟩
    have hC : 0 < C := hC_pos
    have hkC : T τ C = k * C := hk (u := C) hC
    have hk0 : T τ (Ψ x) = k * Ψ x := hk (u := Ψ x) (hPos x)
    have hTC : T τ C = Ψ τ := by
      simp only [T, C, hC, dif_pos]
      have h0 : ΨIso.symm ⟨Ψ 0, hPos 0⟩ = 0 := by
        apply ΨIso.symm_apply_apply
      simp [h0]
    have hTx : T τ (Ψ x) = Ψ (τ + x) := by
      simp only [T, hPos x, dif_pos]
      have hx : ΨIso.symm ⟨Ψ x, hPos x⟩ = x := by
        apply ΨIso.symm_apply_apply
      simp [hx]
    have hkval : k = Ψ τ / C := by
      have heq : k * C = Ψ τ := by rw [← hTC, hkC]
      field_simp [ne_of_gt hC] at heq ⊢
      linarith
    calc Ψ (τ + x)
        = T τ (Ψ x) := hTx.symm
      _ = k * Ψ x := hk0
      _ = (Ψ τ / C) * Ψ x := by rw [hkval]
  let Φ : ℝ → ℝ := fun x => Ψ x / C
  have hΦ_pos : ∀ x, 0 < Φ x := by
    intro x
    exact div_pos (hPos x) hC_pos
  have hΦ_mul : ∀ x y, Φ (x + y) = Φ x * Φ y := by
    intro x y
    have hmul := h_mul x y
    simp [Φ]
    rw [hmul]
    simp [mul_div_assoc]

  let φ : ℝ → ℝ := fun x => Real.log (Φ x)
  have hφ_add : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y
    have hx : 0 < Φ x := hΦ_pos x
    have hy : 0 < Φ y := hΦ_pos y
    have hx0 : Φ x ≠ 0 := ne_of_gt hx
    have hy0 : Φ y ≠ 0 := ne_of_gt hy
    calc
      φ (x + y) = Real.log (Φ (x + y)) := rfl
      _ = Real.log (Φ x * Φ y) := by simp [hΦ_mul x y]
      _ = Real.log (Φ x) + Real.log (Φ y) := Real.log_mul hx0 hy0
      _ = φ x + φ y := rfl
  have hφ_cont : Continuous φ := by
    have hΦ_cont : Continuous Φ := hCont.div_const C
    refine Real.continuousOn_log.comp_continuous hΦ_cont ?_
    intro x
    have : Φ x ≠ 0 := ne_of_gt (hΦ_pos x)
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using this

  rcases continuous_additive_eq_mul φ hφ_add hφ_cont with ⟨A, hA⟩
  refine ⟨C, A, hC_pos, ?_⟩
  intro x
  have : φ x = A * x := hA x
  have : Φ x = Real.exp (A * x) := by
    have hx : 0 < Φ x := hΦ_pos x
    have : Real.exp (Real.log (Φ x)) = Real.exp (A * x) := by simpa [φ] using congrArg Real.exp this
    simpa [Real.exp_log hx, φ] using this
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hdiv : Ψ x / C = Real.exp (A * x) := by simpa [Φ] using this
  have : Ψ x = Real.exp (A * x) * C := (div_eq_iff hC_ne).1 hdiv
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

end KnuthSkilling.Multiplicative
