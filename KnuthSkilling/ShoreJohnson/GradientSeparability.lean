import KnuthSkilling.ShoreJohnson.Inference
import KnuthSkilling.ShoreJohnson.Objective
import KnuthSkilling.ShoreJohnson.Constraints
import KnuthSkilling.ShoreJohnson.AppendixMinimizer
import KnuthSkilling.ShoreJohnson.AppendixTheoremI
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Coordinate gradients, locality and ratio invariance

Differentiability, locality, and the cocycle law are distinct hypotheses.
`ExtractGRegularity` records all three; its locality field is not a theorem
from the inference axioms. Differentiable atom sums provide concrete instances.

The finite reference constructions below retain their supplied coordinates.
Global extraction uses the stronger, explicit ratio-invariance law: arbitrary
positive ratios fit in a four-state probability frame together with ratio one.
The cocycle then produces one coordinate kernel, including on two-state systems.
No bound on every probability coordinate and no inference-totality premise is used.
-/

namespace KnuthSkilling.ShoreJohnson.GradientSeparability
open Classical Finset
open scoped BigOperators Topology
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Inference
open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.Appendix
open KnuthSkilling.ShoreJohnson.AppendixMinimizer
open KnuthSkilling.ShoreJohnson.AppendixTheoremI

noncomputable def simplexFin2 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : ProbDist 2 where
  p := ![t, 1 - t]
  nonneg := by
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact le_of_lt ht0
    · linarith
  sum_one := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

noncomputable def priorFin2 (p₀ : ℝ) (hp0 : 0 < p₀) (hp1 : p₀ < 1) : ProbDist 2 :=
  simplexFin2 p₀ hp0 hp1

structure GradientRepresentation (F : ObjectiveFunctional) where

  g : ℝ → ℝ → ℝ

  scale : ∀ {n : ℕ}, ProbDist n → ProbDist n → ℝ

  scale_ne_zero : ∀ {n : ℕ} (p q : ProbDist n), scale p q ≠ 0

  shift2_deriv :
    ∀ {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j),
      (∀ k, 0 < p.p k) → (∀ k, 0 < q.p k) →
      HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p)
        (scale p q * (g (q.p i) (p.p i) - g (q.p j) (p.p j))) (q.p i)

structure ExtractGRegularity (F : ObjectiveFunctional) where

  has_shift2_deriv :
    ∀ {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j),
      (∀ k, 0 < p.p k) → (∀ k, 0 < q.p k) →
      ∃ L : ℝ, HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (q.p i)

  deriv_local :
    ∀ {n m : ℕ} (p : ProbDist n) (q : ProbDist n) (p' : ProbDist m) (q' : ProbDist m)
      (i j : Fin n) (i' j' : Fin m) (hij : i ≠ j) (hi'j' : i' ≠ j')
      (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k)
      (hp' : ∀ k, 0 < p'.p k) (hq' : ∀ k, 0 < q'.p k),
      q.p i = q'.p i' → p.p i = p'.p i' → q.p j = q'.p j' → p.p j = p'.p j' →
      Classical.choose (has_shift2_deriv p q i j hij hp hq) =
        Classical.choose (has_shift2_deriv p' q' i' j' hi'j' hp' hq')

  cocycle :
    ∀ {n : ℕ} (p q : ProbDist n) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k),
      Classical.choose (has_shift2_deriv p q i j hij hp hq) +
        Classical.choose (has_shift2_deriv p q j k hjk hp hq) =
        Classical.choose (has_shift2_deriv p q i k hik hp hq)

theorem deriv_symmetric_under_swap
    (F : ObjectiveFunctional)
    (hReg : ExtractGRegularity F)
    {n : ℕ} (p q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j)
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k) :
    let L_ij := Classical.choose (hReg.has_shift2_deriv p q i j hij hp hq)
    let L_ji := Classical.choose (hReg.has_shift2_deriv p q j i hij.symm hp hq)
    L_ij = -L_ji := by

  let φ := fun t => F.D (shift2ProbClamp q i j hij t) p
  let ψ := fun s => F.D (shift2ProbClamp q j i hij.symm s) p
  let L_ij := Classical.choose (hReg.has_shift2_deriv p q i j hij hp hq)
  let L_ji := Classical.choose (hReg.has_shift2_deriv p q j i hij.symm hp hq)

  have hDeriv_ij : HasDerivAt φ L_ij (q.p i) :=
    Classical.choose_spec (hReg.has_shift2_deriv p q i j hij hp hq)
  have hDeriv_ji : HasDerivAt ψ L_ji (q.p j) :=
    Classical.choose_spec (hReg.has_shift2_deriv p q j i hij.symm hp hq)

  have hReflect : HasDerivAt (fun t => q.p i + q.p j - t) (-1) (q.p i) := by
    have h2 : HasDerivAt (fun t => t) 1 (q.p i) := hasDerivAt_id _
    exact h2.const_sub (q.p i + q.p j)

  have hReflect_val : q.p i + q.p j - q.p i = q.p j := by ring

  have hComp : HasDerivAt (ψ ∘ (fun t => q.p i + q.p j - t)) (L_ji * (-1)) (q.p i) := by
    have hDeriv_ji' : HasDerivAt ψ L_ji (q.p i + q.p j - q.p i) := by
      simp only [add_sub_cancel_left]
      exact hDeriv_ji
    exact HasDerivAt.comp (q.p i) hDeriv_ji' hReflect

  have hEqNhd : ∀ᶠ t in nhds (q.p i), φ t = (ψ ∘ (fun t => q.p i + q.p j - t)) t := by

    rw [Filter.eventually_iff_exists_mem]
    use Set.Ioo 0 (q.p i + q.p j)
    constructor
    ·
      apply Ioo_mem_nhds
      · exact hq i
      · have : 0 < q.p j := hq j
        linarith
    · intro t ht
      simp only [Function.comp_apply, φ, ψ]
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have ht1 : t ≤ q.p i + q.p j := le_of_lt ht.2
      rw [shift2ProbClamp_swap q i j hij t ht0 ht1]

  have hDerivEq : L_ij = L_ji * (-1) := by
    exact HasDerivAt.unique hDeriv_ij (hComp.congr_of_eventuallyEq hEqNhd)

  simp only [mul_neg_one] at hDerivEq
  exact hDerivEq

theorem simplexFin2_pos (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ k : Fin 2, 0 < (simplexFin2 t ht0 ht1).p k := by
  intro k
  fin_cases k
  · simp [simplexFin2, Matrix.cons_val_zero]; exact ht0
  · simp [simplexFin2, Matrix.cons_val_one]; linarith

noncomputable def gConstruction (F : ObjectiveFunctional) (hReg : ExtractGRegularity F) : ℝ → ℝ → ℝ :=
  fun q p =>
    if hq : 0 < q ∧ q < 1 then
      if hp : 0 < p ∧ p < 1 then
        let Q := simplexFin2 q hq.1 hq.2
        let P := priorFin2 p hp.1 hp.2
        let hQpos := simplexFin2_pos q hq.1 hq.2
        let hPpos := simplexFin2_pos p hp.1 hp.2
        Classical.choose (hReg.has_shift2_deriv P Q 0 1 Fin.zero_ne_one hPpos hQpos) / 2
      else 0
    else 0

theorem gConstruction_fin2_formula
    (F : ObjectiveFunctional)
    (hReg : ExtractGRegularity F)
    (q p : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    let Q := simplexFin2 q hq0 hq1
    let P := priorFin2 p hp0 hp1
    let hQpos := simplexFin2_pos q hq0 hq1
    let hPpos := simplexFin2_pos p hp0 hp1
    let L := Classical.choose (hReg.has_shift2_deriv P Q 0 1 Fin.zero_ne_one hPpos hQpos)
    gConstruction F hReg q p - gConstruction F hReg (1 - q) (1 - p) = L := by
  intro Q P hQpos hPpos L

  have hg_q : gConstruction F hReg q p = L / 2 := by
    simp only [gConstruction]
    simp only [hq0, hq1, hp0, hp1, and_self, ↓reduceDIte]

    rfl

  have hq1_pos : 0 < 1 - q := by linarith
  have hq1_lt : 1 - q < 1 := by linarith
  have hp1_pos : 0 < 1 - p := by linarith
  have hp1_lt : 1 - p < 1 := by linarith

  have h10 : (1 : Fin 2) ≠ 0 := Fin.zero_ne_one.symm
  have hg_1mq : gConstruction F hReg (1 - q) (1 - p) = -L / 2 := by
    simp only [gConstruction]
    simp only [hq1_pos, hq1_lt, hp1_pos, hp1_lt, and_self, ↓reduceDIte]

    suffices h : Classical.choose (hReg.has_shift2_deriv
        (priorFin2 (1 - p) hp1_pos hp1_lt)
        (simplexFin2 (1 - q) hq1_pos hq1_lt)
        0 1 Fin.zero_ne_one
        (simplexFin2_pos (1 - p) hp1_pos hp1_lt)
        (simplexFin2_pos (1 - q) hq1_pos hq1_lt)) = -L by
      simp only [h, neg_div]

    let Q' := simplexFin2 (1 - q) hq1_pos hq1_lt
    let P' := priorFin2 (1 - p) hp1_pos hp1_lt
    let hQ'pos := simplexFin2_pos (1 - q) hq1_pos hq1_lt
    let hP'pos := simplexFin2_pos (1 - p) hp1_pos hp1_lt
    let L' := Classical.choose (hReg.has_shift2_deriv P' Q' 0 1 Fin.zero_ne_one hP'pos hQ'pos)

    have hQ'0 : Q'.p 0 = Q.p 1 := by
      simp only [Q', Q, simplexFin2, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hP'0 : P'.p 0 = P.p 1 := by
      simp only [P', P, simplexFin2, priorFin2, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hQ'1 : Q'.p 1 = Q.p 0 := by
      simp only [Q', Q, simplexFin2, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hP'1 : P'.p 1 = P.p 0 := by
      simp only [P', P, simplexFin2, priorFin2, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring

    have hL'_eq_L10 : L' = Classical.choose (hReg.has_shift2_deriv P Q 1 0 h10 hPpos hQpos) :=
      hReg.deriv_local P' Q' P Q 0 1 1 0 Fin.zero_ne_one h10 hP'pos hQ'pos hPpos hQpos
        hQ'0 hP'0 hQ'1 hP'1

    have hL10_eq_negL : Classical.choose (hReg.has_shift2_deriv P Q 1 0 h10 hPpos hQpos) = -L := by
      have := deriv_symmetric_under_swap F hReg P Q 0 1 Fin.zero_ne_one hPpos hQpos
      simp only at this
      linarith

    calc L' = Classical.choose (hReg.has_shift2_deriv P Q 1 0 h10 hPpos hQpos) := hL'_eq_L10
      _ = -L := hL10_eq_negL

  rw [hg_q, hg_1mq]
  ring

theorem cocycle_implies_difference_form
    (h : ℝ → ℝ → ℝ → ℝ → ℝ)
    (h_antisym : ∀ a α b β, h a α b β = -h b β a α)
    (h_cocycle : ∀ a α b β c γ, h a α b β + h b β c γ = h a α c γ)
    (ref_q ref_p : ℝ) :
    ∃ g : ℝ → ℝ → ℝ,
      ∀ a α b β, h a α b β = g a α - g b β := by
  use fun a α => h a α ref_q ref_p
  intro a α b β
  have step1 : h a α b β = h a α ref_q ref_p - h b β ref_q ref_p := by
    have hcyc := h_cocycle a α ref_q ref_p b β
    have hanti := h_antisym ref_q ref_p b β
    linarith
  exact step1

theorem has_shift2_deriv_of_pos
    (F : ObjectiveFunctional) (hReg : ExtractGRegularity F)
    {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j)
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k) :
    HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p)
      (Classical.choose (hReg.has_shift2_deriv p q i j hij hp hq)) (q.p i) :=
  Classical.choose_spec (hReg.has_shift2_deriv p q i j hij hp hq)

noncomputable def probDist3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hsum : a + b < 1) : ProbDist 3 where
  p := ![a, b, 1 - a - b]
  nonneg := by
    intro k; fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact le_of_lt ha
    · exact le_of_lt hb
    · linarith
  sum_one := by
    have h : (![a, b, 1 - a - b] : Fin 3 → ℝ) = fun i =>
      if i = 0 then a else if i = 1 then b else 1 - a - b := by
      ext i; fin_cases i <;> simp
    simp only [Fin.sum_univ_three, h]
    simp only [show ¬((0 : Fin 3) = 1) by decide,
               show ¬((1 : Fin 3) = 0) by decide,
               show ¬((2 : Fin 3) = 0) by decide, show ¬((2 : Fin 3) = 1) by decide,
               ite_true, ite_false]
    ring

theorem probDist3_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hsum : a + b < 1) :
    ∀ k, 0 < (probDist3 a b ha hb hsum).p k := by
  intro k
  simp only [probDist3]
  fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact ha
  · exact hb
  · linarith

noncomputable def derivValue (F : ObjectiveFunctional) (hReg : ExtractGRegularity F)
    (qi pi qj pj : ℝ) (hqi : 0 < qi) (hpi : 0 < pi) (hqj : 0 < qj) (hpj : 0 < pj)
    (hsum_q : qi + qj < 1) (hsum_p : pi + pj < 1) : ℝ :=
  let Q := probDist3 qi qj hqi hqj hsum_q
  let P := probDist3 pi pj hpi hpj hsum_p
  have hQpos := probDist3_pos qi qj hqi hqj hsum_q
  have hPpos := probDist3_pos pi pj hpi hpj hsum_p
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  Classical.choose (hReg.has_shift2_deriv P Q 0 1 h01 hPpos hQpos)

noncomputable def gFromReference (F : ObjectiveFunctional) (hReg : ExtractGRegularity F)
    (ref_q ref_p : ℝ) (href_q : 0 < ref_q ∧ ref_q < 1) (href_p : 0 < ref_p ∧ ref_p < 1) :
    ℝ → ℝ → ℝ :=
  fun a α =>
    if ha : 0 < a ∧ a < 1 then
      if hα : 0 < α ∧ α < 1 then
        if ha_sum : a + ref_q < 1 then
          if hα_sum : α + ref_p < 1 then

            derivValue F hReg a α ref_q ref_p ha.1 hα.1 href_q.1 href_p.1 ha_sum hα_sum
          else

            gConstruction F hReg a α
        else

          gConstruction F hReg a α
      else 0
    else 0

noncomputable def probDist4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c < 1) : ProbDist 4 where
  p := ![a, b, c, 1 - a - b - c]
  nonneg := by
    intro k; fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact le_of_lt ha
    · exact le_of_lt hb
    · exact le_of_lt hc
    · linarith
  sum_one := by
    have h : (![a, b, c, 1 - a - b - c] : Fin 4 → ℝ) = fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else 1 - a - b - c := by
      ext i; fin_cases i <;> simp
    simp only [Fin.sum_univ_four, h]
    simp only [show ¬((0 : Fin 4) = 1) by decide,
               show ¬((0 : Fin 4) = 2) by decide,
               show ¬((1 : Fin 4) = 0) by decide,
               show ¬((1 : Fin 4) = 2) by decide,
               show ¬((2 : Fin 4) = 0) by decide, show ¬((2 : Fin 4) = 1) by decide,
               show ¬((3 : Fin 4) = 0) by decide, show ¬((3 : Fin 4) = 1) by decide,
               show ¬((3 : Fin 4) = 2) by decide,
               ite_true, ite_false]
    ring

theorem probDist4_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c < 1) : ∀ k, 0 < (probDist4 a b c ha hb hc hsum).p k := by
  intro k
  simp only [probDist4]
  fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact ha
  · exact hb
  · exact hc
  · linarith

theorem abstract_cocycle_4elem
    (F : ObjectiveFunctional) (hReg : ExtractGRegularity F)
    (a α b β c γ : ℝ)
    (ha : 0 < a) (hα : 0 < α) (hb : 0 < b) (hβ : 0 < β) (hc : 0 < c) (hγ : 0 < γ)
    (hsum_q : a + b + c < 1) (hsum_p : α + β + γ < 1)
    (hab_q : a + b < 1) (hab_p : α + β < 1)
    (hac_q : a + c < 1) (hac_p : α + γ < 1)
    (hbc_q : b + c < 1) (hbc_p : β + γ < 1) :
    derivValue F hReg a α b β ha hα hb hβ hab_q hab_p =
      derivValue F hReg a α c γ ha hα hc hγ hac_q hac_p -
      derivValue F hReg b β c γ hb hβ hc hγ hbc_q hbc_p := by

  let Q := probDist4 a b c ha hb hc hsum_q
  let P := probDist4 α β γ hα hβ hγ hsum_p
  have hQpos := probDist4_pos a b c ha hb hc hsum_q
  have hPpos := probDist4_pos α β γ hα hβ hγ hsum_p

  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide

  let L01 := Classical.choose (hReg.has_shift2_deriv P Q 0 1 h01 hPpos hQpos)
  let L02 := Classical.choose (hReg.has_shift2_deriv P Q 0 2 h02 hPpos hQpos)
  let L12 := Classical.choose (hReg.has_shift2_deriv P Q 1 2 h12 hPpos hQpos)

  have hCocycle : L01 + L12 = L02 := hReg.cocycle P Q 0 1 2 h01 h12 h02 hPpos hQpos
  have hL01 : L01 = L02 - L12 := by linarith

  have hQ0 : Q.p 0 = a := by simp [Q, probDist4, Matrix.cons_val_zero]
  have hQ1 : Q.p 1 = b := by simp [Q, probDist4, Matrix.cons_val_one]
  have hQ2 : Q.p 2 = c := by
    simp only [Q, probDist4]

    have : (![a, b, c, 1 - a - b - c] : Fin 4 → ℝ) 2 = c := by
      simp
    exact this
  have hP0 : P.p 0 = α := by simp [P, probDist4, Matrix.cons_val_zero]
  have hP1 : P.p 1 = β := by simp [P, probDist4, Matrix.cons_val_one]
  have hP2 : P.p 2 = γ := by
    simp only [P, probDist4]
    have : (![α, β, γ, 1 - α - β - γ] : Fin 4 → ℝ) 2 = γ := by
      simp
    exact this

  have hL01_eq : L01 = derivValue F hReg a α b β ha hα hb hβ hab_q hab_p := by

    let Q' := probDist3 a b ha hb hab_q
    let P' := probDist3 α β hα hβ hab_p
    have hQ'pos := probDist3_pos a b ha hb hab_q
    have hP'pos := probDist3_pos α β hα hβ hab_p
    have h01' : (0 : Fin 3) ≠ 1 := by decide
    have hEq : L01 = Classical.choose (hReg.has_shift2_deriv P' Q' 0 1 h01' hP'pos hQ'pos) := by
      apply hReg.deriv_local P Q P' Q' 0 1 0 1 h01 h01' hPpos hQpos hP'pos hQ'pos
      · simp [Q, Q', probDist4, probDist3, Matrix.cons_val_zero]
      · simp [P, P', probDist4, probDist3, Matrix.cons_val_zero]
      · simp [Q, Q', probDist4, probDist3, Matrix.cons_val_one]
      · simp [P, P', probDist4, probDist3, Matrix.cons_val_one]
    simp only [derivValue]
    exact hEq

  have hL02_eq : L02 = derivValue F hReg a α c γ ha hα hc hγ hac_q hac_p := by
    let Q' := probDist3 a c ha hc hac_q
    let P' := probDist3 α γ hα hγ hac_p
    have hQ'pos := probDist3_pos a c ha hc hac_q
    have hP'pos := probDist3_pos α γ hα hγ hac_p
    have h01' : (0 : Fin 3) ≠ 1 := by decide
    have hEq : L02 = Classical.choose (hReg.has_shift2_deriv P' Q' 0 1 h01' hP'pos hQ'pos) := by
      apply hReg.deriv_local P Q P' Q' 0 2 0 1 h02 h01' hPpos hQpos hP'pos hQ'pos
      · simp [Q, Q', probDist4, probDist3, Matrix.cons_val_zero]
      · simp [P, P', probDist4, probDist3, Matrix.cons_val_zero]
      ·
        simp [Q, Q', probDist4, probDist3, Matrix.cons_val_one]
      ·
        simp [P, P', probDist4, probDist3, Matrix.cons_val_one]
    simp only [derivValue]
    exact hEq

  have hL12_eq : L12 = derivValue F hReg b β c γ hb hβ hc hγ hbc_q hbc_p := by
    let Q' := probDist3 b c hb hc hbc_q
    let P' := probDist3 β γ hβ hγ hbc_p
    have hQ'pos := probDist3_pos b c hb hc hbc_q
    have hP'pos := probDist3_pos β γ hβ hγ hbc_p
    have h01' : (0 : Fin 3) ≠ 1 := by decide
    have hEq : L12 = Classical.choose (hReg.has_shift2_deriv P' Q' 0 1 h01' hP'pos hQ'pos) := by
      apply hReg.deriv_local P Q P' Q' 1 2 0 1 h12 h01' hPpos hQpos hP'pos hQ'pos
      · simp [Q, Q', probDist4, probDist3, Matrix.cons_val_one]
      · simp [P, P', probDist4, probDist3, Matrix.cons_val_one]
      · simp [Q, Q', probDist4, probDist3, Matrix.cons_val_one]
      · simp [P, P', probDist4, probDist3, Matrix.cons_val_one]
    simp only [derivValue]
    exact hEq

  rw [hL01_eq, hL02_eq, hL12_eq] at hL01
  exact hL01

theorem shift2_deriv_ofAtom
    (d : ℝ → ℝ → ℝ)
    (d' : ℝ → ℝ → ℝ)
    (hd : ∀ q p : ℝ, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (d' q p) q)
    {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j)
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k) :
    HasDerivAt (fun t => (Objective.ofAtom d).D (shift2ProbClamp q i j hij t) p)
      (d' (q.p i) (p.p i) - d' (q.p j) (p.p j)) (q.p i) := by
  have hqi_pos : 0 < q.p i := hq i
  have hqj_pos : 0 < q.p j := hq j

  let φ : Fin n → ℝ → ℝ := fun k x => d x (p.p k)

  have hφi : HasDerivAt (fun x => φ i x) (d' (q.p i) (p.p i)) (q.p i) :=
    hd (q.p i) (p.p i) (hq i) (hp i)
  have hφj : HasDerivAt (fun x => φ j x) (d' (q.p j) (p.p j)) (q.p i + q.p j - q.p i) := by
    have : q.p i + q.p j - q.p i = q.p j := by ring
    rw [this]; exact hd (q.p j) (p.p j) (hq j) (hp j)

  have hderiv_sum : HasDerivAt (fun t => ∑ k : Fin n, d (shift2 q.p i j t k) (p.p k))
      (d' (q.p i) (p.p i) - d' (q.p j) (p.p j)) (q.p i) := by
    have h := hasDerivAt_sumObjectiveCoord_shift2 φ q.p i j (q.p i) hij
      (d' (q.p i) (p.p i)) (d' (q.p j) (p.p j)) hφi hφj

    have : (fun t => sumObjectiveCoord φ (shift2 q.p i j t)) = (fun t => ∑ k : Fin n, d (shift2 q.p i j t k) (p.p k)) := by
      ext t
      unfold sumObjectiveCoord φ
      rfl
    rw [← this]
    exact h

  have hEventuallyEq : (fun t => ∑ k : Fin n, d (shift2 q.p i j t k) (p.p k)) =ᶠ[𝓝 (q.p i)]
      (fun t => (Objective.ofAtom d).D (shift2ProbClamp q i j hij t) p) := by

    have hIoo : Set.Ioo 0 (q.p i + q.p j) ∈ 𝓝 (q.p i) :=
      Ioo_mem_nhds hqi_pos (lt_add_of_pos_right _ hqj_pos)
    apply Filter.eventuallyEq_of_mem hIoo
    intro t ht
    simp only [Objective.ofAtom]
    congr 1
    funext k
    rw [shift2ProbClamp_apply]

    have hclamp : shift2Clamp q i j t = t := shift2Clamp_eq_of_mem q i j t (le_of_lt ht.1) (le_of_lt ht.2)
    rw [hclamp]

  exact hderiv_sum.congr_of_eventuallyEq hEventuallyEq.symm

theorem deriv_local_ofAtom
    (d : ℝ → ℝ → ℝ)
    (d' : ℝ → ℝ → ℝ)
    (_hd : ∀ q p : ℝ, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (d' q p) q)
    {n m : ℕ} (p : ProbDist n) (q : ProbDist n) (p' : ProbDist m) (q' : ProbDist m)
    (i j : Fin n) (i' j' : Fin m) (_hij : i ≠ j) (_hi'j' : i' ≠ j')
    (_hp : ∀ k, 0 < p.p k) (_hq : ∀ k, 0 < q.p k)
    (_hp' : ∀ k, 0 < p'.p k) (_hq' : ∀ k, 0 < q'.p k)
    (h_qi : q.p i = q'.p i') (h_pi : p.p i = p'.p i')
    (h_qj : q.p j = q'.p j') (h_pj : p.p j = p'.p j') :
    d' (q.p i) (p.p i) - d' (q.p j) (p.p j) = d' (q'.p i') (p'.p i') - d' (q'.p j') (p'.p j') := by
  simp only [h_qi, h_pi, h_qj, h_pj]

theorem cocycle_ofAtom
    (d' : ℝ → ℝ → ℝ)
    {n : ℕ} (p q : ProbDist n) (i j k : Fin n) :
    (d' (q.p i) (p.p i) - d' (q.p j) (p.p j)) +
    (d' (q.p j) (p.p j) - d' (q.p k) (p.p k)) =
    (d' (q.p i) (p.p i) - d' (q.p k) (p.p k)) := by ring

structure HasShift2Deriv (F : ObjectiveFunctional) : Prop where
  deriv_exists :
    ∀ {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j),
      (∀ k, 0 < p.p k) → (∀ k, 0 < q.p k) →
      ∃ L : ℝ, HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (q.p i)

def IsEVMinimizer (F : ObjectiveFunctional) {n : ℕ} (p q : ProbDist n) : Prop :=
  ∃ cs : EVConstraintSet n, IsMinimizer F p (toConstraintSet cs) q

def EVRichness (F : ObjectiveFunctional) : Prop :=
  ∀ {n : ℕ} (p q : ProbDist n),
    (∀ i, 0 < p.p i) → (∀ i, 0 < q.p i) →
    IsEVMinimizer F p q

def DerivLocalAssumption (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F) : Prop :=
  ∀ {n m : ℕ} (p : ProbDist n) (q : ProbDist n) (p' : ProbDist m) (q' : ProbDist m)
    (i j : Fin n) (i' j' : Fin m) (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k)
    (hp' : ∀ k, 0 < p'.p k) (hq' : ∀ k, 0 < q'.p k),
    IsEVMinimizer F p q →
    IsEVMinimizer F p' q' →
    q.p i = q'.p i' → p.p i = p'.p i' →
    q.p j = q'.p j' → p.p j = p'.p j' →
    Classical.choose (hDiff.deriv_exists p q i j hij hp hq) =
      Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq')

def DerivRatioInvariant (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F) : Prop :=
  ∀ {n m : ℕ} (p : ProbDist n) (q : ProbDist n) (p' : ProbDist m) (q' : ProbDist m)
    (i j : Fin n) (i' j' : Fin m) (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k)
    (hp' : ∀ k, 0 < p'.p k) (hq' : ∀ k, 0 < q'.p k),
    q.p i / p.p i = q'.p i' / p'.p i' →
    q.p j / p.p j = q'.p j' / p'.p j' →
    Classical.choose (hDiff.deriv_exists p q i j hij hp hq) =
      Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq')

/-- Derivative uniqueness connects the independently differentiated atom sum to its
chosen derivative. No inference axiom is involved. -/
theorem atom_chosen_deriv (d d' : ℝ → ℝ → ℝ)
    (hd : ∀ q p, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (d' q p) q)
    {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j)
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k) :
    Classical.choose (show ∃ L, HasDerivAt
      (fun t => (ofAtom d).D (shift2ProbClamp q i j hij t) p) L (q.p i) from
        ⟨_, shift2_deriv_ofAtom d d' hd p q i j hij hp hq⟩) =
      d' (q.p i) (p.p i) - d' (q.p j) (p.p j) := by
  let ex : ∃ L, HasDerivAt
      (fun t => (ofAtom d).D (shift2ProbClamp q i j hij t) p) L (q.p i) :=
    ⟨_, shift2_deriv_ofAtom d d' hd p q i j hij hp hq⟩
  exact HasDerivAt.unique (Classical.choose_spec ex)
    (shift2_deriv_ofAtom d d' hd p q i j hij hp hq)

theorem ExtractGRegularity.ofAtom (d d' : ℝ → ℝ → ℝ)
    (hd : ∀ q p, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (d' q p) q) :
    ExtractGRegularity (ofAtom d) where
  has_shift2_deriv p q i j hij hp hq :=
    ⟨_, shift2_deriv_ofAtom d d' hd p q i j hij hp hq⟩
  deriv_local := by
    intro n m p q p' q' i j i' j' hij hi'j' hp hq hp' hq' hqi hpi hqj hpj
    rw [atom_chosen_deriv d d' hd p q i j hij hp hq,
      atom_chosen_deriv d d' hd p' q' i' j' hi'j' hp' hq', hqi, hpi, hqj, hpj]
  cocycle := by
    intro n p q i j k hij hjk hik hp hq
    rw [atom_chosen_deriv d d' hd p q i j hij hp hq,
      atom_chosen_deriv d d' hd p q j k hjk hp hq,
      atom_chosen_deriv d d' hd p q i k hik hp hq]
    ring

theorem derivRatioInvariant_ofAtom (d d' : ℝ → ℝ → ℝ)
    (hd : ∀ q p, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (d' q p) q)
    (hRatio : ∀ q p q' p', q / p = q' / p' → d' q p = d' q' p') :
    DerivRatioInvariant (ofAtom d) ⟨(ExtractGRegularity.ofAtom d d' hd).has_shift2_deriv⟩ := by
  intro n m p q p' q' i j i' j' hij hi'j' hp hq hp' hq' hi hj
  rw [atom_chosen_deriv d d' hd p q i j hij hp hq,
    atom_chosen_deriv d d' hd p' q' i' j' hi'j' hp' hq',
    hRatio _ _ _ _ hi, hRatio _ _ _ _ hj]

/-- This direct implication uses ratio invariance, not subset independence. -/
theorem derivLocal_of_ratioInvariant (F : ObjectiveFunctional) (h : HasShift2Deriv F)
    (hr : DerivRatioInvariant F h) : DerivLocalAssumption F h := by
  intro n m p q p' q' i j i' j' hij hi'j' hp hq hp' hq' _ _ hi hpi hj hpj
  exact hr p q p' q' i j i' j' hij hi'j' hp hq hp' hq'
    (by rw [hi, hpi]) (by rw [hj, hpj])

/-- A normalized, strictly positive frame realizes ratios `r`, `s`, and `1`.
The fourth coordinate retains the remaining probability mass. -/
structure RatioFrame (r s : ℝ) where
  prior : ProbDist 4
  posterior : ProbDist 4
  prior_pos : ∀ i, 0 < prior.p i
  posterior_pos : ∀ i, 0 < posterior.p i
  ratio_zero : posterior.p 0 / prior.p 0 = r
  ratio_one : posterior.p 1 / prior.p 1 = s
  ratio_two : posterior.p 2 / prior.p 2 = 1

noncomputable def ratioFrame (r s : ℝ) (hr : 0 < r) (hs : 0 < s) : RatioFrame r s := by
  let t := 1 / (4 * (1 + r + s))
  have ht : 0 < t := by dsimp [t]; positivity
  have hp : t + t + t < 1 := by
    dsimp [t]
    rw [show (1 / (4 * (1+r+s)) + 1 / (4 * (1+r+s)) + 1 / (4 * (1+r+s))) =
      3 / (4 * (1+r+s)) by ring, div_lt_one (by positivity)]
    nlinarith
  have hq : r*t + s*t + t < 1 := by
    have he : r*t + s*t + t = 1/4 := by dsimp [t]; field_simp; ring
    linarith
  refine ⟨probDist4 t t t ht ht ht hp, probDist4 (r*t) (s*t) t
    (mul_pos hr ht) (mul_pos hs ht) ht hq,
    probDist4_pos t t t ht ht ht hp,
    probDist4_pos (r*t) (s*t) t (mul_pos hr ht) (mul_pos hs ht) ht hq, ?_, ?_, ?_⟩
  all_goals simp [probDist4, ht.ne']

noncomputable def ratioDerivative (F : ObjectiveFunctional) (h : ExtractGRegularity F)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) : ℝ :=
  let f := ratioFrame r s hr hs
  Classical.choose (h.has_shift2_deriv f.prior f.posterior 0 1 (by decide)
    f.prior_pos f.posterior_pos)

/-- The four-state cocycle gives a global ratio potential. -/
theorem ratioDerivative_difference (F : ObjectiveFunctional) (h : ExtractGRegularity F)
    (hrat : DerivRatioInvariant F ⟨h.has_shift2_deriv⟩)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    ratioDerivative F h r s hr hs =
      ratioDerivative F h r 1 hr one_pos - ratioDerivative F h s 1 hs one_pos := by
  let f := ratioFrame r s hr hs
  let a := ratioFrame r 1 hr one_pos
  let b := ratioFrame s 1 hs one_pos
  have h02 := hrat f.prior f.posterior a.prior a.posterior 0 2 0 1
    (by decide) (by decide) f.prior_pos f.posterior_pos a.prior_pos a.posterior_pos
    (f.ratio_zero.trans a.ratio_zero.symm) (f.ratio_two.trans a.ratio_one.symm)
  have h12 := hrat f.prior f.posterior b.prior b.posterior 1 2 0 1
    (by decide) (by decide) f.prior_pos f.posterior_pos b.prior_pos b.posterior_pos
    (f.ratio_one.trans b.ratio_zero.symm) (f.ratio_two.trans b.ratio_one.symm)
  have hc := h.cocycle f.prior f.posterior 0 1 2 (by decide) (by decide) (by decide)
    f.prior_pos f.posterior_pos
  change ratioDerivative F h r s hr hs + _ = _ at hc
  rw [h02, h12] at hc
  exact eq_sub_of_add_eq hc

/-- Global extraction requires an explicit invariance hypothesis. The conclusion
retains the original objective and its actual derivatives in every finite dimension. -/
noncomputable def gradientRepresentation_of_ratioInvariant (F : ObjectiveFunctional)
    (h : ExtractGRegularity F) (hrat : DerivRatioInvariant F ⟨h.has_shift2_deriv⟩) :
    GradientRepresentation F := by
  let g : ℝ → ℝ → ℝ := fun x y => if hr : 0 < x/y then
    ratioDerivative F h (x/y) 1 hr one_pos else 0
  refine ⟨g, fun _ _ => 1, fun _ _ => one_ne_zero, ?_⟩
  intro n p q i j hij hp hq
  have hr := div_pos (hq i) (hp i)
  have hs := div_pos (hq j) (hp j)
  let f := ratioFrame (q.p i / p.p i) (q.p j / p.p j) hr hs
  have hm := hrat p q f.prior f.posterior i j 0 1 hij (by decide)
    hp hq f.prior_pos f.posterior_pos f.ratio_zero.symm f.ratio_one.symm
  have hd := Classical.choose_spec (h.has_shift2_deriv p q i j hij hp hq)
  change Classical.choose (h.has_shift2_deriv p q i j hij hp hq) =
    ratioDerivative F h (q.p i / p.p i) (q.p j / p.p j) hr hs at hm
  rw [hm, ratioDerivative_difference F h hrat] at hd
  simpa [g, hr, hs] using hd

/-- This particular richness predicate is automatic because the language can pin
all coordinates. It does not assert existence for an arbitrary given problem. -/
theorem evRichness_of_pointConstraints (F : ObjectiveFunctional) : EVRichness F := by
  intro n p q _ _
  refine ⟨pointConstraints q, ?_⟩
  rw [toConstraintSet_pointConstraints]
  exact ⟨Set.mem_singleton _, fun r hr => by rw [Set.mem_singleton_iff.mp hr]⟩

/-- Assemble locality and an actual directional-gradient certificate. Inference
axioms are not inputs to this analytic construction. -/
theorem regularity_of_localGradient (F : ObjectiveFunctional) (hd : HasShift2Deriv F)
    (hl : DerivLocalAssumption F hd)
    (hg : ∀ {n : ℕ} (p q : ProbDist n) (hp : ∀ i, 0 < p.p i) (hq : ∀ i, 0 < q.p i),
      ∃ g : Fin n → ℝ, ∀ (i j : Fin n) (hij : i ≠ j),
        Classical.choose (hd.deriv_exists p q i j hij hp hq) = g i - g j) :
    ExtractGRegularity F where
  has_shift2_deriv := hd.deriv_exists
  deriv_local := by
    intro n m p q p' q' i j i' j' hij hi'j' hp hq hp' hq' hqi hpi hqj hpj
    exact hl p q p' q' i j i' j' hij hi'j' hp hq hp' hq'
      (evRichness_of_pointConstraints F p q hp hq)
      (evRichness_of_pointConstraints F p' q' hp' hq') hqi hpi hqj hpj
  cocycle := by
    intro n p q i j k hij hjk hik hp hq
    obtain ⟨g, he⟩ := hg p q hp hq
    rw [he i j hij, he j k hjk, he i k hik]
    ring

end KnuthSkilling.ShoreJohnson.GradientSeparability
