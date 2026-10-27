import KnuthSkilling.Information.Divergence
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Countable weights, discrete measures and extended KL

Nonnegative weights are faithfully interpreted as weighted Dirac measures.
Extended divergence retains unsupported source mass as infinity. For summable
weights it equals Mathlib's measure divergence, without a support premise.
The real-valued series instead needs support compatibility and summability.
The explicit discrete natural-number interpretation is a specialization.
-/

namespace KnuthSkilling.Information.Divergence
open scoped BigOperators ENNReal NNReal
open Classical MeasureTheory Real

namespace Countable
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Interpret real weights as atomic masses; negative weights are clipped by `ofReal`. -/
noncomputable def toMeasure (w : α → ℝ) : Measure α :=
  Measure.sum fun a => ENNReal.ofReal (w a) • Measure.dirac a

omit [Countable α] in
@[simp] theorem toMeasure_apply_singleton (w : α → ℝ) (a : α) :
    toMeasure w {a} = ENNReal.ofReal (w a) := by
  classical
  rw [toMeasure, Measure.sum_apply _ (measurableSet_singleton a)]
  simp [Measure.smul_apply, Measure.dirac_apply', Set.indicator, Set.mem_singleton_iff]

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem toMeasure_univ (w : α → ℝ) :
    toMeasure w Set.univ = ∑' a, ENNReal.ofReal (w a) := by
  simp [toMeasure, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply]

omit [Countable α] [MeasurableSingletonClass α] in
theorem isFiniteMeasure_toMeasure (w : α → ℝ) (hw : Summable w) :
    IsFiniteMeasure (toMeasure w) :=
  ⟨by simpa only [toMeasure_univ, lt_top_iff_ne_top] using hw.tsum_ofReal_ne_top⟩

omit [Countable α] in
/-- The interpretation reflects equality on nonnegative weights. -/
theorem toMeasure_inj (w u : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hu : ∀ a, 0 ≤ u a) :
    toMeasure w = toMeasure u ↔ w = u := by
  constructor
  · intro h
    funext a
    have hmass := congrArg (fun μ : Measure α => μ {a}) h
    simpa only [toMeasure_apply_singleton, ENNReal.ofReal_eq_ofReal_iff (hw a) (hu a)] using hmass
  · rintro rfl; rfl

/-- Adding nonnegative masses commutes with their measure interpretation. -/
theorem toMeasure_add (w u : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hu : ∀ a, 0 ≤ u a) :
    toMeasure (fun a => w a + u a) = toMeasure w + toMeasure u := by
  apply Measure.ext_of_singleton
  intro a
  simp [ENNReal.ofReal_add (hw a) (hu a)]

/-- Nonnegative coefficient states carry an additive, law-preserving measure observation. -/
noncomputable def massObservation : (α → ℝ≥0) →+ Measure α where
  toFun w := toMeasure (fun a => (w a : ℝ))
  map_zero' := by apply Measure.ext_of_singleton; intro a; simp
  map_add' w u := toMeasure_add _ _ (fun a => (w a).coe_nonneg) (fun a => (u a).coe_nonneg)

/-- Summing authored mass updates and interpreting them equals summing their interpreted updates. -/
theorem observe_updates (updates : List (α → ℝ≥0)) :
    toMeasure (fun a => (updates.sum a : ℝ)) =
      (updates.map (fun w => toMeasure (fun a => (w a : ℝ)))).sum :=
  massObservation.map_list_sum updates

/-- Extended divergence includes singular atoms, even when the reference mass is zero. -/
noncomputable def divergenceInfTop (w u : α → ℝ) : ℝ≥0∞ :=
  ∑' a, atomDivergenceENNReal (ENNReal.ofReal (w a)) (ENNReal.ofReal (u a))

/-- A real `tsum`; its interpretation as a finite divergence requires summability. -/
noncomputable def divergenceInfCountable (w u : α → ℝ) : ℝ :=
  ∑' a, atomDivergenceExt (w a) (u a)

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem divergenceInfTop_eq_series_of_support (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hSupport : ∀ a, w a ≠ 0 → 0 < u a) :
    divergenceInfTop w u = ∑' a, ENNReal.ofReal (atomDivergenceExt (w a) (u a)) := by
  exact tsum_congr fun a => atomDivergenceENNReal_ofReal_of_support _ _ (hw a) (hSupport a)

theorem toMeasure_eq_withDensity (w u : α → ℝ)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a) :
    toMeasure w = (toMeasure u).withDensity (fun a => ENNReal.ofReal (w a) / ENNReal.ofReal (u a)) := by
  apply Measure.ext_of_singleton
  intro a
  by_cases hwa : w a = 0
  · simp [hwa, withDensity_apply]
  · have hu0 := (ENNReal.ofReal_pos.mpr (hSupport a hwa)).ne'
    have hc := ENNReal.mul_div_cancel (a := ENNReal.ofReal (u a))
      (b := ENNReal.ofReal (w a)) hu0 ENNReal.ofReal_ne_top
    simp [withDensity_apply, hc]

/-- Historical supported-case interface, derived from the actual density. -/
theorem klDiv_toMeasure_eq_divergenceInfTop (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hu : ∀ a, 0 ≤ u a)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a)
    (hw_sum : Summable w) (hu_sum : Summable u) :
    InformationTheory.klDiv (toMeasure w) (toMeasure u) = divergenceInfTop w u := by
  let μ := toMeasure w
  let ν := toMeasure u
  let dens := fun a => ENNReal.ofReal (w a) / ENNReal.ofReal (u a)
  let : IsFiniteMeasure μ := isFiniteMeasure_toMeasure w hw_sum
  let : IsFiniteMeasure ν := isFiniteMeasure_toMeasure u hu_sum
  have hwd : μ = ν.withDensity dens := toMeasure_eq_withDensity w u hSupport
  have hmeas : Measurable dens := measurable_of_countable dens
  have hac : μ ≪ ν := hwd ▸ withDensity_absolutelyContinuous ν dens
  have hrn : μ.rnDeriv ν =ᵐ[ν] dens := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity ν hmeas
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac,
    divergenceInfTop_eq_series_of_support w u hw hSupport]
  calc
    _ = ∫⁻ a, ENNReal.ofReal (InformationTheory.klFun ((dens a).toReal)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with a ha
      rw [ha]
    _ = ∑' a, ENNReal.ofReal (InformationTheory.klFun ((dens a).toReal)) * ν {a} :=
      lintegral_countable' _
    _ = _ := by
      apply tsum_congr
      intro a
      simp only [ν, toMeasure_apply_singleton]
      by_cases hua : u a = 0
      · have hwa : w a = 0 := by
          by_contra h; exact (hSupport a h).ne' hua
        simp [hua, hwa]
      · have hup := (hu a).lt_of_ne' hua
        have hd : (dens a).toReal = w a / u a := by
          simp [dens, ENNReal.toReal_div, ENNReal.toReal_ofReal, hw a, hu a]
        rw [hd, mul_comm, ← ENNReal.ofReal_mul (hu a),
          atomDivergenceExt_eq_mul_klFun _ _ (hw a) hup]

/-- Finite source and reference masses suffice; support failure gives infinity on both sides. -/
theorem klDiv_toMeasure_eq_divergenceInfTop_all (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hu : ∀ a, 0 ≤ u a)
    (hw_sum : Summable w) (hu_sum : Summable u) :
    InformationTheory.klDiv (toMeasure w) (toMeasure u) = divergenceInfTop w u := by
  by_cases hSupport : ∀ a, w a ≠ 0 → 0 < u a
  · exact klDiv_toMeasure_eq_divergenceInfTop w u hw hu hSupport hw_sum hu_sum
  · push Not at hSupport
    obtain ⟨a, hwa, hua⟩ := hSupport
    have hz : u a = 0 := le_antisymm hua (hu a)
    have hp : 0 < w a := (hw a).lt_of_ne' hwa
    have ht : divergenceInfTop w u = ⊤ :=
      ENNReal.tsum_eq_top_of_eq_top ⟨a, by
        simp [atomDivergenceENNReal, hz, (ENNReal.ofReal_pos.mpr hp).ne']⟩
    rw [ht]
    apply InformationTheory.klDiv_of_not_ac
    intro hac
    have h := hac (show toMeasure u {a} = 0 by simp [hz])
    exact (ENNReal.ofReal_pos.mpr hp).ne' (by simpa using h)

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem divergenceInfTop_eq_ofReal_divergenceInfCountable (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hu : ∀ a, 0 ≤ u a)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a)
    (hSum : Summable (fun a => atomDivergenceExt (w a) (u a))) :
    divergenceInfTop w u = ENNReal.ofReal (divergenceInfCountable w u) := by
  rw [divergenceInfTop_eq_series_of_support w u hw hSupport]
  apply (ENNReal.ofReal_tsum_of_nonneg _ hSum).symm
  intro a
  by_cases hua : u a = 0
  · have hwa : w a = 0 := by
      by_contra h; exact (hSupport a h).ne' hua
    simp [hua, hwa]
  · exact atomDivergenceExt_nonneg _ _ (hw a) ((hu a).lt_of_ne' hua)

theorem klDiv_toMeasure_eq_ofReal_divergenceInfCountable (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hu : ∀ a, 0 ≤ u a)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a)
    (hw_sum : Summable w) (hu_sum : Summable u)
    (hSum : Summable (fun a => atomDivergenceExt (w a) (u a))) :
    InformationTheory.klDiv (toMeasure w) (toMeasure u) =
      ENNReal.ofReal (divergenceInfCountable w u) := by
  rw [klDiv_toMeasure_eq_divergenceInfTop w u hw hu hSupport hw_sum hu_sum,
    divergenceInfTop_eq_ofReal_divergenceInfCountable w u hw hu hSupport hSum]
end Countable

namespace Seq
local instance : MeasurableSpace ℕ := ⊤
local instance instMeasurableSingletonClassNatTop : @MeasurableSingletonClass ℕ ⊤ :=
  ⟨fun _ => by simp⟩

/-- Discrete natural-number specialization of the same atomic interpretation. -/
noncomputable def toMeasureTop (w : ℕ → ℝ) : @Measure ℕ ⊤ := Countable.toMeasure w

@[simp] theorem toMeasureTop_apply_singleton (w : ℕ → ℝ) (n : ℕ) :
    toMeasureTop w {n} = ENNReal.ofReal (w n) := Countable.toMeasure_apply_singleton w n

@[simp] theorem toMeasureTop_univ (w : ℕ → ℝ) :
    toMeasureTop w Set.univ = ∑' n, ENNReal.ofReal (w n) := Countable.toMeasure_univ w

theorem isFiniteMeasure_toMeasureTop (w : ℕ → ℝ) (hw : Summable w) :
    IsFiniteMeasure (toMeasureTop w) := Countable.isFiniteMeasure_toMeasure w hw

noncomputable def divergenceInfTop (w u : ℕ → ℝ) : ℝ≥0∞ := Countable.divergenceInfTop w u

theorem toMeasureTop_eq_withDensity (w u : ℕ → ℝ)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n) :
    toMeasureTop w = (toMeasureTop u).withDensity (fun n => ENNReal.ofReal (w n) / ENNReal.ofReal (u n)) :=
  Countable.toMeasure_eq_withDensity w u hSupport

theorem klDiv_toMeasureTop_eq_divergenceInfTop (w u : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hu : ∀ n, 0 ≤ u n)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n) (hw_sum : Summable w) (hu_sum : Summable u) :
    @InformationTheory.klDiv ℕ ⊤ (toMeasureTop w) (toMeasureTop u) = divergenceInfTop w u :=
  Countable.klDiv_toMeasure_eq_divergenceInfTop w u hw hu hSupport hw_sum hu_sum

theorem divergenceInfTop_eq_ofReal_divergenceInf (w u : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hu : ∀ n, 0 ≤ u n)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n)
    (hSum : Summable (fun n => atomDivergenceExt (w n) (u n))) :
    divergenceInfTop w u = ENNReal.ofReal (divergenceInf w u) :=
  Countable.divergenceInfTop_eq_ofReal_divergenceInfCountable w u hw hu hSupport hSum

theorem klDiv_toMeasureTop_eq_ofReal_divergenceInf (w u : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hu : ∀ n, 0 ≤ u n)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n) (hw_sum : Summable w) (hu_sum : Summable u)
    (hSum : Summable (fun n => atomDivergenceExt (w n) (u n))) :
    @InformationTheory.klDiv ℕ ⊤ (toMeasureTop w) (toMeasureTop u) =
      ENNReal.ofReal (divergenceInf w u) :=
  Countable.klDiv_toMeasure_eq_ofReal_divergenceInfCountable w u hw hu hSupport hw_sum hu_sum hSum

/-- A singular atom is infinite, whereas clipping the real formula loses it. -/
theorem unsupported_atom_control :
    divergenceInfTop (fun n => if n = 0 then 1 else 0) (fun _ => 0) = ⊤ ∧
      (∑' n : ℕ, ENNReal.ofReal (atomDivergenceExt (if n = 0 then 1 else 0) 0)) = 0 := by
  constructor
  · exact ENNReal.tsum_eq_top_of_eq_top ⟨0, by norm_num [atomDivergenceENNReal]⟩
  · have h : ∀ n : ℕ,
        ENNReal.ofReal (atomDivergenceExt (if n = 0 then 1 else 0) 0) = 0 := by
      intro n
      split_ifs <;> norm_num [atomDivergenceExt]
    simp only [h, tsum_zero]

/-- Equality reflection would fail for signed weights. -/
theorem negative_weight_invisible :
    toMeasureTop (fun _ => -1) = toMeasureTop (fun _ => 0) ∧
      (fun _ : ℕ => (-1 : ℝ)) ≠ (fun _ => 0) := by
  constructor
  · simp [toMeasureTop, Countable.toMeasure]
  · intro h; have := congrFun h 0; norm_num at this
end Seq
end KnuthSkilling.Information.Divergence
