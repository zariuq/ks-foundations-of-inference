import KnuthSkilling.Information.InformationEntropy
import KnuthSkilling.Information.DivergenceMathlib

/-!
# Finite probability distributions as discrete measures

The finite interpretation is the countable atomic construction. Normalization
makes it a probability measure, and the shared extended divergence theorem
handles supported and singular pairs. Real KL identities retain their support
premises, while the extended identity is unconditional.
-/

namespace KnuthSkilling.Information.InformationEntropy
open scoped BigOperators ENNReal
open Classical MeasureTheory Real
open KnuthSkilling.Information.Divergence

namespace ProbDist
variable {n : ℕ}
local instance : MeasurableSpace (Fin n) := ⊤
local instance : @MeasurableSingletonClass (Fin n) ⊤ := ⟨fun _ => by simp⟩

/-- Interpret the supplied finite weights using the shared atomic construction. -/
noncomputable def toMeasureTop (P : ProbDist n) : @Measure (Fin n) ⊤ := Countable.toMeasure P.p

@[simp] theorem toMeasureTop_apply_singleton (P : ProbDist n) (i : Fin n) :
    P.toMeasureTop {i} = ENNReal.ofReal (P.p i) := Countable.toMeasure_apply_singleton P.p i

@[simp] theorem toMeasureTop_univ (P : ProbDist n) : P.toMeasureTop Set.univ = 1 := by
  rw [toMeasureTop, Countable.toMeasure_univ, tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.nonneg i), P.sum_one]
  simp

instance instIsProbabilityMeasure_toMeasureTop (P : ProbDist n) :
    IsProbabilityMeasure P.toMeasureTop := ⟨P.toMeasureTop_univ⟩

instance instIsFiniteMeasure_toMeasureTop (P : ProbDist n) : IsFiniteMeasure P.toMeasureTop :=
  Countable.isFiniteMeasure_toMeasure P.p (hasSum_fintype _).summable

/-- The interpretation forgets no finite probability weights. -/
theorem toMeasureTop_injective : Function.Injective (toMeasureTop (n := n)) := by
  intro P Q h
  apply ProbDist.ext
  exact congrFun ((Countable.toMeasure_inj P.p Q.p P.nonneg Q.nonneg).mp h)

theorem toMeasureTop_absolutelyContinuous_of_support_pos (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) : P.toMeasureTop ≪ Q.toMeasureTop := by
  rw [toMeasureTop, Countable.toMeasure_eq_withDensity P.p Q.p hQ_pos]
  exact withDensity_absolutelyContinuous _ _

theorem klDiv_toMeasureTop_eq_top_of_support_violation (P Q : ProbDist n) (i : Fin n)
    (hPi : P.p i ≠ 0) (hQi : Q.p i = 0) :
    @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop = ⊤ := by
  apply InformationTheory.klDiv_of_not_ac
  intro hac
  have h := hac (show Q.toMeasureTop {i} = 0 by simp [hQi])
  exact (ENNReal.ofReal_pos.mpr ((P.nonneg i).lt_of_ne' hPi)).ne' (by simpa using h)

theorem klDiv_toMeasureTop_eq_of_support_pos (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop =
      ENNReal.ofReal (klDivergence P Q hQ_pos) := by
  rw [toMeasureTop, toMeasureTop,
    Countable.klDiv_toMeasure_eq_ofReal_divergenceInfCountable P.p Q.p P.nonneg Q.nonneg hQ_pos
      (hasSum_fintype _).summable (hasSum_fintype _).summable (hasSum_fintype _).summable]
  congr 1
  simp only [Countable.divergenceInfCountable, tsum_fintype]
  have atom : ∀ i, atomDivergenceExt (P.p i) (Q.p i) = atomDivergence (P.p i) (Q.p i) := by
    intro i
    by_cases h : P.p i = 0 <;> simp [atomDivergenceExt, atomDivergence, h]
  simp_rw [atom]
  simpa [P.sum_one, Q.sum_one] using (klDivergence_from_divergence_formula P Q hQ_pos).symm

/-- Extended finite KL agrees with the actual measure divergence, including unsupported atoms. -/
theorem klDiv_toMeasureTop_eq_klDivergenceTop (P Q : ProbDist n) :
    @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop = klDivergenceTop P Q := by
  by_cases hs : ∀ i, P.p i ≠ 0 → 0 < Q.p i
  · rw [klDivergenceTop_eq_of_support_pos P Q hs, klDiv_toMeasureTop_eq_of_support_pos P Q hs]
  · obtain ⟨i, hi, hq⟩ : ∃ i, P.p i ≠ 0 ∧ Q.p i = 0 := by
      push Not at hs
      obtain ⟨i, hi, hq⟩ := hs
      exact ⟨i, hi, le_antisymm hq (Q.nonneg i)⟩
    rw [klDiv_toMeasureTop_eq_top_of_support_violation P Q i hi hq,
      klDivergenceTop_eq_top_of_support_violation P Q i hi hq]

/-- Finite and countable extended presentations agree without a support hypothesis. -/
theorem divergenceInfTop_eq_klDivergenceTop (P Q : ProbDist n) :
    Countable.divergenceInfTop P.p Q.p = klDivergenceTop P Q := by
  rw [← klDiv_toMeasureTop_eq_klDivergenceTop P Q]
  exact (Countable.klDiv_toMeasure_eq_divergenceInfTop_all P.p Q.p P.nonneg Q.nonneg
    (hasSum_fintype _).summable (hasSum_fintype _).summable).symm

theorem klDivergenceTop_self (P : ProbDist n) : klDivergenceTop P P = 0 := by
  rw [← klDiv_toMeasureTop_eq_klDivergenceTop P P, InformationTheory.klDiv_self]

/-- Distinct point masses are a normalized singular-pair control. -/
theorem klDivergenceTop_pointMass_ne {i j : Fin n} (hij : i ≠ j) :
    klDivergenceTop (ProbDist.pointMass i) (ProbDist.pointMass j) = ⊤ := by
  apply klDivergenceTop_eq_top_of_support_violation _ _ i
  · simp [ProbDist.pointMass_apply]
  · simp [ProbDist.pointMass_apply, hij]
end ProbDist
end KnuthSkilling.Information.InformationEntropy
