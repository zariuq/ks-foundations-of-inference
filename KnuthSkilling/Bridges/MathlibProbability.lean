import KnuthSkilling.Information.InformationEntropyMathlib
import KnuthSkilling.Core.ScaleCompleteness
import KnuthSkilling.Additive.Axioms.OpIsAddition
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Probability observations as Mathlib measures

The finite construction retains atomic weights, all event probabilities and
extended KL, including infinity at support violations. It is faithful on
probability distributions. A supplied KS event model reaches this construction
through its explicit representation and positive-total normalization.
`SigmaAdditiveMeasureData` separately packages supplied countably additive data;
its measure constructor does not prove those premises from finite operator laws.
-/

namespace KnuthSkilling.MathlibProbability
open MeasureTheory Classical
open KnuthSkilling.Information
open scoped BigOperators ENNReal

namespace FiniteProbDist
variable {n : ℕ}

noncomputable def toProbabilityMeasure (P : InformationEntropy.ProbDist n) :
    @ProbabilityMeasure (Fin n) ⊤ :=
  ⟨P.toMeasureTop, InformationEntropy.ProbDist.instIsProbabilityMeasure_toMeasureTop P⟩

@[simp] theorem toProbabilityMeasure_toMeasure (P : InformationEntropy.ProbDist n) :
    (toProbabilityMeasure P : Measure (Fin n)) = P.toMeasureTop := rfl

theorem toProbabilityMeasure_singleton (P : InformationEntropy.ProbDist n) (i : Fin n) :
    (toProbabilityMeasure P : Measure (Fin n)) {i} = ENNReal.ofReal (P.p i) := by simp

theorem toProbabilityMeasure_univ (P : InformationEntropy.ProbDist n) :
    (toProbabilityMeasure P : Measure (Fin n)) Set.univ = 1 := by simp

/-- Every finite event has the supplied sum of atomic weights. -/
theorem toProbabilityMeasure_apply (P : InformationEntropy.ProbDist n) (s : Set (Fin n)) :
    (toProbabilityMeasure P : Measure (Fin n)) s =
      ENNReal.ofReal (∑ i, if i ∈ s then P.p i else 0) := by
  rw [toProbabilityMeasure_toMeasure]
  change Divergence.Countable.toMeasure P.p s = _
  rw [Divergence.Countable.toMeasure, Measure.sum_apply _ (show MeasurableSet s from trivial),
    tsum_fintype, ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs; exact P.nonneg i; exact le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [Measure.smul_apply, Measure.dirac_apply', hi]

/-- Equality of interpreted measures reflects equality of supplied probabilities. -/
theorem toProbabilityMeasure_injective : Function.Injective (toProbabilityMeasure (n := n)) := by
  intro P Q h
  exact InformationEntropy.ProbDist.toMeasureTop_injective
    (congrArg (fun μ : @ProbabilityMeasure (Fin n) ⊤ => (μ : Measure (Fin n))) h)

/-- Extended KL commutes with this interpretation without a support premise. -/
theorem klDiv_toProbabilityMeasure (P Q : InformationEntropy.ProbDist n) :
    @InformationTheory.klDiv (Fin n) ⊤ (toProbabilityMeasure P : Measure (Fin n))
      (toProbabilityMeasure Q : Measure (Fin n)) = InformationEntropy.klDivergenceTop P Q :=
  InformationEntropy.ProbDist.klDiv_toMeasureTop_eq_klDivergenceTop P Q

theorem klDiv_toProbabilityMeasure_eq_top (P Q : InformationEntropy.ProbDist n) (i : Fin n)
    (hP : P.p i ≠ 0) (hQ : Q.p i = 0) :
    @InformationTheory.klDiv (Fin n) ⊤ (toProbabilityMeasure P : Measure (Fin n))
      (toProbabilityMeasure Q : Measure (Fin n)) = ⊤ :=
  InformationEntropy.ProbDist.klDiv_toMeasureTop_eq_top_of_support_violation P Q i hP hQ
end FiniteProbDist

/-- Countable additivity is input data, not a consequence of normalization. -/
structure SigmaAdditiveMeasureData (E : Type*) [MeasurableSpace E] where
  /-- The valuation function assigning real values to measurable sets -/
  μ : Set E → ℝ
  /-- Non-negativity -/
  μ_nonneg : ∀ s : Set E, MeasurableSet s → 0 ≤ μ s
  /-- Empty set has measure 0 -/
  μ_empty : μ ∅ = 0
  /-- σ-additivity for disjoint countable unions -/
  μ_sigma_additive : ∀ ⦃f : ℕ → Set E⦄,
    (∀ n, MeasurableSet (f n)) →
    Pairwise (Function.onFun Disjoint f) →
    (Summable (μ ∘ f)) ∧ μ (⋃ n, f n) = ∑' n, μ (f n)

namespace SigmaAdditiveMeasureData

variable {E : Type*} [MeasurableSpace E]

/-- Convert SigmaAdditiveMeasureData to a mathlib Measure. -/
noncomputable def toMeasure (m : SigmaAdditiveMeasureData E) : Measure E :=
  Measure.ofMeasurable
    (fun s _ => ENNReal.ofReal (m.μ s))
    (by simp [m.μ_empty])
    (by
      intro f hf hd
      have h_nonneg : ∀ n, 0 ≤ m.μ (f n) := fun n => m.μ_nonneg (f n) (hf n)
      obtain ⟨h_sum, h_eq⟩ := m.μ_sigma_additive hf hd
      rw [h_eq, ENNReal.ofReal_tsum_of_nonneg h_nonneg h_sum])

/-- The measure assigns the expected value to measurable sets. -/
theorem toMeasure_apply (m : SigmaAdditiveMeasureData E) (s : Set E) (hs : MeasurableSet s) :
    m.toMeasure s = ENNReal.ofReal (m.μ s) :=
  Measure.ofMeasurable_apply s hs

end SigmaAdditiveMeasureData

end KnuthSkilling.MathlibProbability
