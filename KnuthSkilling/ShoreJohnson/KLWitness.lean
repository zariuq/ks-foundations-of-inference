import KnuthSkilling.ShoreJohnson.GradientSeparability
import KnuthSkilling.ShoreJohnson.AppendixKL
import KnuthSkilling.Information.InformationEntropyMathlib
import KnuthSkilling.ShoreJohnson.KLDerivation
import KnuthSkilling.ShoreJohnson.OperatorAtomBridge
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite KL inference and its analytic models

Positive-reference KL projection inhabits the partial inference laws. Compactness
supplies existence; strict convexity supplies uniqueness. Ratio-invariant
derivatives, the conditional positive-scale conclusion, and a nonlinear
objective with the same minimizers have independently checked constructions.
Extended KL retains the unsupported boundary; the real-valued inference
interpretation is explicitly restricted to positive references.
-/

namespace KnuthSkilling.ShoreJohnson.KLWitness

open Classical Finset
open scoped BigOperators ENNReal
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Proof
open KnuthSkilling.ShoreJohnson.Inference
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.AppendixKL
open KnuthSkilling.ShoreJohnson.AppendixTheoremI
open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.KL

open KnuthSkilling.ShoreJohnson.AppendixKL.KLStationary
open KnuthSkilling.ShoreJohnson.GradientSeparability

/-- First-argument derivative of `klAtom` in the positive regime. -/
noncomputable def klAtomDeriv (q p : ℝ) : ℝ :=
  Real.log (q / p) + 1

lemma hasDerivAt_klAtom_pos (q p : ℝ) (hq : 0 < q) (hp : 0 < p) :
    HasDerivAt (fun t => klAtom t p) (klAtomDeriv q p) q := by
  simpa [klAtomDeriv, gKL] using (hasDerivAt_klAtom q p hq hp)

lemma klAtomDeriv_ratio (q p q' p' : ℝ) (h : q / p = q' / p') :
    klAtomDeriv q p = klAtomDeriv q' p' := by
  simp [klAtomDeriv, h]

/-- KL atom objective satisfies ratio-invariant derivatives. -/
theorem derivRatioInvariant_klAtom :
    DerivRatioInvariant (ofAtom klAtom)
      ⟨(ExtractGRegularity.ofAtom klAtom klAtomDeriv hasDerivAt_klAtom_pos).has_shift2_deriv⟩ := by
  exact derivRatioInvariant_ofAtom klAtom klAtomDeriv hasDerivAt_klAtom_pos klAtomDeriv_ratio


/-- The finite value uses the supplied coordinate arrays. -/
noncomputable def klValue {ι : Type*} [Fintype ι] (p x : ι → ℝ) : ℝ :=
  ∑ i, klAtom (x i) (p i)

theorem continuous_klValue {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    Continuous (klValue p) := by
  apply continuous_finsetSum
  intro i _
  simp_rw [klAtom_eq_mul_log_sub _ _ (hp i)]
  exact (Real.continuous_mul_log.comp (continuous_apply i)).sub
    ((continuous_apply i).mul continuous_const)

theorem strictConvexOn_klValue {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    StrictConvexOn ℝ (stdSimplex ℝ ι) (klValue p) :=
  strictConvexOn_sum_coordinates (fun i w => klAtom w (p i))
    (fun i => strictConvexOn_klAtom (p i) (hp i))

noncomputable def indexDistribution {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) : ProbDist (Fintype.card ι) where
  p i := x ((Fintype.equivFin ι).symm i)
  nonneg i := hx _
  sum_one := by rw [Equiv.sum_comp (Fintype.equivFin ι).symm]; exact hs

theorem klValue_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (hs : ∀ i, q i ≠ 0 → 0 < p i) : 0 ≤ klValue p q := by
  let P := indexDistribution p hp hps
  let Q := indexDistribution q hq hqs
  have hs' : ∀ i, Q.p i ≠ 0 → 0 < P.p i := fun i => hs _
  have h := klDivergence_nonneg' Q P hs'
  rw [← KnuthSkilling.ShoreJohnson.Bridge.sum_klAtom_eq_klDivergence Q P hs'] at h
  change 0 ≤ ∑ i, klAtom (q ((Fintype.equivFin ι).symm i)) (p ((Fintype.equivFin ι).symm i)) at h
  rwa [Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => klAtom (q i) (p i))] at h

theorem klValue_eq_zero_iff {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (hs : ∀ i, q i ≠ 0 → 0 < p i) : klValue p q = 0 ↔ q = p := by
  constructor
  · intro hz
    let P := indexDistribution p hp hps
    let Q := indexDistribution q hq hqs
    have hs' : ∀ i, Q.p i ≠ 0 → 0 < P.p i := fun i => hs _
    have hd : klDivergence Q P hs' = 0 := by
      rw [← KnuthSkilling.ShoreJohnson.Bridge.sum_klAtom_eq_klDivergence Q P hs']
      change (∑ i, klAtom (q ((Fintype.equivFin ι).symm i)) (p ((Fintype.equivFin ι).symm i))) = 0
      rwa [Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => klAtom (q i) (p i))]
    have hm : Q.toMeasureTop = P.toMeasureTop := by
      apply InformationTheory.klDiv_eq_zero_iff.mp
      rw [ProbDist.klDiv_toMeasureTop_eq_of_support_pos Q P hs', hd]
      simp
    have he := ProbDist.toMeasureTop_injective hm
    funext i
    have hi := congrArg (fun D : ProbDist (Fintype.card ι) => D.p (Fintype.equivFin ι i)) he
    simpa [P, Q, indexDistribution] using hi
  · intro he
    subst q
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : p i = 0 <;> simp [klAtom, hi]

/-- Existence is proved for the nonempty compact affine feasible region. -/
theorem exists_kl_minimizer {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (hne : (toConstraintSet cs).Nonempty) :
    ∃ q, IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q :=
  exists_minimizer_of_compact (ofAtom klAtom) p (toConstraintSet cs) (klValue p.p)
    (fun _ => rfl) (compact_ev_coordinates cs) hne (continuous_klValue p.p hp).continuousOn

private noncomputable def atomInference : InferenceMethod := minimizerMethod (ofAtom klAtom)

private theorem atomInference_unique {n : ℕ} (p : ProbDist n) (C : ConstraintSet n)
    (ha : Admissible p C) (q r : ProbDist n)
    (hq : atomInference.Infer p C q) (hr : atomInference.Infer p C r) : q = r :=
  minimizer_unique_of_strictConvex (ofAtom klAtom) p C (klValue p.p) (fun _ => rfl)
    ha.2.1 (strictConvexOn_klValue p.p ha.1) q r hq hr


theorem klValue_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (p q : ProbDist n) :
    klValue (ProbDist.permute σ p).p (ProbDist.permute σ q).p = klValue p.p q.p :=
  Equiv.sum_comp σ⁻¹ (fun i => klAtom (q.p i) (p.p i))

private theorem atomInference_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbDist n)
    (C : ConstraintSet n) (q : ProbDist n) (hq : atomInference.Infer p C q) :
    atomInference.Infer (ProbDist.permute σ p) (ConstraintSet.permute σ C) (ProbDist.permute σ q) := by
  refine ⟨(ConstraintSet.mem_permute σ C q).mpr hq.1, fun r hr => ?_⟩
  change klValue (ProbDist.permute σ p).p (ProbDist.permute σ q).p ≤
    klValue (ProbDist.permute σ p).p r.p
  rw [klValue_permute]
  have hh := hq.2 (ProbDist.permute σ⁻¹ r) hr
  have he := klValue_permute σ⁻¹ (ProbDist.permute σ p) r
  simp only [ProbDist.permute_inv_permute] at he
  change klValue p.p q.p ≤ klValue p.p (ProbDist.permute σ⁻¹ r).p at hh
  rwa [he] at hh

theorem klValue_self {ι : Type*} [Fintype ι] (p : ι → ℝ) : klValue p p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : p i = 0 <;> simp [klAtom, hi]

private theorem atomInference_priorPreservation : PriorPreservation atomInference := by
  intro n p hp
  refine ⟨Set.mem_univ p, fun q _ => ?_⟩
  change klValue p.p p.p ≤ klValue p.p q.p
  rw [klValue_self]
  exact klValue_nonneg p.p q.p p.nonneg q.nonneg p.sum_one q.sum_one (fun i _ => hp i)

theorem klValue_product {n m : ℕ} (p₁ q₁ : ProbDist n) (p₂ q₂ : ProbDist m)
    (hp₁ : ∀ i, 0 < p₁.p i) (hp₂ : ∀ i, 0 < p₂.p i) :
    klValue (p₁ ⊗ p₂).p (q₁ ⊗ q₂).p = klValue p₁.p q₁.p + klValue p₂.p q₂.p := by
  let : NeZero n := ⟨Nat.ne_of_gt (ProbDist.dimension_pos p₁)⟩
  let : NeZero m := ⟨Nat.ne_of_gt (ProbDist.dimension_pos p₂)⟩
  exact OperatorAtomBridge.klAtom_productAdditiveAtom_pos q₁ p₁ q₂ p₂ hp₁ hp₂

/-- A joint distribution is supported by the product of its own marginals. -/
theorem marginal_product_support {n m : ℕ} (Q : ProbDistProd n m) (ij : Fin n × Fin m)
    (h : Q.p ij ≠ 0) :
    0 < ((ProbDistProd.marginalLeft Q) ⊗ (ProbDistProd.marginalRight Q)).p ij := by
  have hq : 0 < Q.p ij := lt_of_le_of_ne (Q.nonneg ij) h.symm
  exact mul_pos (lt_of_lt_of_le hq
    (Finset.single_le_sum (fun j _ => Q.nonneg (ij.1,j)) (Finset.mem_univ ij.2)))
    (lt_of_lt_of_le hq
    (Finset.single_le_sum (fun i _ => Q.nonneg (i,ij.2)) (Finset.mem_univ ij.1)))

/-- The residual term is mutual information. Its support premise follows from
marginalization, even when some marginals vanish. -/
theorem klValue_joint_decomposition {n m : ℕ} (p₁ : ProbDist n) (p₂ : ProbDist m)
    (hp₁ : ∀ i, 0 < p₁.p i) (hp₂ : ∀ i, 0 < p₂.p i) (Q : ProbDistProd n m) :
    klValue (p₁ ⊗ p₂).p Q.p =
      klValue ((ProbDistProd.marginalLeft Q) ⊗ (ProbDistProd.marginalRight Q)).p Q.p +
      klValue p₁.p (ProbDistProd.marginalLeft Q).p +
      klValue p₂.p (ProbDistProd.marginalRight Q).p := by
  let l := ProbDistProd.marginalLeft Q
  let r := ProbDistProd.marginalRight Q
  have hd (ij : Fin n × Fin m) :
      klAtom (Q.p ij) ((p₁ ⊗ p₂).p ij) = klAtom (Q.p ij) ((l ⊗ r).p ij) +
        Q.p ij * gKL (l.p ij.1) (p₁.p ij.1) + Q.p ij * gKL (r.p ij.2) (p₂.p ij.2) := by
    by_cases ht : Q.p ij = 0
    · simp [ht, klAtom]
    have hs := marginal_product_support Q ij ht
    change 0 < l.p ij.1 * r.p ij.2 at hs
    have hboth : 0 < l.p ij.1 ∧ 0 < r.p ij.2 :=
      (mul_pos_iff.mp hs).resolve_right (fun h => (l.nonneg ij.1).not_gt h.1)
    have hl' := hboth.1
    have hr := hboth.2
    simp only [productDist]
    rw [klAtom_eq_mul_log_sub _ _ (mul_pos (hp₁ _) (hp₂ _)),
      klAtom_eq_mul_log_sub _ _ hs, gKL_pos_pos _ _ hl' (hp₁ _),
      gKL_pos_pos _ _ hr (hp₂ _)]
    rw [Real.log_mul (hp₁ _).ne' (hp₂ _).ne', Real.log_mul hl'.ne' hr.ne']
    ring
  unfold klValue
  simp_rw [hd, Finset.sum_add_distrib]
  congr 1
  · congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul]
    rfl
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rfl


private theorem atomInference_system_independent {n m : ℕ} (p₁ : ProbDist n) (p₂ : ProbDist m)
    (C₁ : ConstraintSet n) (C₂ : ConstraintSet m) (q₁ : ProbDist n) (q₂ : ProbDist m)
    (Q : ProbDistProd n m) (ha₁ : Admissible p₁ C₁) (ha₂ : Admissible p₂ C₂)
    (hq₁ : atomInference.Infer p₁ C₁ q₁) (hq₂ : atomInference.Infer p₂ C₂ q₂)
    (hQ : atomInference.InferProd (p₁ ⊗ p₂) (ConstraintSetProd.product C₁ C₂) Q) :
    Q = q₁ ⊗ q₂ := by
  let l := ProbDistProd.marginalLeft Q
  let r := ProbDistProd.marginalRight Q
  have hmem : l ∈ C₁ ∧ r ∈ C₂ := hQ.1
  have hlval : klValue p₁.p q₁.p ≤ klValue p₁.p l.p := hq₁.2 l hmem.1
  have hrval : klValue p₂.p q₂.p ≤ klValue p₂.p r.p := hq₂.2 r hmem.2
  have hfeas : (q₁ ⊗ q₂) ∈ ConstraintSetProd.product C₁ C₂ := by
    change ProbDistProd.marginalLeft (q₁ ⊗ q₂) ∈ C₁ ∧
      ProbDistProd.marginalRight (q₁ ⊗ q₂) ∈ C₂
    simpa using And.intro hq₁.1 hq₂.1
  have hupper : klValue (p₁ ⊗ p₂).p Q.p ≤ klValue p₁.p q₁.p + klValue p₂.p q₂.p := by
    rw [← klValue_product p₁ q₁ p₂ q₂ ha₁.1 ha₂.1]
    exact hQ.2 (q₁ ⊗ q₂) hfeas
  have hnonneg : 0 ≤ klValue (l ⊗ r).p Q.p :=
    klValue_nonneg (l ⊗ r).p Q.p (l ⊗ r).nonneg Q.nonneg (l ⊗ r).sum_one Q.sum_one
      (marginal_product_support Q)
  have hdecomp := klValue_joint_decomposition p₁ p₂ ha₁.1 ha₂.1 Q
  change klValue (p₁ ⊗ p₂).p Q.p = klValue (l ⊗ r).p Q.p +
    klValue p₁.p l.p + klValue p₂.p r.p at hdecomp
  have hz : klValue (l ⊗ r).p Q.p = 0 := by linarith
  have heL : klValue p₁.p l.p = klValue p₁.p q₁.p := by linarith
  have heR : klValue p₂.p r.p = klValue p₂.p q₂.p := by linarith
  have hlmin : atomInference.Infer p₁ C₁ l := by
    refine ⟨hmem.1, fun x hx => ?_⟩
    change klValue p₁.p l.p ≤ klValue p₁.p x.p
    rw [heL]
    exact hq₁.2 x hx
  have hrmin : atomInference.Infer p₂ C₂ r := by
    refine ⟨hmem.2, fun x hx => ?_⟩
    change klValue p₂.p r.p ≤ klValue p₂.p x.p
    rw [heR]
    exact hq₂.2 x hx
  have hleq := atomInference_unique p₁ C₁ ha₁ l q₁ hlmin hq₁
  have hreq := atomInference_unique p₂ C₂ ha₂ r q₂ hrmin hq₂
  have he := (klValue_eq_zero_iff (l ⊗ r).p Q.p (l ⊗ r).nonneg Q.nonneg
    (l ⊗ r).sum_one Q.sum_one (marginal_product_support Q)).mp hz
  apply ProbDistProd.ext
  intro ij
  rw [hleq, hreq] at he
  exact congrFun he ij


theorem klValue_twoBlock {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p₁ q₁ : ProbDist n) (p₂ q₂ : ProbDist m) :
    klValue (ProbDist.twoBlock w hw0 hw1 p₁ p₂).p (ProbDist.twoBlock w hw0 hw1 q₁ q₂).p =
      w*klValue p₁.p q₁.p + (1-w)*klValue p₂.p q₂.p := by
  change (ofAtom klAtom).D _ _ = _
  rw [sum_atom_twoBlock]
  simp_rw [klAtom_scale, ← Finset.mul_sum]
  rfl

private theorem atomInference_uniqueProd {n m : ℕ} (p : ProbDistProd n m) (C : ConstraintSetProd n m)
    (ha : AdmissibleProd p C) (q r : ProbDistProd n m)
    (hq : atomInference.InferProd p C q) (hr : atomInference.InferProd p C r) : q = r := by
  have hsub : (fun q : ProbDistProd n m => q.p) '' C ⊆ stdSimplex ℝ (Fin n × Fin m) := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x.nonneg, x.sum_one⟩
  have hm (x : ProbDistProd n m) (hx : atomInference.InferProd p C x) :
      IsMinOn (klValue p.p) ((fun q : ProbDistProd n m => q.p) '' C) x.p := by
    rintro _ ⟨z, hz, rfl⟩
    exact hx.2 z hz
  have he := ((strictConvexOn_klValue p.p ha.1).subset hsub ha.2.1).eq_of_isMinOn
    (hm q hq) (hm r hr) ⟨q, hq.1, rfl⟩ ⟨r, hr.1, rfl⟩
  exact ProbDistProd.ext q r (fun i => congrFun he i)

/-- A concrete inhabitant of the repaired laws; no existence clause is assumed. -/
private theorem atomInference_axioms : ShoreJohnsonAxioms atomInference where
  unique := atomInference_unique
  uniqueProd := atomInference_uniqueProd
  feasible h := h.1
  feasibleProd h := h.1
  perm_invariant := atomInference_permute
  system_independent := atomInference_system_independent
  subset_independent_twoBlock := by
    intro n m w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ hq₁ hq₂ hQ
    apply subset_independent_of_block_formula (ofAtom klAtom) atomInference_unique
      w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ hq₁ hq₂ hQ 0
    intro r₁ _ r₂ _
    simpa [klValue, ofAtom] using klValue_twoBlock w hw0 hw1 p₁ r₁ p₂ r₂


/-- KL inference on the positive-reference finite profile. Unsupported reference
problems have no verdict here; their divergence is represented by extended KL. -/
noncomputable def klInference : InferenceMethod := positiveMinimizerMethod (ofAtom klAtom)

theorem klInference_axioms : ShoreJohnsonAxioms klInference :=
  positiveMinimizerMethod_axioms (ofAtom klAtom) atomInference_axioms

theorem klInference_priorPreservation : PriorPreservation klInference := by
  intro n p hp
  exact ⟨hp, atomInference_priorPreservation p hp⟩

theorem exists_unique_klInference {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (hne : (toConstraintSet cs).Nonempty) :
    ∃! q, klInference.Infer p (toConstraintSet cs) q := by
  apply Inference.unique_of_solvable klInference_axioms p (toConstraintSet cs) (admissible_ev p cs hp)
  obtain ⟨q, hq⟩ := exists_kl_minimizer p hp cs hne
  exact ⟨q, hp, hq⟩


/-- Separately inferred posteriors actually construct a joint inferred posterior.
This supplies the forward direction of the system-independence correspondence. -/
theorem klInference_product {n m : ℕ} (p₁ q₁ : ProbDist n) (p₂ q₂ : ProbDist m)
    (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
    (h₁ : klInference.Infer p₁ C₁ q₁) (h₂ : klInference.Infer p₂ C₂ q₂) :
    klInference.InferProd (p₁ ⊗ p₂) (ConstraintSetProd.product C₁ C₂) (q₁ ⊗ q₂) := by
  refine ⟨fun ij => mul_pos (h₁.1 ij.1) (h₂.1 ij.2), ?_, fun Q hQ => ?_⟩
  · change ProbDistProd.marginalLeft (q₁ ⊗ q₂) ∈ C₁ ∧ ProbDistProd.marginalRight (q₁ ⊗ q₂) ∈ C₂
    simpa using And.intro h₁.2.1 h₂.2.1
  · change klValue (p₁ ⊗ p₂).p (q₁ ⊗ q₂).p ≤ klValue (p₁ ⊗ p₂).p Q.p
    rw [klValue_product p₁ q₁ p₂ q₂ h₁.1 h₂.1, klValue_joint_decomposition p₁ p₂ h₁.1 h₂.1 Q]
    let l := ProbDistProd.marginalLeft Q
    let r := ProbDistProd.marginalRight Q
    have hl : klValue p₁.p q₁.p ≤ klValue p₁.p l.p := h₁.2.2 l hQ.1
    have hr : klValue p₂.p q₂.p ≤ klValue p₂.p r.p := h₂.2.2 r hQ.2
    have hz := klValue_nonneg (l ⊗ r).p Q.p (l ⊗ r).nonneg Q.nonneg
      (l ⊗ r).sum_one Q.sum_one (marginal_product_support Q)
    change _ ≤ klValue (l ⊗ r).p Q.p + klValue p₁.p l.p + klValue p₂.p r.p
    linarith

/-- The positive-reference block construction also preserves inferred results. -/
theorem klInference_twoBlock {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (p₁ q₁ : ProbDist n) (p₂ q₂ : ProbDist m) (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
    (h₁ : klInference.Infer p₁ C₁ q₁) (h₂ : klInference.Infer p₂ C₂ q₂) :
    klInference.Infer (ProbDist.twoBlock w hw0.le hw1.le p₁ p₂)
      (ConstraintSet.twoBlock w hw0.le hw1.le C₁ C₂) (ProbDist.twoBlock w hw0.le hw1.le q₁ q₂) := by
  refine ⟨?_, ⟨q₁, h₁.2.1, q₂, h₂.2.1, rfl⟩, ?_⟩
  · intro k
    cases hh : (finSumFinEquiv (m := n) (n := m)).symm k with
    | inl i => simpa [ProbDist.twoBlock, hh] using mul_pos hw0 (h₁.1 i)
    | inr j => simpa [ProbDist.twoBlock, hh] using mul_pos (sub_pos.mpr hw1) (h₂.1 j)
  · intro Q hQ
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hQ
    change klValue (ProbDist.twoBlock w hw0.le hw1.le p₁ p₂).p
      (ProbDist.twoBlock w hw0.le hw1.le q₁ q₂).p ≤
      klValue (ProbDist.twoBlock w hw0.le hw1.le p₁ p₂).p
        (ProbDist.twoBlock w hw0.le hw1.le r₁ r₂).p
    rw [klValue_twoBlock, klValue_twoBlock]
    exact add_le_add (mul_le_mul_of_nonneg_left (h₁.2.2 r₁ hr₁) hw0.le)
      (mul_le_mul_of_nonneg_left (h₂.2.2 r₂ hr₂) (sub_nonneg.mpr hw1.le))

/-- A nontrivial inhabitant of the conditional analytic KL pipeline. -/
noncomputable def klProfile : KLDerivation.SeparableKLProfile where
  I := klInference
  F := ofAtom klAtom
  d := klAtom
  realizesEV := realizesEVPositive_positiveMinimizerMethod (ofAtom klAtom)
  appendix :=
    { g := gKL
      scale := fun _ _ => 1
      scale_ne := fun _ _ => one_ne_zero
      F_shift2_deriv := by
        intro n p q i j hij hp hq
        simpa [klAtomDeriv, gKL] using shift2_deriv_ofAtom klAtom klAtomDeriv hasDerivAt_klAtom_pos p q i j hij hp hq
      stationary_iff_isMinimizer_F := by
        intro n p hp cs q hq hpos
        exact stationaryEV_iff_isMinimizer_ofAtom_klAtom p hp cs q hq hpos
      stationary_iff_isMinimizer_ofAtom := by
        intro n p hp cs q hq hpos
        exact stationaryEV_iff_isMinimizer_ofAtom_klAtom p hp cs q hq hpos }
  regularAtom := fun u => by simp [klAtom]
  ratio := ⟨Real.log, fun _ _ _ _ => rfl⟩
  gMul := fun _ _ hx hy => Real.log_mul hx.ne' hy.ne'
  gMeas := Real.measurable_log
  d1Meas := by
    change Measurable (fun x : ℝ => 1 * Real.log (1/x))
    fun_prop

/-- The extended bridge detects singularity rather than assigning it the atom's junk value. -/
theorem unsupported_pointMass_divergence :
    klDivergenceTop (ProbDist.pointMass (0 : Fin 2)) (ProbDist.pointMass 1) = ⊤ :=
  ProbDist.klDivergenceTop_pointMass_ne (by decide)


/-- Prior preservation fixes the direction of optimization: zero and negative
multipliers are ruled out by a genuine two-state comparison and uniqueness. -/
theorem positive_scale_of_priorPreservation (h : KLDerivation.SeparableKLProfile)
    (hSJ : ShoreJohnsonAxioms h.I) (hPrior : PriorPreservation h.I) :
    ∃ C : ℝ, 0 < C ∧ ∀ w u, 0 < w → 0 < u → h.d w u = C*klAtom w u := by
  obtain ⟨C, hC⟩ := KLDerivation.d_eq_const_mul_klAtom h
  let p : ProbDist 2 := uniformDist 2 (by decide)
  let r : ProbDist 2 := simplexFin2 (1/3) (by norm_num) (by norm_num)
  have hp : ∀ i, 0 < p.p i := by intro i; norm_num [p, uniformDist]
  have hr : ∀ i, 0 < r.p i := by intro i; fin_cases i <;> norm_num [r, simplexFin2]
  have hne : r.p ≠ p.p := by
    intro he
    have hi := congrFun he 0
    norm_num [r, p, simplexFin2, uniformDist] at hi
  have hD : 0 < klValue p.p r.p := by
    have hnonneg := klValue_nonneg p.p r.p p.nonneg r.nonneg p.sum_one r.sum_one (fun i _ => hp i)
    have hneq : klValue p.p r.p ≠ 0 := fun hz => hne
      ((klValue_eq_zero_iff p.p r.p p.nonneg r.nonneg p.sum_one r.sum_one (fun i _ => hp i)).mp hz)
    exact lt_of_le_of_ne hnonneg hneq.symm
  have hIp : h.I.Infer p (toConstraintSet []) p := by
    simpa [toConstraintSet, satisfiesSet] using hPrior p hp
  have hmin := (KLDerivation.infer_iff_scaledKL_of_identity h C hC p [] p hp hp).mp hIp
  have hb := hmin.2 r (by simp [toConstraintSet, satisfiesSet])
  change (∑ i, C*klAtom (p.p i) (p.p i)) ≤ ∑ i, C*klAtom (r.p i) (p.p i) at hb
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hb
  change C*klValue p.p p.p ≤ C*klValue p.p r.p at hb
  rw [klValue_self, mul_zero] at hb
  have hCnonneg : 0 ≤ C := nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hb) hD
  have hCne : C ≠ 0 := by
    intro hz
    have hminr : IsMinimizer (ofAtom (fun w u => C*klAtom w u)) p (toConstraintSet []) r := by
      refine ⟨by simp [toConstraintSet, satisfiesSet], fun _ _ => ?_⟩
      simp [ofAtom, hz]
    have hIr := (KLDerivation.infer_iff_scaledKL_of_identity h C hC p [] r hp hr).mpr hminr
    have he := hSJ.unique p (toConstraintSet []) (admissible_ev p [] hp) r p hIr hIp
    exact hne (congrArg (fun q : ProbDist 2 => q.p) he)
  exact ⟨C, lt_of_le_of_ne hCnonneg hCne.symm, hC⟩

/-- This conditional conclusion retains the profile's ratio/Cauchy/analytic
premises. It does not assert that the five operator laws derive those premises. -/
theorem infer_iff_kl_of_priorPreservation (h : KLDerivation.SeparableKLProfile)
    (hSJ : ShoreJohnsonAxioms h.I) (hPrior : PriorPreservation h.I)
    {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : ∀ i, 0 < q.p i) :
    h.I.Infer p (toConstraintSet cs) q ↔ IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q := by
  obtain ⟨C, hc, hC⟩ := positive_scale_of_priorPreservation h hSJ hPrior
  exact (KLDerivation.infer_iff_scaledKL_of_identity h C hC p cs q hp hq).trans
    (isMinimizer_const_mul_ofAtom_iff C hc klAtom p (toConstraintSet cs) q).symm

/-- A boundary posterior forced by affine observations is still inferred. -/
theorem forced_boundary_posterior :
    let p := uniformDist 2 (by decide)
    let q := ProbDist.pointMass (0 : Fin 2)
    klInference.Infer p (toConstraintSet (pointConstraints q)) q ∧ q.p 1 = 0 := by
  dsimp only
  constructor
  · refine ⟨fun i => by norm_num [uniformDist], ?_⟩
    rw [toConstraintSet_pointConstraints]
    exact ⟨Set.mem_singleton _, fun r hr => by rw [Set.mem_singleton_iff.mp hr]⟩
  · simp [ProbDist.pointMass]


/-- A nonlinear change of objective preserves selected posteriors while changing values. -/
noncomputable def expKLObjective : ObjectiveFunctional := transform (ofAtom klAtom) Real.exp

theorem expKL_same_minimizers : ObjEquiv (ofAtom klAtom) expKLObjective :=
  objEquiv_transform (ofAtom klAtom) Real.exp Real.exp_strictMono

noncomputable def klDerivative {n : ℕ} (p q : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, klAtomDeriv (q i) (p i) • ContinuousLinearMap.proj i

theorem hasFDerivAt_klValue {n : ℕ} (p q : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    HasFDerivAt (klValue p) (klDerivative p q) q := by
  apply HasFDerivAt.fun_sum
  intro i _
  exact (hasDerivAt_klAtom_pos (q i) (p i) (hq i) (hp i)).comp_hasFDerivAt q
    (ContinuousLinearMap.hasFDerivAt (f := (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) (x := q))

noncomputable def expKLGradient : GradientRepresentation expKLObjective where
  g := klAtomDeriv
  scale p q := Real.exp (klValue p.p q.p)
  scale_ne_zero p q := (Real.exp_pos _).ne'
  shift2_deriv := by
    intro n p q i j hij hp hq
    have h := (shift2_deriv_ofAtom klAtom klAtomDeriv hasDerivAt_klAtom_pos p q i j hij hp hq).exp
    simpa [expKLObjective, transform, klValue, ofAtom,
      AppendixMinimizer.shift2ProbClamp_at_qi_eq_q] using h

theorem convexOn_expKL {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    ConvexOn ℝ (stdSimplex ℝ (Fin n)) (fun x => Real.exp (klValue p x)) := by
  have hc := (strictConvexOn_klValue p hp).convexOn
  refine ⟨hc.1, fun x hx y hy a b ha hb hab => ?_⟩
  exact (Real.exp_le_exp.mpr (hc.2 hx hy ha hb hab)).trans
    (convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab)

/-- An independent use of the reconstructed variational theorem, with a nonlinear
objective rather than the atom sum used as its own validation. -/
theorem expKL_minimizers_via_gradient {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (q : ProbDist n) (hq : q ∈ toConstraintSet cs)
    (hpos : ∀ i, 0 < q.p i) :
    IsMinimizer expKLObjective p (toConstraintSet cs) q ↔
      IsMinimizer (ofAtom klAtom) p (toConstraintSet cs) q := by
  exact TheoremI.sumForm_positive_minimizers_of_convex_gradient expKLObjective expKLGradient
    klAtom hasDerivAt_klAtom_pos (fun u hu => (strictConvexOn_klAtom u hu).convexOn)
    p hp cs (fun x => Real.exp (klValue p.p x)) (fun _ => rfl)
    (convexOn_expKL p.p hp) q hq hpos _ (hasFDerivAt_klValue p.p q.p hp hpos).exp

theorem expKL_changes_values (p : ProbDist 2) :
    expKLObjective.D p p ≠ (ofAtom klAtom).D p p := by
  change Real.exp (klValue p.p p.p) ≠ klValue p.p p.p
  rw [klValue_self]
  norm_num


noncomputable def projectionPrior : ProbDist 3 := uniformDist 3 (by decide)
noncomputable def projectionPosterior : ProbDist 3 :=
  GradientSeparability.probDist3 (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num)
noncomputable def projectionConstraints : EVConstraintSet 3 := [⟨Pi.single 0 1, 1/2⟩]

/-- A nontrivial projection and an independent nonlinear objective have the same
selected posterior, by the rebuilt variational comparison. -/
theorem three_state_projection :
    klInference.Infer projectionPrior (toConstraintSet projectionConstraints) projectionPosterior ∧
    (positiveMinimizerMethod expKLObjective).Infer projectionPrior
      (toConstraintSet projectionConstraints) projectionPosterior := by
  have hp : ∀ i, 0 < projectionPrior.p i := by intro i; norm_num [projectionPrior, uniformDist]
  have hpos : ∀ i, 0 < projectionPosterior.p i := by
    intro i; fin_cases i <;> norm_num [projectionPosterior, GradientSeparability.probDist3]
  have hq : projectionPosterior ∈ toConstraintSet projectionConstraints := by
    simp [toConstraintSet, satisfiesSet, satisfies, projectionConstraints,
      projectionPosterior, GradientSeparability.probDist3, Pi.single_apply]
  have hs : StationaryEV gKL projectionPrior projectionPosterior projectionConstraints := by
    let β := gKL (projectionPosterior.p 1) (projectionPrior.p 1)
    let lam := gKL (projectionPosterior.p 0) (projectionPrior.p 0) - β
    refine ⟨β, (fun _ : Fin 1 => lam), ?_⟩
    intro i
    change gKL (projectionPosterior.p i) (projectionPrior.p i) =
      β + ∑ _ : Fin 1, lam * (Pi.single (0 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) i
    rw [Fin.sum_univ_one]
    fin_cases i <;> simp [β, lam, projectionPosterior, projectionPrior,
      GradientSeparability.probDist3, uniformDist]
    all_goals ring
  have hm := isMinimizer_ofAtom_klAtom_of_stationaryEV projectionPrior hp projectionConstraints
    projectionPosterior hq hpos hs
  exact ⟨⟨hp, hm⟩, hp, (expKL_minimizers_via_gradient projectionPrior hp projectionConstraints
    projectionPosterior hq hpos).mpr hm⟩

/-- A genuine tie outside the convex domain; feasibility is not uniqueness. -/
theorem nonconvex_kl_tie :
    ∃ (p q r : ProbDist 2) (C : ConstraintSet 2), q ≠ r ∧
      klInference.Infer p C q ∧ klInference.Infer p C r ∧ ¬ Admissible p C := by
  let p := uniformDist 2 (by decide)
  let q := ProbDist.pointMass (0 : Fin 2)
  let r := ProbDist.pointMass (1 : Fin 2)
  let C : ConstraintSet 2 := {q, r}
  have hp : ∀ i, 0 < p.p i := by intro i; norm_num [p, uniformDist]
  have he : (ofAtom klAtom).D q p = (ofAtom klAtom).D r p := by
    simp [ofAtom, klAtom, p, q, r, uniformDist, ProbDist.pointMass]
  have hq : klInference.Infer p C q := by
    refine ⟨hp, by simp [C], fun x hx => ?_⟩
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    obtain rfl | rfl := hx
    · exact le_rfl
    · exact he.le
  have hr : klInference.Infer p C r := by
    refine ⟨hp, by simp [C], fun x hx => ?_⟩
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    obtain rfl | rfl := hx
    · exact he.ge
    · exact le_rfl
  have hne : q ≠ r := by
    intro hh
    have hi := congrArg (fun x : ProbDist 2 => x.p 0) hh
    norm_num [q, r, ProbDist.pointMass] at hi
  exact ⟨p, q, r, C, hne, hq, hr, fun ha => hne (klInference_axioms.unique p C ha q r hq hr)⟩

private theorem permuted_pointMass {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ProbDist.permute σ (ProbDist.pointMass i) = ProbDist.pointMass (σ i) := by
  ext j
  have he : σ⁻¹ j = i ↔ j = σ i := by
    constructor
    · intro h
      simpa using congrArg σ h
    · rintro rfl; simp
  simp only [ProbDist.permute, ProbDist.pointMass, he]

/-- A three-cycle distinguishes forward transport from using the forward action
as its own inverse. Swaps alone cannot expose this mistake. -/
theorem three_cycle_constraint_transport :
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    let q := ProbDist.pointMass (0 : Fin 3)
    ProbDist.permute σ q ∈ ConstraintSet.permute σ {q} ∧
      ProbDist.permute σ (ProbDist.permute σ q) ≠ q := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have h0 : σ 0 = 1 := by decide
  have h1 : σ 1 = 2 := by decide
  dsimp only
  constructor
  · exact (ConstraintSet.mem_permute _ _ _).mpr (Set.mem_singleton _)
  · intro hh
    change ProbDist.permute σ (ProbDist.permute σ (ProbDist.pointMass 0)) = ProbDist.pointMass 0 at hh
    rw [permuted_pointMass, permuted_pointMass, h0, h1] at hh
    have hi := congrArg (fun x : ProbDist 3 => x.p 0) hh
    have hn : (0 : Fin 3) ≠ 2 := by decide
    simp [ProbDist.pointMass, hn] at hi

/-- Nonempty open probability constraints need not attain a minimum of a linear observation. -/
theorem open_region_no_coordinate_minimum :
    (∃ q : ProbDist 2, 0 < q.p 0) ∧
      ¬ ∃ q : ProbDist 2, 0 < q.p 0 ∧ ∀ r : ProbDist 2, 0 < r.p 0 → q.p 0 ≤ r.p 0 := by
  refine ⟨⟨ProbDist.pointMass 0, by norm_num [ProbDist.pointMass]⟩, ?_⟩
  rintro ⟨q, hq, hm⟩
  have ht : 0 < q.p 0 / 2 := by linarith
  have ht1 : q.p 0 / 2 < 1 := by have := ProbabilityTheory.Foundations.Distributions.ProbDist.le_one q 0; linarith
  let r := simplexFin2 (q.p 0 / 2) ht ht1
  have hr : 0 < r.p 0 := ht
  have hh := hm r hr
  change q.p 0 ≤ q.p 0 / 2 at hh
  linarith

end KnuthSkilling.ShoreJohnson.KLWitness
