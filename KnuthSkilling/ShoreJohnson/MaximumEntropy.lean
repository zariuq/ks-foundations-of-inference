import KnuthSkilling.ShoreJohnson.KLWitness

/-!
# Maximum entropy and the discrete prior-preservation boundary

The four structural inference laws do not force dependence on the prior.
Negative Shannon entropy supplies a concrete alternative objective. Its
minimizer relation satisfies the same finite laws while ignoring prior values.
The null-information law distinguishes it from relative-entropy inference.

Reference: Johnson and Shore (1983), https://zenodo.org/records/1281600
-/
namespace KnuthSkilling.ShoreJohnson.MaximumEntropy
open Classical Finset
open scoped BigOperators
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Proof
open KnuthSkilling.ShoreJohnson.Inference
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.KL
open KnuthSkilling.ShoreJohnson.KLWitness
open KnuthSkilling.ShoreJohnson.AppendixKL

noncomputable def entropyAtom (x _ : ℝ) : ℝ := x*Real.log x
noncomputable def entropyObjective : ObjectiveFunctional := ofAtom entropyAtom
private noncomputable def rawEntropy : InferenceMethod := minimizerMethod entropyObjective

private theorem klValue_const_reference {ι : Type*} [Fintype ι] (p x : ι → ℝ)
    (c : ℝ) (hc : 0 < c) (hp : ∀ i, p i = c) (hx : ∑ i, x i = 1) :
    klValue p x = (∑ i, x i*Real.log (x i)) - Real.log c := by
  unfold klValue
  simp_rw [hp, klAtom_eq_mul_log_sub _ c hc, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hx, one_mul]

private theorem entropy_min_iff_kl {n : ℕ} (p u : ProbDist n) (c : ℝ) (hc : 0 < c)
    (hu : ∀ i, u.p i = c) (C : ConstraintSet n) (q : ProbDist n) :
    IsMinimizer entropyObjective p C q ↔ IsMinimizer (ofAtom klAtom) u C q := by
  constructor
  · intro h
    refine ⟨h.1, fun r hr => ?_⟩
    change klValue u.p q.p ≤ klValue u.p r.p
    rw [klValue_const_reference u.p q.p c hc hu q.sum_one,
      klValue_const_reference u.p r.p c hc hu r.sum_one]
    exact sub_le_sub_right (h.2 r hr) _
  · intro h
    refine ⟨h.1, fun r hr => ?_⟩
    have hh := h.2 r hr
    change klValue u.p q.p ≤ klValue u.p r.p at hh
    rw [klValue_const_reference u.p q.p c hc hu q.sum_one,
      klValue_const_reference u.p r.p c hc hu r.sum_one] at hh
    exact (sub_le_sub_iff_right _).mp hh

private theorem entropy_minProd_iff_kl {n m : ℕ} (p u : ProbDistProd n m)
    (c : ℝ) (hc : 0 < c) (hu : ∀ i, u.p i = c) (C : ConstraintSetProd n m)
    (q : ProbDistProd n m) :
    IsMinimizerProd entropyObjective p C q ↔ IsMinimizerProd (ofAtom klAtom) u C q := by
  constructor
  · intro h
    refine ⟨h.1, fun r hr => ?_⟩
    change klValue u.p q.p ≤ klValue u.p r.p
    rw [klValue_const_reference u.p q.p c hc hu q.sum_one,
      klValue_const_reference u.p r.p c hc hu r.sum_one]
    exact sub_le_sub_right (h.2 r hr) _
  · intro h
    refine ⟨h.1, fun r hr => ?_⟩
    have hh := h.2 r hr
    change klValue u.p q.p ≤ klValue u.p r.p at hh
    rw [klValue_const_reference u.p q.p c hc hu q.sum_one,
      klValue_const_reference u.p r.p c hc hu r.sum_one] at hh
    exact (sub_le_sub_iff_right _).mp hh

noncomputable def uniformFor {n : ℕ} (p : ProbDist n) : ProbDist n :=
  uniformDist n (ProbDist.dimension_pos p)

lemma uniformFor_pos {n : ℕ} (p : ProbDist n) (i : Fin n) : 0 < (uniformFor p).p i := by
  dsimp [uniformFor, uniformDist]
  have := ProbDist.dimension_pos p
  positivity

private theorem rawEntropy_unique {n : ℕ} (p : ProbDist n) (C : ConstraintSet n)
    (ha : Admissible p C) (q r : ProbDist n) (hq : rawEntropy.Infer p C q)
    (hr : rawEntropy.Infer p C r) : q = r := by
  let u := uniformFor p
  have hc : 0 < (1 : ℝ)/n := uniformFor_pos p ⟨0, ProbDist.dimension_pos p⟩
  exact klInference_axioms.unique u C ⟨uniformFor_pos p, ha.2⟩ q r
    ⟨uniformFor_pos p, (entropy_min_iff_kl p u _ hc (fun _ => rfl) C q).mp hq⟩
    ⟨uniformFor_pos p, (entropy_min_iff_kl p u _ hc (fun _ => rfl) C r).mp hr⟩

private theorem rawEntropy_uniqueProd {n m : ℕ} (p : ProbDistProd n m) (C : ConstraintSetProd n m)
    (ha : AdmissibleProd p C) (q r : ProbDistProd n m)
    (hq : rawEntropy.InferProd p C q) (hr : rawEntropy.InferProd p C r) : q = r := by
  let u := uniformFor (ProbDistProd.marginalLeft p)
  let v := uniformFor (ProbDistProd.marginalRight p)
  have huv : ∀ ij, 0 < (u ⊗ v).p ij := fun ij =>
    mul_pos (uniformFor_pos _ ij.1) (uniformFor_pos _ ij.2)
  have hc : 0 < ((1 : ℝ)/n)*((1 : ℝ)/m) := huv
    (⟨0, ProbDist.dimension_pos (ProbDistProd.marginalLeft p)⟩,
      ⟨0, ProbDist.dimension_pos (ProbDistProd.marginalRight p)⟩)
  exact klInference_axioms.uniqueProd (u ⊗ v) C ⟨huv, ha.2⟩ q r
    ⟨huv, (entropy_minProd_iff_kl p (u ⊗ v) _ hc (fun _ => rfl) C q).mp hq⟩
    ⟨huv, (entropy_minProd_iff_kl p (u ⊗ v) _ hc (fun _ => rfl) C r).mp hr⟩

private theorem rawEntropy_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbDist n)
    (C : ConstraintSet n) (q : ProbDist n) (hq : rawEntropy.Infer p C q) :
    rawEntropy.Infer (ProbDist.permute σ p) (ConstraintSet.permute σ C) (ProbDist.permute σ q) := by
  let u := uniformFor p
  have hc : 0 < (1 : ℝ)/n := uniformFor_pos p ⟨0, ProbDist.dimension_pos p⟩
  have h := klInference_axioms.perm_invariant σ u C q
    ⟨uniformFor_pos p, (entropy_min_iff_kl p u _ hc (fun _ => rfl) C q).mp hq⟩
  exact (entropy_min_iff_kl (ProbDist.permute σ p) (ProbDist.permute σ u) _ hc
    (fun _ => rfl) _ _).mpr h.2

private theorem rawEntropy_system {n m : ℕ} (p₁ : ProbDist n) (p₂ : ProbDist m)
    (C₁ : ConstraintSet n) (C₂ : ConstraintSet m) (q₁ : ProbDist n) (q₂ : ProbDist m)
    (Q : ProbDistProd n m) (ha₁ : Admissible p₁ C₁) (ha₂ : Admissible p₂ C₂)
    (h₁ : rawEntropy.Infer p₁ C₁ q₁) (h₂ : rawEntropy.Infer p₂ C₂ q₂)
    (hQ : rawEntropy.InferProd (p₁ ⊗ p₂) (ConstraintSetProd.product C₁ C₂) Q) : Q = q₁ ⊗ q₂ := by
  let u := uniformFor p₁
  let v := uniformFor p₂
  have hc : 0 < (1 : ℝ)/n := uniformFor_pos p₁ ⟨0, ProbDist.dimension_pos p₁⟩
  have hd : 0 < (1 : ℝ)/m := uniformFor_pos p₂ ⟨0, ProbDist.dimension_pos p₂⟩
  exact klInference_axioms.system_independent u v C₁ C₂ q₁ q₂ Q
    ⟨uniformFor_pos p₁, ha₁.2⟩ ⟨uniformFor_pos p₂, ha₂.2⟩
    ⟨uniformFor_pos p₁, (entropy_min_iff_kl p₁ u _ hc (fun _ => rfl) C₁ q₁).mp h₁⟩
    ⟨uniformFor_pos p₂, (entropy_min_iff_kl p₂ v _ hd (fun _ => rfl) C₂ q₂).mp h₂⟩
    ⟨fun ij => mul_pos (uniformFor_pos _ ij.1) (uniformFor_pos _ ij.2),
      (entropy_minProd_iff_kl (p₁ ⊗ p₂) (u ⊗ v) _ (mul_pos hc hd)
        (fun _ => rfl) _ Q).mp hQ⟩

lemma mul_log_scale (c x : ℝ) :
    (c*x)*Real.log (c*x) = c*(x*Real.log x) + (c*Real.log c)*x := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [Real.log_mul hc0 hx0]
  ring

lemma sum_mul_log_scale {n : ℕ} (c : ℝ) (q : ProbDist n) :
    (∑ i, (c*q.p i)*Real.log (c*q.p i)) = c*(∑ i, q.p i*Real.log (q.p i)) + c*Real.log c := by
  simp_rw [mul_log_scale c _, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, q.sum_one, mul_one]

private theorem rawEntropy_axioms : ShoreJohnsonAxioms rawEntropy where
  unique := rawEntropy_unique
  uniqueProd := rawEntropy_uniqueProd
  feasible h := h.1
  feasibleProd h := h.1
  perm_invariant := rawEntropy_permute
  system_independent := rawEntropy_system
  subset_independent_twoBlock := by
    intro n m w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ h₁ h₂ hQ
    apply subset_independent_of_block_formula entropyObjective rawEntropy_unique
      w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ h₁ h₂ hQ
      (w*Real.log w + (1-w)*Real.log (1-w))
    intro r₁ _ r₂ _
    change (ofAtom entropyAtom).D _ _ = _
    rw [sum_atom_twoBlock]
    simp only [entropyAtom]
    rw [sum_mul_log_scale w r₁, sum_mul_log_scale (1-w) r₂]
    change _ = w*(∑ i, r₁.p i*Real.log (r₁.p i)) +
      (1-w)*(∑ i, r₂.p i*Real.log (r₂.p i)) + _
    ring

noncomputable def maximumEntropy : InferenceMethod := positiveMinimizerMethod entropyObjective

theorem maximumEntropy_axioms : ShoreJohnsonAxioms maximumEntropy :=
  positiveMinimizerMethod_axioms entropyObjective rawEntropy_axioms

theorem maximumEntropy_infers_uniform {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i) :
    maximumEntropy.Infer p Set.univ (uniformFor p) := by
  refine ⟨hp, (entropy_min_iff_kl p (uniformFor p) _
    (uniformFor_pos p ⟨0, ProbDist.dimension_pos p⟩) (fun _ => rfl) _ _).mpr ?_⟩
  exact (klInference_priorPreservation (uniformFor p) (uniformFor_pos p)).2


/-- A positive prior that is not the maximum-entropy answer to null information. -/
noncomputable def skewPrior : ProbDist 2 :=
  GradientSeparability.simplexFin2 (1/3) (by norm_num) (by norm_num)

lemma skewPrior_pos : ∀ i, 0 < skewPrior.p i := by
  intro i
  fin_cases i <;> norm_num [skewPrior, GradientSeparability.simplexFin2]

theorem maximumEntropy_not_priorPreservation : ¬ PriorPreservation maximumEntropy := by
  intro h
  have ha : Admissible skewPrior Set.univ := by
    simpa [toConstraintSet, satisfiesSet] using admissible_ev skewPrior [] skewPrior_pos
  have he := maximumEntropy_axioms.unique skewPrior Set.univ ha skewPrior (uniformFor skewPrior)
    (h skewPrior skewPrior_pos) (maximumEntropy_infers_uniform skewPrior skewPrior_pos)
  have hi := congrArg (fun q : ProbDist 2 => q.p 0) he
  norm_num [skewPrior, GradientSeparability.simplexFin2, uniformFor, uniformDist] at hi

/-- The finite structural laws admit a prior-ignoring inference method. -/
theorem four_laws_do_not_imply_priorPreservation :
    ∃ I : InferenceMethod, ShoreJohnsonAxioms I ∧ ¬ PriorPreservation I :=
  ⟨maximumEntropy, maximumEntropy_axioms, maximumEntropy_not_priorPreservation⟩

end KnuthSkilling.ShoreJohnson.MaximumEntropy
