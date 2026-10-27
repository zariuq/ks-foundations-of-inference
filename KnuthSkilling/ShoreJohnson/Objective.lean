import KnuthSkilling.ShoreJohnson.Inference
import KnuthSkilling.ShoreJohnson.Constraints
import KnuthSkilling.ShoreJohnson.Theorem

/-!
# Shore–Johnson: objective-function layer (discrete skeleton)

Shore–Johnson (1980) is fundamentally about an **inference operator**
`p ∘ I = q` realized by minimizing some functional `H(q,p)` over a constraint set.

Our project currently has:
- an operator-level axiom interface (`Inference.lean`), and
- an objective-level functional-equation analysis yielding `log` / KL rigidity
  (`Theorem.lean`, `KL.lean`).

This file provides a small amount of glue for talking about objective-based inference in the
finite/discrete setting, without yet committing to Shore–Johnson’s full expected-value constraint
language.

No Shore–Johnson uniqueness theorem is proved here; this is infrastructure.
-/

namespace KnuthSkilling.ShoreJohnson.Objective

open Classical

open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Proof
open KnuthSkilling.ShoreJohnson.Constraints

/-! ## Objective-based inference (relation form) -/

/-- An objective functional on finite distributions. -/
structure ObjectiveFunctional where
  D : ∀ {n : ℕ}, ProbDist n → ProbDist n → ℝ
  DProd : ∀ {n m : ℕ}, ProbDistProd n m → ProbDistProd n m → ℝ

/-- `q` is a minimizer of the objective `D(·,p)` over a constraint set `C`. -/
def IsMinimizer (F : ObjectiveFunctional) {n : ℕ} (p : ProbDist n)
    (C : Inference.ConstraintSet n)
    (q : ProbDist n) : Prop :=
  q ∈ C ∧ ∀ q' ∈ C, F.D q p ≤ F.D q' p

/-- `q` is a minimizer of the product objective `DProd(·,p)` over a product constraint set. -/
def IsMinimizerProd (F : ObjectiveFunctional) {n m : ℕ} (p : ProbDistProd n m)
    (C : Inference.ConstraintSetProd n m) (q : ProbDistProd n m) : Prop :=
  q ∈ C ∧ ∀ q' ∈ C, F.DProd q p ≤ F.DProd q' p

/-! ## Objective realization and equivalence -/

/-- An inference method is realized by an objective functional. -/
structure Realizes (I : Inference.InferenceMethod) (F : ObjectiveFunctional) : Prop where
  infer_iff_minimizer :
    ∀ {n : ℕ} (p : ProbDist n) (C : Inference.ConstraintSet n) (q : ProbDist n),
      I.Infer p C q ↔ IsMinimizer F p C q
  inferProd_iff_minimizer :
    ∀ {n m : ℕ} (p : ProbDistProd n m) (C : Inference.ConstraintSetProd n m)
      (q : ProbDistProd n m),
      I.InferProd p C q ↔ IsMinimizerProd F p C q

/-- An inference method is realized by an objective functional, *restricted to expected-value
constraint sets*.

This matches the scope of Shore–Johnson's 1980 theorem, which is stated for constraints given as
expected values (affine equalities). -/
structure RealizesEV (I : Inference.InferenceMethod) (F : ObjectiveFunctional) : Prop where
  infer_iff_minimizer_ev :
    ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (q : ProbDist n),
      I.Infer p (toConstraintSet cs) q ↔ IsMinimizer F p (toConstraintSet cs) q

/-- A real-valued objective interpretation on strictly positive reference laws. -/
structure RealizesEVPositive (I : Inference.InferenceMethod) (F : ObjectiveFunctional) : Prop where
  infer_iff_minimizer_ev :
    ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (q : ProbDist n),
      (∀ i, 0 < p.p i) →
      (I.Infer p (toConstraintSet cs) q ↔ IsMinimizer F p (toConstraintSet cs) q)

theorem Realizes.toRealizesEV
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (h : Realizes I F) : RealizesEV I F := by
  refine ⟨?_⟩
  intro n p cs q
  simpa using (h.infer_iff_minimizer p (toConstraintSet cs) q)

/-- Objective-level equivalence: identical minimizers for every prior and constraint set. -/
def ObjEquiv (F G : ObjectiveFunctional) : Prop :=
  ∀ {n : ℕ} (p : ProbDist n) (C : Inference.ConstraintSet n),
    {q | IsMinimizer F p C q} = {q | IsMinimizer G p C q}

/-- Objective equivalence restricted to expected-value constraint sets. -/
def ObjEquivEV (F G : ObjectiveFunctional) : Prop :=
  ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n),
    {q | IsMinimizer F p (toConstraintSet cs) q} = {q | IsMinimizer G p (toConstraintSet cs) q}

theorem objEquivEV_isMinimizer_iff
    {F G : ObjectiveFunctional} (hEq : ObjEquivEV F G)
    {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (q : ProbDist n) :
    IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer G p (toConstraintSet cs) q := by
  have h := congrArg (fun s => q ∈ s) (hEq (n := n) p cs)
  simpa using h

theorem objEquiv_refl (F : ObjectiveFunctional) : ObjEquiv F F := by
  intro n p C
  rfl

theorem objEquivEV_refl (F : ObjectiveFunctional) : ObjEquivEV F F := by
  intro n p cs
  rfl

theorem objEquiv_symm {F G : ObjectiveFunctional} (h : ObjEquiv F G) : ObjEquiv G F := by
  intro n p C
  simpa using (h (n := n) p C).symm

theorem objEquivEV_symm {F G : ObjectiveFunctional} (h : ObjEquivEV F G) : ObjEquivEV G F := by
  intro n p cs
  simpa using (h (n := n) p cs).symm

theorem objEquiv_trans {F G H : ObjectiveFunctional} (hFG : ObjEquiv F G) (hGH : ObjEquiv G H) :
    ObjEquiv F H := by
  intro n p C
  exact (hFG (n := n) p C).trans (hGH (n := n) p C)

theorem objEquivEV_trans {F G H : ObjectiveFunctional} (hFG : ObjEquivEV F G) (hGH : ObjEquivEV G H) :
    ObjEquivEV F H := by
  intro n p cs
  exact (hFG (n := n) p cs).trans (hGH (n := n) p cs)

theorem objEquiv_of_realizes
    {I : Inference.InferenceMethod} {F G : ObjectiveFunctional}
    (hF : Realizes I F) (hG : Realizes I G) :
    ObjEquiv F G := by
  intro n p C
  ext q
  constructor
  · intro hq
    exact (hG.infer_iff_minimizer p C q).1 ((hF.infer_iff_minimizer p C q).2 hq)
  · intro hq
    exact (hF.infer_iff_minimizer p C q).1 ((hG.infer_iff_minimizer p C q).2 hq)

theorem objEquivEV_of_realizesEV
    {I : Inference.InferenceMethod} {F G : ObjectiveFunctional}
    (hF : RealizesEV I F) (hG : RealizesEV I G) :
    ObjEquivEV F G := by
  intro n p cs
  ext q
  constructor
  · intro hq
    exact (hG.infer_iff_minimizer_ev p cs q).1 ((hF.infer_iff_minimizer_ev p cs q).2 hq)
  · intro hq
    exact (hF.infer_iff_minimizer_ev p cs q).1 ((hG.infer_iff_minimizer_ev p cs q).2 hq)

theorem realizesEV_of_objEquivEV
    {I : Inference.InferenceMethod} {F G : ObjectiveFunctional}
    (hF : RealizesEV I F) (hEq : ObjEquivEV F G) :
    RealizesEV I G := by
  refine ⟨?_⟩
  intro n p cs q
  have hMin : IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer G p (toConstraintSet cs) q :=
    objEquivEV_isMinimizer_iff (hEq := hEq) (p := p) (cs := cs) (q := q)
  exact (hF.infer_iff_minimizer_ev p cs q).trans hMin

theorem unique_minimizer_of_realizes
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : Inference.ShoreJohnsonAxioms I) (hF : Realizes I F)
    {n : ℕ} (p : ProbDist n) (C : Inference.ConstraintSet n)
    (ha : Inference.Admissible p C) (hs : Inference.Solvable I p C) :
    ∃! q : ProbDist n, IsMinimizer F p C q := by
  obtain ⟨q, hq, hu⟩ := Inference.unique_of_solvable hSJ p C ha hs
  exact ⟨q, (hF.infer_iff_minimizer p C q).mp hq,
    fun r hr => hu r ((hF.infer_iff_minimizer p C r).mpr hr)⟩

/-! ## Objective-level consequences of SJ2/SJ3/SJ4 -/

theorem isMinimizer_permute_of_realizes
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : Inference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbDist n)
    (C : Inference.ConstraintSet n) (q : ProbDist n),
    IsMinimizer F p C q →
        IsMinimizer F (Inference.ProbDist.permute σ p)
          (Inference.ConstraintSet.permute σ C)
          (Inference.ProbDist.permute σ q) := by
  intro n σ p C q hmin
  have hInf : I.Infer p C q := (hF.infer_iff_minimizer p C q).2 hmin
  have hInf' := hSJ.perm_invariant σ p C q hInf
  exact (hF.infer_iff_minimizer _ _ _).1 hInf'

theorem eq_twoBlock_of_isMinimizer_twoBlock
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : Inference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
  ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p₁ : ProbDist n) (p₂ : ProbDist m)
    (C₁ : Inference.ConstraintSet n) (C₂ : Inference.ConstraintSet m)
    (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m)),
    Inference.Admissible p₁ C₁ → Inference.Admissible p₂ C₂ →
    IsMinimizer F p₁ C₁ q₁ →
    IsMinimizer F p₂ C₂ q₂ →
      IsMinimizer F (Inference.ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 p₁ p₂)
        (Inference.ConstraintSet.twoBlock (n := n) (m := m) w hw0 hw1 C₁ C₂) q →
      q = Inference.ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 q₁ q₂ := by
  intro n m w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ q ha₁ ha₂ hq₁ hq₂ hq
  have hInf₁ : I.Infer p₁ C₁ q₁ := (hF.infer_iff_minimizer p₁ C₁ q₁).2 hq₁
  have hInf₂ : I.Infer p₂ C₂ q₂ := (hF.infer_iff_minimizer p₂ C₂ q₂).2 hq₂
  have hInf :
      I.Infer (Inference.ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 p₁ p₂)
        (Inference.ConstraintSet.twoBlock (n := n) (m := m) w hw0 hw1 C₁ C₂) q :=
    (hF.infer_iff_minimizer _ _ _).2 hq
  exact hSJ.subset_independent_twoBlock w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ q ha₁ ha₂ hInf₁ hInf₂ hInf

theorem eq_twoBlock_of_isMinimizer_twoBlock_ev
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : Inference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
      (p₁ : ProbDist n) (p₂ : ProbDist m)
      (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m)),
      (∀ i, 0 < p₁.p i) → (∀ i, 0 < p₂.p i) →
      IsMinimizer F p₁ (toConstraintSet cs₁) q₁ →
      IsMinimizer F p₂ (toConstraintSet cs₂) q₂ →
      IsMinimizer F (Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂)) q →
      q = Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q₁ q₂ := by
  intro n m w hw0 hw1 p₁ p₂ cs₁ cs₂ q₁ q₂ q hp₁ hp₂ hq₁ hq₂ hq
  have heq :
      toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) =
        Inference.ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
          (toConstraintSet cs₁) (toConstraintSet cs₂) :=
    twoBlockConstraints_equiv_set (n := n) (m := m) w hw0 hw1 cs₁ cs₂
  have hq' :
      IsMinimizer F
        (Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (Inference.ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
          (toConstraintSet cs₁) (toConstraintSet cs₂)) q := by
    rcases hq with ⟨hq_mem, hq_le⟩
    refine ⟨?_, ?_⟩
    · simpa [heq] using hq_mem
    · intro q' hq'
      have hq'' : q' ∈ toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) := by
        simpa [heq] using hq'
      exact hq_le q' hq''
  exact eq_twoBlock_of_isMinimizer_twoBlock (hSJ := hSJ) (hF := hF) w (le_of_lt hw0) (le_of_lt hw1)
    p₁ p₂ (toConstraintSet cs₁) (toConstraintSet cs₂) q₁ q₂ q (admissible_ev p₁ cs₁ hp₁) (admissible_ev p₂ cs₂ hp₂) hq₁ hq₂ hq'

theorem eq_prod_of_isMinimizer_product
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : Inference.ShoreJohnsonAxioms I) (hF : Realizes I F) :
    ∀ {n m : ℕ} (p₁ : ProbDist n) (p₂ : ProbDist m)
      (C₁ : Inference.ConstraintSet n) (C₂ : Inference.ConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDistProd n m),
      Inference.Admissible p₁ C₁ → Inference.Admissible p₂ C₂ →
      IsMinimizer F p₁ C₁ q₁ →
      IsMinimizer F p₂ C₂ q₂ →
      IsMinimizerProd F (p₁ ⊗ p₂) (Inference.ConstraintSetProd.product C₁ C₂) q →
      q = (q₁ ⊗ q₂) := by
  intro n m p₁ p₂ C₁ C₂ q₁ q₂ q ha₁ ha₂ hq₁ hq₂ hq
  have hInf₁ : I.Infer p₁ C₁ q₁ := (hF.infer_iff_minimizer p₁ C₁ q₁).2 hq₁
  have hInf₂ : I.Infer p₂ C₂ q₂ := (hF.infer_iff_minimizer p₂ C₂ q₂).2 hq₂
  have hInf :
      I.InferProd (p₁ ⊗ p₂) (Inference.ConstraintSetProd.product C₁ C₂) q :=
    (hF.inferProd_iff_minimizer _ _ _).2 hq
  exact hSJ.system_independent p₁ p₂ C₁ C₂ q₁ q₂ q ha₁ ha₂ hInf₁ hInf₂ hInf

/-! ## Atom-sum objectives -/

/-- Build an objective functional from an atom divergence `d` by summing over indices. -/
noncomputable def ofAtom (d : ℝ → ℝ → ℝ) : ObjectiveFunctional where
  D := fun {n} q p => ∑ i : Fin n, d (q.p i) (p.p i)
  DProd := fun {n m} q p => ∑ ij : Fin n × Fin m, d (q.p ij) (p.p ij)

/-- Objective-based inference is a relation; unattained minima produce no answer. -/
def minimizerMethod (F : ObjectiveFunctional) : Inference.InferenceMethod where
  Infer p C q := IsMinimizer F p C q
  InferProd p C q := IsMinimizerProd F p C q

/-- A partial finite-reference interpretation. It does not assign the total-real
atom's finite boundary convention to unsupported probabilistic problems. -/
def positiveMinimizerMethod (F : ObjectiveFunctional) : Inference.InferenceMethod where
  Infer p C q := (∀ i, 0 < p.p i) ∧ IsMinimizer F p C q
  InferProd p C q := (∀ i, 0 < p.p i) ∧ IsMinimizerProd F p C q

theorem realizesEVPositive_positiveMinimizerMethod (F : ObjectiveFunctional) :
    RealizesEVPositive (positiveMinimizerMethod F) F :=
  ⟨fun _ _ _ hp => and_iff_right hp⟩

theorem positiveMinimizerMethod_axioms (F : ObjectiveFunctional)
    (h : Inference.ShoreJohnsonAxioms (minimizerMethod F)) :
    Inference.ShoreJohnsonAxioms (positiveMinimizerMethod F) where
  unique p C ha q r hq hr := h.unique p C ha q r hq.2 hr.2
  uniqueProd p C ha q r hq hr := h.uniqueProd p C ha q r hq.2 hr.2
  feasible hq := h.feasible hq.2
  feasibleProd hq := h.feasibleProd hq.2
  perm_invariant σ p C q hq :=
    ⟨fun i => hq.1 (σ⁻¹ i), h.perm_invariant σ p C q hq.2⟩
  system_independent p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ h₁ h₂ hQ :=
    h.system_independent p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ h₁.2 h₂.2 hQ.2
  subset_independent_twoBlock w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ h₁ h₂ hQ :=
    h.subset_independent_twoBlock w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ Q ha₁ ha₂ h₁.2 h₂.2 hQ.2

theorem realizes_minimizerMethod (F : ObjectiveFunctional) : Realizes (minimizerMethod F) F :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

/-- Strictness is supplied by a coordinate on which the two vectors differ. -/
theorem strictConvexOn_sum_coordinates {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (h : ∀ i, StrictConvexOn ℝ (Set.Ici 0) (f i)) :
    StrictConvexOn ℝ (stdSimplex ℝ ι) (fun x => ∑ i, f i (x i)) := by
  classical
  refine ⟨convex_stdSimplex ℝ ι, fun x hx y hy hxy a b ha hb hab => ?_⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  have hs := Finset.sum_lt_sum
    (fun (j : ι) (_ : j ∈ Finset.univ) => (h j).convexOn.2
      (hx.1 j) (hy.1 j) ha.le hb.le hab)
    ⟨i, Finset.mem_univ i, (h i).2 (hx.1 i) (hy.1 i) hi ha hb hab⟩
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum] using hs

/-- Compactness supplies existence. Feasibility alone does not imply attainment. -/
theorem exists_minimizer_of_compact {n : ℕ} (F : ObjectiveFunctional) (p : ProbDist n)
    (C : Inference.ConstraintSet n) (φ : (Fin n → ℝ) → ℝ)
    (hvalue : ∀ q : ProbDist n, φ q.p = F.D q p)
    (hc : IsCompact ((fun q : ProbDist n => q.p) '' C))
    (hne : C.Nonempty) (hφ : ContinuousOn φ ((fun q : ProbDist n => q.p) '' C)) :
    ∃ q, IsMinimizer F p C q := by
  obtain ⟨x, ⟨q, hq, rfl⟩, hm⟩ := hc.exists_isMinOn (hne.image _) hφ
  refine ⟨q, hq, fun r hr => ?_⟩
  have hh : φ q.p ≤ φ r.p := hm ⟨r, hr, rfl⟩
  simpa only [hvalue] using hh

theorem minimizer_unique_of_strictConvex {n : ℕ} (F : ObjectiveFunctional) (p : ProbDist n)
    (C : Inference.ConstraintSet n) (φ : (Fin n → ℝ) → ℝ)
    (hvalue : ∀ q : ProbDist n, φ q.p = F.D q p)
    (hc : Convex ℝ ((fun q : ProbDist n => q.p) '' C))
    (hs : StrictConvexOn ℝ (stdSimplex ℝ (Fin n)) φ)
    (q r : ProbDist n) (hq : IsMinimizer F p C q) (hr : IsMinimizer F p C r) : q = r := by
  have hsub : (fun q : ProbDist n => q.p) '' C ⊆ stdSimplex ℝ (Fin n) := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x.nonneg, x.sum_one⟩
  have hm (x : ProbDist n) (hx : IsMinimizer F p C x) :
      IsMinOn φ ((fun q : ProbDist n => q.p) '' C) x.p := by
    rintro y ⟨z, hz, rfl⟩
    change φ x.p ≤ φ z.p
    simpa only [hvalue] using hx.2 z hz
  have he := (hs.subset hsub hc).eq_of_isMinOn (hm q hq) (hm r hr)
    ⟨q, hq.1, rfl⟩ ⟨r, hr.1, rfl⟩
  exact ProbDist.ext q r (fun i => congrFun he i)

/-- A strictly increasing value transformation preserves the minimizer observation. -/
noncomputable def transform (F : ObjectiveFunctional) (f : ℝ → ℝ) : ObjectiveFunctional where
  D q p := f (F.D q p)
  DProd q p := f (F.DProd q p)

theorem isMinimizer_transform_iff (F : ObjectiveFunctional) (f : ℝ → ℝ) (hf : StrictMono f)
    {n : ℕ} (p : ProbDist n) (C : Inference.ConstraintSet n) (q : ProbDist n) :
    IsMinimizer (transform F f) p C q ↔ IsMinimizer F p C q := by
  simp only [IsMinimizer, transform, hf.le_iff_le]

theorem objEquiv_transform (F : ObjectiveFunctional) (f : ℝ → ℝ) (hf : StrictMono f) :
    ObjEquiv F (transform F f) := by
  intro n p C
  ext q
  exact (isMinimizer_transform_iff F f hf p C q).symm

/-! ## Objective equivalences -/

theorem objEquiv_of_pointwise_eq
    {F : ObjectiveFunctional} (d : ℝ → ℝ → ℝ)
    (hD : ∀ {n : ℕ} (q p : ProbDist n),
      F.D q p = ∑ i : Fin n, d (q.p i) (p.p i)) :
    ObjEquiv F (ofAtom d) := by
  intro n p C
  ext q
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    simpa [ofAtom, hD] using hle
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    simpa [ofAtom, hD] using hle

theorem isMinimizer_const_mul_ofAtom_iff {n : ℕ} (c : ℝ) (hc : 0 < c)
    (d : ℝ → ℝ → ℝ)
    (p : ProbDist n) (C : Inference.ConstraintSet n) (q : ProbDist n) :
    IsMinimizer (ofAtom d) p C q ↔ IsMinimizer (ofAtom (fun w u => c * d w u)) p C q := by
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    -- Scale both sides by `c` (positive) and pull `c` out of the sums.
    have hle' : c * (∑ i : Fin n, d (q.p i) (p.p i)) ≤ c * (∑ i : Fin n, d (q'.p i) (p.p i)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hc)
    -- Rewrite each objective value as `c * sum`.
    simpa [ofAtom, Finset.mul_sum, mul_assoc] using hle'
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    -- Divide by `c` by scaling with `c⁻¹` (still positive).
    have hc' : 0 < c⁻¹ := inv_pos.2 hc
    have hle' :
        c⁻¹ * (∑ i : Fin n, (c * d (q.p i) (p.p i))) ≤
          c⁻¹ * (∑ i : Fin n, (c * d (q'.p i) (p.p i))) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hc')
    -- Simplify `c⁻¹ * c = 1`.
    have : (∑ i : Fin n, d (q.p i) (p.p i)) ≤ ∑ i : Fin n, d (q'.p i) (p.p i) := by
      simpa [Finset.mul_sum, inv_mul_cancel_left₀ hc.ne', mul_assoc] using hle'
    simpa [ofAtom] using this

theorem objEquiv_const_mul_ofAtom (c : ℝ) (hc : 0 < c) (d : ℝ → ℝ → ℝ) :
    ObjEquiv (ofAtom d) (ofAtom (fun w u => c * d w u)) := by
  intro n p C
  ext q
  exact isMinimizer_const_mul_ofAtom_iff (n := n) c hc d p C q

/-- Reindexing a disjoint-union presentation retains both authored blocks. -/
theorem sum_atom_twoBlock (d : ℝ → ℝ → ℝ) {n m : ℕ}
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p₁ q₁ : ProbDist n) (p₂ q₂ : ProbDist m) :
    (ofAtom d).D (Inference.ProbDist.twoBlock w hw0 hw1 q₁ q₂)
      (Inference.ProbDist.twoBlock w hw0 hw1 p₁ p₂) =
      (∑ i, d (w*q₁.p i) (w*p₁.p i)) +
      ∑ j, d ((1-w)*q₂.p j) ((1-w)*p₂.p j) := by
  let e := (finSumFinEquiv (m := n) (n := m)).symm
  let f : Fin n ⊕ Fin m → ℝ := fun s => match s with
    | .inl i => d (w*q₁.p i) (w*p₁.p i)
    | .inr j => d ((1-w)*q₂.p j) ((1-w)*p₂.p j)
  change (∑ i : Fin (n+m), _) = _
  calc
    _ = ∑ i : Fin (n+m), f (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      cases hh : e i <;> simp_all [f, e, Inference.ProbDist.twoBlock]
    _ = _ := by rw [Equiv.sum_comp e f, Fintype.sum_sum_type]

/-- A fixed-mass block formula and component uniqueness imply subset independence.
At zero block mass the hidden component need not be identified. -/
theorem subset_independent_of_block_formula (F : ObjectiveFunctional)
    (hu : ∀ {n : ℕ} (p : ProbDist n) (C : Inference.ConstraintSet n),
      Inference.Admissible p C → ∀ q r,
        IsMinimizer F p C q → IsMinimizer F p C r → q = r)
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p₁ : ProbDist n) (p₂ : ProbDist m)
    (C₁ : Inference.ConstraintSet n) (C₂ : Inference.ConstraintSet m)
    (q₁ : ProbDist n) (q₂ : ProbDist m) (Q : ProbDist (n+m))
    (ha₁ : Inference.Admissible p₁ C₁) (ha₂ : Inference.Admissible p₂ C₂)
    (hq₁ : IsMinimizer F p₁ C₁ q₁) (hq₂ : IsMinimizer F p₂ C₂ q₂)
    (hQ : IsMinimizer F (Inference.ProbDist.twoBlock w hw0 hw1 p₁ p₂)
      (Inference.ConstraintSet.twoBlock w hw0 hw1 C₁ C₂) Q)
    (k : ℝ) (hblock : ∀ r₁ ∈ C₁, ∀ r₂ ∈ C₂,
      F.D (Inference.ProbDist.twoBlock w hw0 hw1 r₁ r₂)
        (Inference.ProbDist.twoBlock w hw0 hw1 p₁ p₂) = w*F.D r₁ p₁ + (1-w)*F.D r₂ p₂ + k) :
    Q = Inference.ProbDist.twoBlock w hw0 hw1 q₁ q₂ := by
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hQ.1
  have hb := hQ.2 (Inference.ProbDist.twoBlock w hw0 hw1 q₁ q₂)
    ⟨q₁, hq₁.1, q₂, hq₂.1, rfl⟩
  rw [hblock r₁ hr₁ r₂ hr₂, hblock q₁ hq₁.1 q₂ hq₂.1] at hb
  have h₁ := mul_nonneg hw0 (sub_nonneg.mpr (hq₁.2 r₁ hr₁))
  have h₂ := mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr (hq₂.2 r₂ hr₂))
  have hz₁ : w*(F.D r₁ p₁ - F.D q₁ p₁) = 0 := by nlinarith
  have hz₂ : (1-w)*(F.D r₂ p₂ - F.D q₂ p₂) = 0 := by nlinarith
  have he₁ (hw : w ≠ 0) : r₁ = q₁ := by
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hz₁).resolve_left hw)
    exact hu p₁ C₁ ha₁ r₁ q₁ ⟨hr₁, fun r hr => by rw [he]; exact hq₁.2 r hr⟩ hq₁
  have he₂ (hw : 1-w ≠ 0) : r₂ = q₂ := by
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hz₂).resolve_left hw)
    exact hu p₂ C₂ ha₂ r₂ q₂ ⟨hr₂, fun r hr => by rw [he]; exact hq₂.2 r hr⟩ hq₂
  apply ProbDist.ext
  intro i
  cases hh : (finSumFinEquiv (m := n) (n := m)).symm i with
  | inl j =>
    by_cases hw : w = 0
    · simp [Inference.ProbDist.twoBlock, hh, hw]
    · simp [Inference.ProbDist.twoBlock, hh, he₁ hw]
  | inr j =>
    by_cases hw : 1-w = 0
    · simp [Inference.ProbDist.twoBlock, hh, hw]
    · simp [Inference.ProbDist.twoBlock, hh, he₂ hw]

end KnuthSkilling.ShoreJohnson.Objective
