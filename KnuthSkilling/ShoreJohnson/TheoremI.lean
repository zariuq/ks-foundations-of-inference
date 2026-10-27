import KnuthSkilling.ShoreJohnson.Inference
import KnuthSkilling.ShoreJohnson.Objective
import KnuthSkilling.ShoreJohnson.Constraints
import KnuthSkilling.ShoreJohnson.AppendixFDeriv
import KnuthSkilling.ShoreJohnson.AppendixMinimizer
import KnuthSkilling.ShoreJohnson.AppendixTheoremI
import KnuthSkilling.ShoreJohnson.GradientSeparability
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

/-!
# Affine-constrained stationarity and separable objectives

The calculus in this module concerns the supplied objective and all feasible affine
variations. Pairwise shifts alone need not span the constraint kernel. Positivity
is imposed on the particular prior and candidate, never on every distribution.
The KL application permits zero coordinates in competitors.

These are conditional variational results. They do not constitute a derivation of
sum form or ratio invariance from the four discrete inference laws.
-/
namespace KnuthSkilling.ShoreJohnson.TheoremI
open Classical Finset
open scoped BigOperators Topology
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Inference
open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.Appendix
open KnuthSkilling.ShoreJohnson.AppendixMinimizer
open KnuthSkilling.ShoreJohnson.AppendixTheoremI

theorem lemma_I_twoBlock
    (I : InferenceMethod) (hSJ : ShoreJohnsonAxioms I)
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p₁ : ProbDist n) (p₂ : ProbDist m)
    (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
    (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m))
    (ha₁ : Admissible p₁ C₁) (ha₂ : Admissible p₂ C₂)
    (hInfer₁ : I.Infer p₁ C₁ q₁)
    (hInfer₂ : I.Infer p₂ C₂ q₂)
    (hInfer : I.Infer (ProbDist.twoBlock w hw0 hw1 p₁ p₂)
      (ConstraintSet.twoBlock w hw0 hw1 C₁ C₂) q) :
    q = ProbDist.twoBlock w hw0 hw1 q₁ q₂ :=
  hSJ.subset_independent_twoBlock w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ q ha₁ ha₂ hInfer₁ hInfer₂ hInfer

theorem lemma_II_permutation_symmetry
    (I : InferenceMethod) (F : ObjectiveFunctional)
    (hSJ : ShoreJohnsonAxioms I)
    (hRealize : RealizesEV I F)
    {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (σ : Equiv.Perm (Fin n)) (q : ProbDist n) :
    IsMinimizer F p (toConstraintSet cs) q ↔
    IsMinimizer F (ProbDist.permute σ p) (toConstraintSet (EVConstraintSet.permute σ cs))
      (ProbDist.permute σ q) := by

  have hcompat : ConstraintSet.permute σ (toConstraintSet cs) =
      toConstraintSet (EVConstraintSet.permute σ cs) :=
    toConstraintSet_permute σ cs

  have hLeft := hRealize.infer_iff_minimizer_ev (p := p) (cs := cs) (q := q)

  have hRight := hRealize.infer_iff_minimizer_ev
    (p := ProbDist.permute σ p) (cs := EVConstraintSet.permute σ cs) (q := ProbDist.permute σ q)
  constructor
  ·
    intro hMin

    have hInfer : I.Infer p (toConstraintSet cs) q := hLeft.mpr hMin

    have hPermInfer := hSJ.perm_invariant (σ := σ) (p := p) (C := toConstraintSet cs) (q := q) hInfer

    rw [hcompat] at hPermInfer

    exact hRight.mp hPermInfer
  ·
    intro hMinPerm

    have hInferPerm : I.Infer (ProbDist.permute σ p)
        (toConstraintSet (EVConstraintSet.permute σ cs)) (ProbDist.permute σ q) :=
      hRight.mpr hMinPerm

    rw [← hcompat] at hInferPerm
    have hInferPermBack := hSJ.perm_invariant (σ := σ⁻¹)
      (p := ProbDist.permute σ p) (C := ConstraintSet.permute σ (toConstraintSet cs))
      (q := ProbDist.permute σ q) hInferPerm

    have hp_back : ProbDist.permute σ⁻¹ (ProbDist.permute σ p) = p := by
      ext i; simp [ProbDist.permute]
    have hq_back : ProbDist.permute σ⁻¹ (ProbDist.permute σ q) = q := by
      ext i; simp [ProbDist.permute]
    have hC_back : ConstraintSet.permute σ⁻¹ (ConstraintSet.permute σ (toConstraintSet cs)) =
        toConstraintSet cs := by
      ext Q
      simp [ConstraintSet.permute]
    rw [hp_back, hq_back, hC_back] at hInferPermBack
    exact hLeft.mp hInferPermBack

def IsAntiderivative (d g : ℝ → ℝ → ℝ) : Prop :=
  ∀ q p : ℝ, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (g q p) q

noncomputable def gradAt_general {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun v => ∑ i : Fin n, v i * (g (q.p i) (p.p i) + 1)
    map_add' := by
      intro v w
      classical
      simp [Finset.sum_add_distrib, add_mul, mul_add, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro c v
      classical
      simp [Finset.mul_sum, mul_assoc] }

lemma gradAt_general_apply_single {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (i : Fin n) :
    gradAt_general g p q (Pi.single i (1 : ℝ) : Fin n → ℝ) = g (q.p i) (p.p i) + 1 := by
  classical
  have :
      (∑ j : Fin n, ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) * (g (q.p j) (p.p j) + 1)) =
        (Pi.single i (1 : ℝ) : Fin n → ℝ) i * (g (q.p i) (p.p i) + 1) := by
    refine Fintype.sum_eq_single i ?_
    intro j hji
    simp [Pi.single, hji]
  simpa [gradAt_general, Pi.single, this] using this

noncomputable def constraintForm_general {n : ℕ} (cs : EVConstraintSet n) :
    Option (Fin cs.length) → (Fin n → ℝ) →ₗ[ℝ] ℝ
  | none =>
      { toFun := fun v => ∑ i : Fin n, v i
        map_add' := by
          intro v w
          classical
          simp [Finset.sum_add_distrib]
        map_smul' := by
          intro c v
          classical
          simp [Finset.mul_sum] }
  | some k =>
      { toFun := fun v => ∑ i : Fin n, v i * (cs.get k).coeff i
        map_add' := by
          intro v w
          classical
          simp [Finset.sum_add_distrib, add_mul]
        map_smul' := by
          intro c v
          classical
          simp [Finset.mul_sum, mul_assoc] }

lemma constraintForm_general_apply_single_none {n : ℕ} (cs : EVConstraintSet n) (i : Fin n) :
    constraintForm_general cs none (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
  classical
  simp [constraintForm_general, Pi.single]
  convert Finset.sum_eq_single i ?_ ?_
  · simp
  · intro j _ hj
    simp [hj]
  · simp

lemma constraintForm_general_apply_single_some {n : ℕ} (cs : EVConstraintSet n)
    (k : Fin cs.length) (i : Fin n) :
    constraintForm_general cs (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ) = (cs.get k).coeff i := by
  classical
  simp [constraintForm_general, Pi.single]
  convert Finset.sum_eq_single i ?_ ?_
  · simp
  · intro j _ hj
    simp [hj]
  · simp

lemma constraintForm_general_none_apply {n : ℕ} (cs : EVConstraintSet n) (v : Fin n → ℝ) :
    constraintForm_general cs none v = ∑ i : Fin n, v i := by
  simp [constraintForm_general]

lemma constraintForm_general_some_apply {n : ℕ} (cs : EVConstraintSet n)
    (k : Fin cs.length) (v : Fin n → ℝ) :
    constraintForm_general cs (some k) v = ∑ i : Fin n, v i * (cs.get k).coeff i := by
  simp [constraintForm_general]

lemma mem_span_of_iInf_ker_le_ker {ι α : Type*} [Fintype ι] [AddCommGroup α] [Module ℝ α]
    (L : ι → α →ₗ[ℝ] ℝ) (K : α →ₗ[ℝ] ℝ)
    (h : (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker K) :
    K ∈ Submodule.span ℝ (Set.range L) :=
  _root_.mem_span_of_iInf_ker_le_ker h

/-- Full affine-direction Fermat argument. Derivatives are supplied for the actual
ambient extension, rather than inferred from a restricted collection of pairwise shifts. -/
theorem stationaryEV_of_isMinimizer_directional {n : ℕ}
    (F : ObjectiveFunctional) (g : ℝ → ℝ → ℝ) (p q : ProbDist n)
    (cs : EVConstraintSet n) (φ : (Fin n → ℝ) → ℝ)
    (hvalue : ∀ r : ProbDist n, φ r.p = F.D r p)
    (hderiv : ∀ v : Fin n → ℝ, (∑ i, v i) = 0 →
      HasDerivAt (fun t => φ (fun i => q.p i + t * v i))
        (∑ i, v i * g (q.p i) (p.p i)) 0)
    (hq : q ∈ toConstraintSet cs) (hqPos : ∀ i, 0 < q.p i)
    (hmin : IsMinimizer F p (toConstraintSet cs) q) : StationaryEV g p q cs := by
  classical

  let K : (Fin n → ℝ) →ₗ[ℝ] ℝ := gradAt_general g p q
  let L : Option (Fin cs.length) → (Fin n → ℝ) →ₗ[ℝ] ℝ := constraintForm_general (n := n) cs

  have hKer : (⨅ o, LinearMap.ker (L o)) ≤ LinearMap.ker K := by
    intro v hv

    let qLine : ℝ → (Fin n → ℝ) := fun t => fun i => q.p i + t * v i
    let φLine : ℝ → ℝ := fun t => φ (qLine t)
    have hsumv : (∑ i : Fin n, v i) = 0 := by
      have hv0 : v ∈ LinearMap.ker (L none) := (Submodule.mem_iInf _).1 hv none
      have : L none v = 0 := hv0
      simpa [L, constraintForm_general_none_apply] using this
    have hvCoeff : ∀ k : Fin cs.length, (∑ i : Fin n, v i * (cs.get k).coeff i) = 0 := by
      intro k
      have hvk : v ∈ LinearMap.ker (L (some k)) := (Submodule.mem_iInf _).1 hv (some k)
      have : L (some k) v = 0 := hvk
      simpa [L, constraintForm_general_some_apply] using this

    have hpos : ∀ᶠ t in nhds (0 : ℝ), ∀ i : Fin n, 0 < qLine t i := by

      have hpos_i : ∀ i : Fin n, ∀ᶠ t in nhds (0 : ℝ), 0 < qLine t i := by
        intro i
        have hcont : Continuous (fun t : ℝ => qLine t i) := by
          show Continuous (fun t : ℝ => q.p i + t * v i)
          fun_prop
        have h0 : 0 < qLine 0 i := by simpa [qLine] using hqPos i
        have : ∀ᶠ t in nhds (0 : ℝ), qLine t i ∈ Set.Ioi (0 : ℝ) :=
          hcont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h0)
        simpa [Set.mem_Ioi] using this
      simpa using (Filter.eventually_all.2 hpos_i)
    have hloc : IsLocalMin φLine 0 := by
      refine (hpos.mono ?_)
      intro t htpos
      have ht_nonneg : ∀ i, 0 ≤ qLine t i := fun i => le_of_lt (htpos i)
      have ht_sum : (∑ i : Fin n, qLine t i) = 1 := by
        calc
          (∑ i : Fin n, qLine t i) = (∑ i : Fin n, q.p i) + t * (∑ i : Fin n, v i) := by
            simp [qLine, Finset.sum_add_distrib, Finset.mul_sum]
          _ = 1 + t * (∑ i : Fin n, v i) := by simp [q.sum_one]
          _ = 1 := by simp [hsumv]
      let qT : ProbDist n :=
        { p := fun i => qLine t i
          nonneg := ht_nonneg
          sum_one := ht_sum }
      have hqT_mem : qT ∈ toConstraintSet cs := by
        have hq_sat : satisfiesSet cs q := (mem_toConstraintSet cs q).1 hq
        have hsat : satisfiesSet cs qT := by
          intro c hc
          obtain ⟨k, rfl⟩ := List.get_of_mem hc
          have hk : (∑ i : Fin n, v i * (cs.get k).coeff i) = 0 := hvCoeff k
          have hqk : satisfies (cs.get k) q := hq_sat (cs.get k) (List.get_mem cs k)
          dsimp [satisfies] at hqk ⊢
          calc
            (∑ i : Fin n, qT.p i * (cs.get k).coeff i)
                = (∑ i : Fin n, q.p i * (cs.get k).coeff i) +
                    t * (∑ i : Fin n, v i * (cs.get k).coeff i) := by
                      simp [qT, qLine, Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]
            _ = (cs.get k).rhs + t * (∑ i : Fin n, v i * (cs.get k).coeff i) := by
              simp [hqk]
            _ = (cs.get k).rhs + t * 0 := by
              rw [hk]
            _ = (cs.get k).rhs := by simp
        exact (mem_toConstraintSet cs qT).2 hsat
      have hle := hmin.2 qT hqT_mem
      change φ (qLine 0) ≤ φ qT.p
      have he0 : qLine 0 = q.p := by ext i; simp [qLine]
      rw [he0, hvalue q, hvalue qT]
      exact hle
    have hderiv : HasDerivAt φLine (∑ i : Fin n, v i * g (q.p i) (p.p i)) 0 :=
      hderiv v hsumv
    have hderiv0 : (∑ i : Fin n, v i * g (q.p i) (p.p i)) = 0 := by
      exact hloc.hasDerivAt_eq_zero hderiv

    have : K v = 0 := by
      simp only [K, gradAt_general, LinearMap.coe_mk, AddHom.coe_mk]

      have h1 : (∑ i : Fin n, v i * (g (q.p i) (p.p i) + 1)) =
                (∑ i : Fin n, (v i * g (q.p i) (p.p i) + v i)) := by
        congr 1; ext i; ring
      have h2 : (∑ i : Fin n, (v i * g (q.p i) (p.p i) + v i)) =
                (∑ i : Fin n, v i * g (q.p i) (p.p i)) + (∑ i : Fin n, v i) := by
        simp only [Finset.sum_add_distrib]
      rw [h1, h2, hderiv0, hsumv]
      norm_num
    exact this

  have hKspan : K ∈ Submodule.span ℝ (Set.range L) :=
    mem_span_of_iInf_ker_le_ker (L := L) (K := K) hKer

  rcases (Submodule.mem_span_range_iff_exists_fun ℝ).1 hKspan with ⟨c, hc⟩

  refine ⟨c none - 1, fun k => c (some k), ?_⟩
  intro i

  have hci :=
    congrArg (fun (K' : (Fin n → ℝ) →ₗ[ℝ] ℝ) => K' (Pi.single i (1 : ℝ) : Fin n → ℝ)) hc

  have hK : K (Pi.single i (1 : ℝ) : Fin n → ℝ) = g (q.p i) (p.p i) + 1 := by
    simpa using gradAt_general_apply_single g p q i
  have hL :
      (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) =
        c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := by
    classical
    have hsum :
        (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) =
          c none * (L none (Pi.single i (1 : ℝ) : Fin n → ℝ)) +
            ∑ k : Fin cs.length, c (some k) * (L (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      simp [Fintype.sum_option, Finset.sum_apply, LinearMap.smul_apply]
    have hnone : L none (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
      simpa [L] using constraintForm_general_apply_single_none (cs := cs) i
    have hsome : ∀ k : Fin cs.length, L (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ) = (cs.get k).coeff i := by
      intro k
      simpa [L] using constraintForm_general_apply_single_some (cs := cs) k i
    simp [hnone, hsome]
  have : g (q.p i) (p.p i) + 1 = c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := by
    calc
      g (q.p i) (p.p i) + 1 = K (Pi.single i (1 : ℝ) : Fin n → ℝ) := by simpa using hK.symm
      _ = (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        simpa using hci.symm
      _ = c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := hL
  linarith

theorem hasDerivAt_atom_line {n : ℕ} (d g : ℝ → ℝ → ℝ)
    (hd : IsAntiderivative d g) (p q : ProbDist n)
    (hp : ∀ i, 0 < p.p i) (hq : ∀ i, 0 < q.p i) (v : Fin n → ℝ) :
    HasDerivAt (fun t => ∑ i, d (q.p i + t * v i) (p.p i))
      (∑ i, v i * g (q.p i) (p.p i)) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have hi : HasDerivAt (fun t : ℝ => q.p i + t * v i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (q.p i)
  have ho := hd (q.p i) (p.p i) (hq i) (hp i)
  have ho' : HasDerivAt (fun x => d x (p.p i)) (g (q.p i) (p.p i))
      (q.p i + (0 : ℝ) * v i) := by simpa using ho
  convert ho'.comp 0 hi using 1 <;> first | rfl | ring

theorem stationaryEV_of_isMinimizer_ofAtom_general {n : ℕ}
    (d g : ℝ → ℝ → ℝ) (hd : IsAntiderivative d g)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i)
    (hm : IsMinimizer (ofAtom d) p (toConstraintSet cs) q) : StationaryEV g p q cs :=
  stationaryEV_of_isMinimizer_directional (ofAtom d) g p q cs
    (fun x => ∑ i, d (x i) (p.p i)) (fun _ => rfl)
    (fun v _ => hasDerivAt_atom_line d g hd p q hp hpos v) hq hpos hm

/-- The supporting-line inequality, including endpoints of the convex domain. -/
theorem convex_lower_bound {f : ℝ → ℝ} {S : Set ℝ} {x y a : ℝ}
    (hc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f a x) :
    f x + a * (y-x) ≤ f y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hs := mul_le_mul_of_nonneg_right
      (hc.le_slope_of_hasDerivAt hx hy h hd) (le_of_lt (sub_pos.mpr h))
    rw [slope_def_field, div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')] at hs
    linarith
  · simp
  · have hs := mul_le_mul_of_nonneg_right
      (hc.slope_le_of_hasDerivAt hy hx h hd) (le_of_lt (sub_pos.mpr h))
    rw [slope_def_field, div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')] at hs
    linarith

/-- Convexity on the closed nonnegative domain permits zero-valued competitors. -/
def IsConvexInFirstArg (d : ℝ → ℝ → ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → ConvexOn ℝ (Set.Ici 0) (fun q => d q p)

theorem isMinimizer_ofAtom_of_stationaryEV_convex {n : ℕ}
    (d g : ℝ → ℝ → ℝ) (hc : IsConvexInFirstArg d) (hd : IsAntiderivative d g)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i)
    (hs : StationaryEV g p q cs) : IsMinimizer (ofAtom d) p (toConstraintSet cs) q := by
  refine ⟨hq, fun q' hq' => ?_⟩
  have hb := Finset.sum_le_sum fun (i : Fin n) (_ : i ∈ Finset.univ) =>
    convex_lower_bound (hc (p.p i) (hp i)) (le_of_lt (hpos i)) (q'.nonneg i)
      (hd (q.p i) (p.p i) (hpos i) (hp i))
  have hz := stationaryEV_feasible_difference hs hq q' hq'
  simp_rw [mul_comm (g _ _) _, Finset.sum_add_distrib] at hb
  rw [hz, add_zero] at hb
  exact hb

theorem stationaryEV_iff_minimizer_ofAtom (d g : ℝ → ℝ → ℝ)
    (hd : IsAntiderivative d g) (hc : IsConvexInFirstArg d)
    {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i) :
    StationaryEV g p q cs ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q :=
  ⟨isMinimizer_ofAtom_of_stationaryEV_convex d g hc hd p hp cs q hq hpos,
    stationaryEV_of_isMinimizer_ofAtom_general d g hd p hp cs q hq hpos⟩

/-- Convexity and the derivative along the actual feasible chord imply global
optimality. Competitors may lie on the boundary of the simplex. -/
theorem isMinimizer_of_convex_directional {n : ℕ} (F : ObjectiveFunctional)
    (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (cs : EVConstraintSet n)
    (φ : (Fin n → ℝ) → ℝ) (hvalue : ∀ r : ProbDist n, φ r.p = F.D r p)
    (hc : ConvexOn ℝ (stdSimplex ℝ (Fin n)) φ) (s : ℝ)
    (hd : ∀ v : Fin n → ℝ, (∑ i, v i) = 0 →
      HasDerivAt (fun t => φ (fun i => q.p i + t*v i))
        (s * ∑ i, v i * g (q.p i) (p.p i)) 0)
    (hq : q ∈ toConstraintSet cs) (hs : StationaryEV g p q cs) :
    IsMinimizer F p (toConstraintSet cs) q := by
  refine ⟨hq, fun q' hq' => ?_⟩
  let line : ℝ →ᵃ[ℝ] (Fin n → ℝ) := AffineMap.lineMap q.p q'.p
  have hline : Set.Icc (0 : ℝ) 1 ⊆ line ⁻¹' stdSimplex ℝ (Fin n) := by
    intro t ht
    change line t ∈ stdSimplex ℝ (Fin n)
    rw [AffineMap.lineMap_apply_module]
    exact (convex_stdSimplex ℝ (Fin n)) ⟨q.nonneg, q.sum_one⟩
      ⟨q'.nonneg, q'.sum_one⟩ (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hc' := (hc.comp_affineMap line).subset hline (convex_Icc (0 : ℝ) 1)
  have hz := stationaryEV_feasible_difference hs hq q' hq'
  have hd' := hd (fun i => q'.p i - q.p i)
    (by simp [Finset.sum_sub_distrib, q'.sum_one, q.sum_one])
  rw [hz, mul_zero] at hd'
  have hdline : HasDerivAt (φ ∘ line) 0 0 := by
    have he : (φ ∘ line) = (fun t => φ (fun i => q.p i + t*(q'.p i - q.p i))) := by
      funext t
      apply congrArg φ
      funext i
      simp [line, AffineMap.lineMap_apply_module', add_comm]
    rw [he]
    exact hd'
  have hb := convex_lower_bound hc' (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) hdline
  simpa [Function.comp_def, line, hvalue] using hb

/-- The full first-order characterization comes from directional calculus and
convexity, not an assumed equivalence between stationarity and minimization. -/
theorem stationaryEV_iff_minimizer_directional {n : ℕ} (F : ObjectiveFunctional)
    (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (cs : EVConstraintSet n)
    (φ : (Fin n → ℝ) → ℝ) (hvalue : ∀ r : ProbDist n, φ r.p = F.D r p)
    (hc : ConvexOn ℝ (stdSimplex ℝ (Fin n)) φ) (s : ℝ) (hs : s ≠ 0)
    (hd : ∀ v : Fin n → ℝ, (∑ i, v i) = 0 →
      HasDerivAt (fun t => φ (fun i => q.p i + t*v i))
        (s * ∑ i, v i * g (q.p i) (p.p i)) 0)
    (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i) :
    StationaryEV g p q cs ↔ IsMinimizer F p (toConstraintSet cs) q := by
  refine ⟨isMinimizer_of_convex_directional F g p q cs φ hvalue hc s hd hq, fun hm => ?_⟩
  apply (stationaryEV_const_mul_iff g s hs p q cs).mp
  apply stationaryEV_of_isMinimizer_directional F (fun x y => s*g x y) p q cs φ hvalue
    (fun v hv => ?_) hq hpos hm
  convert hd v hv using 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A genuine Fréchet derivative makes the pairwise gradient certificate linear
on every normalization-preserving direction. This is the missing spanning premise
when one tries to use only the constraint-preserving pairwise shifts. -/
theorem hasDerivAt_line_of_gradient {n : ℕ} (F : ObjectiveFunctional)
    (gr : GradientSeparability.GradientRepresentation F) (p q : ProbDist n)
    (hp : ∀ i, 0 < p.p i) (hq : ∀ i, 0 < q.p i)
    (φ : (Fin n → ℝ) → ℝ) (hvalue : ∀ r : ProbDist n, φ r.p = F.D r p)
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (hF : HasFDerivAt φ L q.p)
    (v : Fin n → ℝ) (hv : ∑ i, v i = 0) :
    HasDerivAt (fun t => φ (fun i => q.p i + t*v i))
      (gr.scale p q * ∑ i, v i * gr.g (q.p i) (p.p i)) 0 := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    simpa using p.sum_one
  let j : Fin n := ⟨0, hn⟩
  have hcoord (i : Fin n) :
      L (Pi.single i 1) - L (Pi.single j 1) =
        gr.scale p q * (gr.g (q.p i) (p.p i) - gr.g (q.p j) (p.p j)) := by
    by_cases hij : i = j
    · subst i; simp
    have hF' : HasFDerivAt φ L (shift2 q.p i j (q.p i)) := by
      rw [shift2_self q.p i j hij]
      exact hF
    have hcurve := hasDerivAt_comp_shift2_of_hasFDerivAt φ q.p i j (q.p i) hij L hF'
    have he : (fun t => φ (shift2 q.p i j t)) =ᶠ[𝓝 (q.p i)]
        (fun t => F.D (shift2ProbClamp q i j hij t) p) := by
      filter_upwards [Ioo_mem_nhds (hq i) (lt_add_of_pos_right _ (hq j))] with t ht
      rw [← hvalue (shift2ProbClamp q i j hij t)]
      apply congrArg φ
      funext k
      rw [shift2ProbClamp_apply, shift2Clamp_eq_of_mem q i j t ht.1.le ht.2.le]
    simpa only [map_sub] using
      (hcurve.congr_of_eventuallyEq he.symm).unique (gr.shift2_deriv p q i j hij hp hq)
  have hc (i : Fin n) : L (Pi.single i 1) = gr.scale p q * gr.g (q.p i) (p.p i) +
      (L (Pi.single j 1) - gr.scale p q * gr.g (q.p j) (p.p j)) := by
    have := hcoord i
    linarith
  have hLv : L v = gr.scale p q * ∑ i, v i * gr.g (q.p i) (p.p i) := by
    have he : v = ∑ i, v i • (Pi.single i (1 : ℝ)) := by
      ext k
      simp [Pi.single_apply]
    calc
      L v = ∑ i, v i * L (Pi.single i 1) := by
        conv_lhs => rw [he]
        simp
      _ = ∑ i, v i * (gr.scale p q * gr.g (q.p i) (p.p i) +
          (L (Pi.single j 1) - gr.scale p q * gr.g (q.p j) (p.p j))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hc i]
      _ = gr.scale p q * ∑ i, v i * gr.g (q.p i) (p.p i) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hv, zero_mul, add_zero, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hline : HasDerivAt (fun t : ℝ => q.p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q.p
  have hF' : HasFDerivAt φ L (q.p + (0 : ℝ) • v) := by simpa using hF
  have hh := hF'.comp_hasDerivAt 0 hline
  rw [hLv] at hh
  convert hh using 1 <;> rfl

/-- The repaired sum-form comparison is per positive candidate and positive prior.
All feasible competitors, including boundary points, participate in minimization. -/
theorem sumForm_positive_minimizers_of_convex_gradient {n : ℕ} (F : ObjectiveFunctional)
    (gr : GradientSeparability.GradientRepresentation F) (d : ℝ → ℝ → ℝ)
    (hd : IsAntiderivative d gr.g) (hcd : IsConvexInFirstArg d)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i) (cs : EVConstraintSet n)
    (φ : (Fin n → ℝ) → ℝ) (hvalue : ∀ r : ProbDist n, φ r.p = F.D r p)
    (hc : ConvexOn ℝ (stdSimplex ℝ (Fin n)) φ) (q : ProbDist n)
    (hq : q ∈ toConstraintSet cs) (hpos : ∀ i, 0 < q.p i)
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (hF : HasFDerivAt φ L q.p) :
    IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q :=
  (stationaryEV_iff_minimizer_directional F gr.g p q cs φ hvalue hc (gr.scale p q)
    (gr.scale_ne_zero p q) (hasDerivAt_line_of_gradient F gr p q hp hpos φ hvalue L hF)
    hq hpos).symm.trans (stationaryEV_iff_minimizer_ofAtom d gr.g hd hcd p hp cs q hq hpos)

end KnuthSkilling.ShoreJohnson.TheoremI
