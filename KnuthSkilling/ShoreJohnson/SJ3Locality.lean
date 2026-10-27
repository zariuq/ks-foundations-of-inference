import KnuthSkilling.ShoreJohnson.GradientSeparability
import KnuthSkilling.ShoreJohnson.TwoBlock

/-!
# Analytic transport across two-block presentations

The inference subset law concerns selected posteriors; a derivative transport law
concerns the supplied objective. They are different assertions. This module proves
locality from explicit analytic transport and objective permutation symmetry.
Ratio invariance also implies locality directly, without an inference premise.
-/
namespace KnuthSkilling.ShoreJohnson.SJ3Locality
open Classical
open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Inference
open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.Constraints
open KnuthSkilling.ShoreJohnson.GradientSeparability
open KnuthSkilling.ShoreJohnson.AppendixMinimizer
open KnuthSkilling.ShoreJohnson.TwoBlock

theorem shift2ProbClamp_twoBlock_left_of_mem
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m)
    (i j : Fin n) (hij : i ≠ j) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ P₁.p i + P₁.p j) :
    shift2ProbClamp
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
        (by
          intro h
          exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h))
        (w * u) =
      ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
        (_root_.KnuthSkilling.ShoreJohnson.Appendix.shift2Prob
          P₁ i j hij u hu0 hu1) P₂ := by
  simpa using
    (TwoBlock.shift2ProbClamp_twoBlock_inl_of_mem
      (w := w) (hw0 := hw0) (hw1 := hw1)
      (P₁ := P₁) (P₂ := P₂) (i := i) (j := j) (hij := hij) (u := u) (hu0 := hu0) (hu1 := hu1))

theorem hasDerivAt_shift2ProbClamp_scaled_left
    {F : ObjectiveFunctional} {n : ℕ} (p q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j) (w u0 : ℝ)
    (hqi : q.p i = w * u0) {L : ℝ}
    (h : HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (q.p i)) :
    HasDerivAt (fun u => F.D (shift2ProbClamp q i j hij (w * u)) p) (w * L) u0 := by
  simpa using
    (TwoBlock.hasDerivAt_shift2ProbClamp_scaled
      (p := p) (q := q) (i := i) (j := j) (hij := hij) (w := w) (u0 := u0) (hqi := hqi)
      (L := L) h)

theorem hasDerivAt_twoBlock_left_shift2ProbClamp
    {F : ObjectiveFunctional} {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (p : ProbDist (n + m))
    (i j : Fin n) (hij : i ≠ j) (u0 : ℝ)
    (hqi :
      (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂).p
        (inlFin (n := n) (m := m) i) = w * u0)
    (hu0 : 0 < u0) (hu1 : u0 < P₁.p i + P₁.p j)
    {L : ℝ}
    (h :
      HasDerivAt
        (fun t =>
          F.D
            (shift2ProbClamp
              (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂)
              (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
              (by
                intro h'
                exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h')) t)
            p)
        L (w * u0)) :
    HasDerivAt
      (fun u =>
        F.D
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
            (shift2ProbClamp P₁ i j hij u) P₂) p)
      (w * L) u0 := by
  simpa using
    (TwoBlock.hasDerivAt_twoBlock_left_shift2ProbClamp
      (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := P₁) (P₂ := P₂) (p := p)
      (i := i) (j := j) (hij := hij) (u0 := u0) (hqi := hqi) (hu0 := hu0) (hu1 := hu1)
      (L := L) h)

def ObjectivePermuteInvariant (F : ObjectiveFunctional) : Prop :=
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p q : ProbDist n),
    F.D (ProbDist.permute σ q) (ProbDist.permute σ p) = F.D q p

def DerivPermuteInvariant (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F) : Prop :=
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j)
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k),
    Classical.choose (hDiff.deriv_exists p q i j hij hp hq) =
      Classical.choose (hDiff.deriv_exists
        (ProbDist.permute σ p) (ProbDist.permute σ q)
        (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
        (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k)))

theorem derivPermuteInvariant_of_objectivePermuteInvariant
    (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F)
    (hPerm : ObjectivePermuteInvariant F) :
    DerivPermuteInvariant F hDiff := by
  intro n σ p q i j hij hp hq

  let φ := fun t => F.D (shift2ProbClamp q i j hij t) p
  let ψ := fun t =>
    F.D (shift2ProbClamp (ProbDist.permute σ q) (σ i) (σ j) (σ.injective.ne_iff.mpr hij) t)
      (ProbDist.permute σ p)
  have hφψ : φ = ψ := by
    funext t

    have hperm :
        ProbDist.permute σ (shift2ProbClamp q i j hij t) =
          shift2ProbClamp (ProbDist.permute σ q) (σ i) (σ j)
            (σ.injective.ne_iff.mpr hij) t :=
      _root_.KnuthSkilling.ShoreJohnson.AppendixMinimizer.permute_shift2ProbClamp
        (σ := σ) (q := q) (i := i) (j := j) (hij := hij) (t := t)

    simpa [φ, ψ, hperm] using (hPerm (σ := σ) (p := p) (q := shift2ProbClamp q i j hij t)).symm

  have hDeriv₁ :
      HasDerivAt φ (Classical.choose (hDiff.deriv_exists p q i j hij hp hq)) (q.p i) :=
    Classical.choose_spec (hDiff.deriv_exists p q i j hij hp hq)
  have hDeriv₂ :
      HasDerivAt ψ
        (Classical.choose
          (hDiff.deriv_exists
            (ProbDist.permute σ p) (ProbDist.permute σ q)
            (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
            (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k))))
        ((ProbDist.permute σ q).p (σ i)) :=
    Classical.choose_spec
      (hDiff.deriv_exists
        (ProbDist.permute σ p) (ProbDist.permute σ q)
        (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
        (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k)))

  have hpoint : (ProbDist.permute σ q).p (σ i) = q.p i := by
    simp [ProbDist.permute_apply]

  have hDeriv₂' :
      HasDerivAt φ
        (Classical.choose
          (hDiff.deriv_exists
            (ProbDist.permute σ p) (ProbDist.permute σ q)
            (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
            (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k))))
        (q.p i) := by
    simpa [hφψ, hpoint] using hDeriv₂
  exact (hDeriv₁.unique hDeriv₂')

theorem twoBlock_permute_swap_eq
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m)
    (i : Fin n) (j : Fin m)
    (hij : w * P₁.p i = (1 - w) * P₂.p j) :
    ProbDist.permute (Equiv.swap (inlFin (n := n) (m := m) i) (inrFin (n := n) (m := m) j))
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂) =
      ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂ := by
  apply ProbDist.ext
  intro k
  classical
  by_cases hk_i : k = inlFin (n := n) (m := m) i
  · subst hk_i
    simp [ProbDist.permute_apply, hij, twoBlock_apply_inl, twoBlock_apply_inr]
  by_cases hk_j : k = inrFin (n := n) (m := m) j
  · subst hk_j
    simp [ProbDist.permute_apply, hij, twoBlock_apply_inl, twoBlock_apply_inr]
  have hswap :
      (Equiv.swap (inlFin (n := n) (m := m) i) (inrFin (n := n) (m := m) j)) k = k := by
    exact
      (Equiv.swap_apply_of_ne_of_ne (a := inlFin (n := n) (m := m) i)
        (b := inrFin (n := n) (m := m) j) (x := k) hk_i hk_j)
  simp [ProbDist.permute_apply, hswap]

structure DerivTwoBlockTransport (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F) : Prop where
  left :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
      (p q : ProbDist n) (p' q' : ProbDist m)
      (i j : Fin n) (hij : i ≠ j)
      (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k)
      (hpComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p k)
      (hqComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p k),
      Classical.choose
          (hDiff.deriv_exists
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
            (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
            (by
              intro h
              exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h))
            hpComb hqComb) =
        Classical.choose (hDiff.deriv_exists p q i j hij hp hq)
  right :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
      (p q : ProbDist n) (p' q' : ProbDist m)
      (i' j' : Fin m) (hi'j' : i' ≠ j')
      (hp' : ∀ k, 0 < p'.p k) (hq' : ∀ k, 0 < q'.p k)
      (hpComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p k)
      (hqComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p k),
      Classical.choose
          (hDiff.deriv_exists
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
            (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j')
            (by
              intro h
              exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h))
            hpComb hqComb) =
        Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq')

theorem derivTwoBlockTransport_of_ratio
    (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F)
    (hRatio : DerivRatioInvariant F hDiff) :
    DerivTwoBlockTransport F hDiff := by
  refine ⟨?left, ?right⟩
  · intro n m w hw0 hw1 p q p' q' i j hij hp hq hpComb hqComb
    have hij_inl :
        inlFin (n := n) (m := m) i ≠ inlFin (n := n) (m := m) j := by
      intro h
      exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h)
    have hwne : w ≠ 0 := ne_of_gt hw0
    have hratio_i :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inlFin (n := n) (m := m) i) /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inlFin (n := n) (m := m) i) =
          q.p i / p.p i := by
      simp [twoBlock_apply_inl, mul_div_mul_left, hwne]
    have hratio_j :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inlFin (n := n) (m := m) j) /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inlFin (n := n) (m := m) j) =
          q.p j / p.p j := by
      simp [twoBlock_apply_inl, mul_div_mul_left, hwne]
    exact
      hRatio
        (p := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
        (q := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (p' := p) (q' := q)
        (i := inlFin (n := n) (m := m) i) (j := inlFin (n := n) (m := m) j)
        (i' := i) (j' := j) (hij := hij_inl) (hi'j' := hij)
        (hp := hpComb) (hq := hqComb) (hp' := hp) (hq' := hq)
        hratio_i hratio_j
  · intro n m w hw0 hw1 p q p' q' i' j' hi'j' hp' hq' hpComb hqComb
    have hi'j'_inr :
        inrFin (n := n) (m := m) i' ≠ inrFin (n := n) (m := m) j' := by
      intro h
      exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h)
    have h1wne : 1 - w ≠ 0 := ne_of_gt (sub_pos.mpr hw1)
    have hratio_i :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inrFin (n := n) (m := m) i') /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inrFin (n := n) (m := m) i') =
          q'.p i' / p'.p i' := by
      simp [twoBlock_apply_inr, mul_div_mul_left, h1wne]
    have hratio_j :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inrFin (n := n) (m := m) j') /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inrFin (n := n) (m := m) j') =
          q'.p j' / p'.p j' := by
      simp [twoBlock_apply_inr, mul_div_mul_left, h1wne]
    exact
      hRatio
        (p := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
        (q := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (p' := p') (q' := q')
        (i := inrFin (n := n) (m := m) i') (j := inrFin (n := n) (m := m) j')
        (i' := i') (j' := j') (hij := hi'j'_inr) (hi'j' := hi'j')
        (hp := hpComb) (hq := hqComb) (hp' := hp') (hq' := hq')
        hratio_i hratio_j

theorem eq_twoBlock_of_isMinimizer_twoBlock_ev_of_realizesEV
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : Inference.ShoreJohnsonAxioms I) (hF : RealizesEV I F) :
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
  have hInf₁ : I.Infer p₁ (toConstraintSet cs₁) q₁ :=
    (hF.infer_iff_minimizer_ev (p := p₁) (cs := cs₁) (q := q₁)).2 hq₁
  have hInf₂ : I.Infer p₂ (toConstraintSet cs₂) q₂ :=
    (hF.infer_iff_minimizer_ev (p := p₂) (cs := cs₂) (q := q₂)).2 hq₂
  have hInf' :
      I.Infer (Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂)) q := by
    rcases hq with ⟨hq_mem, hq_le⟩
    refine (hF.infer_iff_minimizer_ev (p := _)
      (cs := twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) (q := q)).2 ?_
    refine ⟨?_, hq_le⟩
    simpa [heq] using hq_mem
  have hInf :
      I.Infer (Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (Inference.ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
          (toConstraintSet cs₁) (toConstraintSet cs₂)) q := by
    simpa [heq] using hInf'
  exact hSJ.subset_independent_twoBlock w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂
    (toConstraintSet cs₁) (toConstraintSet cs₂) q₁ q₂ q (admissible_ev p₁ cs₁ hp₁) (admissible_ev p₂ cs₂ hp₂) hInf₁ hInf₂ hInf

/-- Combine the actual two posteriors, then exchange matching coordinates.
No inferred combined posterior or universal existence hypothesis is needed. -/
theorem derivLocal_of_transport (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F)
    (hPerm : ObjectivePermuteInvariant F) (hTransport : DerivTwoBlockTransport F hDiff) :
    DerivLocalAssumption F hDiff := by
  intro n m p q p' q' i j i' j' hij hi'j' hp hq hp' hq' _ _ h_qi h_pi h_qj h_pj
  let w : ℝ := 1/2
  have hw0 : 0 < w := by norm_num [w]
  have hw1 : w < 1 := by norm_num [w]
  let pComb := ProbDist.twoBlock w hw0.le hw1.le p p'
  let qComb := ProbDist.twoBlock w hw0.le hw1.le q q'
  have hCombEq : qComb = ProbDist.twoBlock w hw0.le hw1.le q q' := rfl
  have hPermDeriv : DerivPermuteInvariant F hDiff :=
    derivPermuteInvariant_of_objectivePermuteInvariant F hDiff hPerm
  have hTransport' : DerivTwoBlockTransport F hDiff := by
    exact hTransport

  have hpComb : ∀ k, 0 < pComb.p k := by
    intro k
    classical
    cases h : (finSumFinEquiv (m := n) (n := m)).symm k with
    | inl i0 =>
        have hk : k = inlFin (n := n) (m := m) i0 := by
          simpa [inlFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        exact twoBlock_pos_inl_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := p) (P₂ := p') i0 hp
    | inr j0 =>
        have hk : k = inrFin (n := n) (m := m) j0 := by
          simpa [inrFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        exact twoBlock_pos_inr_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := p) (P₂ := p') j0 hp'

  have hqComb : ∀ k, 0 < qComb.p k := by
    intro k
    classical
    cases h : (finSumFinEquiv (m := n) (n := m)).symm k with
    | inl i0 =>
        have hk : k = inlFin (n := n) (m := m) i0 := by
          simpa [inlFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        simpa [hCombEq] using
          (twoBlock_pos_inl_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := q) (P₂ := q') i0 hq)
    | inr j0 =>
        have hk : k = inrFin (n := n) (m := m) j0 := by
          simpa [inrFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        simpa [hCombEq] using
          (twoBlock_pos_inr_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := q) (P₂ := q') j0 hq')

  let σi : Equiv.Perm (Fin (n + m)) :=
    Equiv.swap (inlFin (n := n) (m := m) i) (inrFin (n := n) (m := m) i')
  let σj : Equiv.Perm (Fin (n + m)) :=
    Equiv.swap (inlFin (n := n) (m := m) j) (inrFin (n := n) (m := m) j')

  have hpiw : w * p.p i = (1 - w) * p'.p i' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * p.p i = (1 - w) * p.p i := by simp [hhalf]
      _ = (1 - w) * p'.p i' := by simp [h_pi]
  have hpjw : w * p.p j = (1 - w) * p'.p j' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * p.p j = (1 - w) * p.p j := by simp [hhalf]
      _ = (1 - w) * p'.p j' := by simp [h_pj]
  have hqiw : w * q.p i = (1 - w) * q'.p i' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * q.p i = (1 - w) * q.p i := by simp [hhalf]
      _ = (1 - w) * q'.p i' := by simp [h_qi]
  have hqjw : w * q.p j = (1 - w) * q'.p j' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * q.p j = (1 - w) * q.p j := by simp [hhalf]
      _ = (1 - w) * q'.p j' := by simp [h_qj]

  have hpComb_perm_i : ProbDist.permute σi pComb = pComb := by
    dsimp [pComb, σi]
    exact
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := p) (P₂ := p') (i := i) (j := i') hpiw)
  have hpComb_perm_j : ProbDist.permute σj pComb = pComb := by
    dsimp [pComb, σj]
    exact
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := p) (P₂ := p') (i := j) (j := j') hpjw)

  have hqComb_perm_i : ProbDist.permute σi qComb = qComb := by
    dsimp [σi]
    simpa [hCombEq] using
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := q) (P₂ := q') (i := i) (j := i') hqiw)
  have hqComb_perm_j : ProbDist.permute σj qComb = qComb := by
    dsimp [σj]
    simpa [hCombEq] using
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := q) (P₂ := q') (i := j) (j := j') hqjw)

  have hij_inl : inlFin (n := n) (m := m) i ≠ inlFin (n := n) (m := m) j := by
    intro h
    exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h)
  have hi'j'_inr : inrFin (n := n) (m := m) i' ≠ inrFin (n := n) (m := m) j' := by
    intro h
    exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h)
  have h_inr_inl : inrFin (n := n) (m := m) i' ≠ inlFin (n := n) (m := m) j := by
    intro h
    exact (inlFin_ne_inrFin (n := n) (m := m) j i') h.symm

  have hL1 :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inlFin (n := n) (m := m) j) h_inr_inl hpComb hqComb) := by
    have hperm :=
      hPermDeriv (σ := σi) (p := pComb) (q := qComb)
        (i := inlFin (n := n) (m := m) i) (j := inlFin (n := n) (m := m) j)
        (hij := hij_inl) (hp := hpComb) (hq := hqComb)

    have hσi_i :
        σi (inlFin (n := n) (m := m) i) = inrFin (n := n) (m := m) i' := by
      simp [σi]
    have hσi_j :
        σi (inlFin (n := n) (m := m) j) = inlFin (n := n) (m := m) j := by
      have hji :
          inlFin (n := n) (m := m) j ≠ inlFin (n := n) (m := m) i := by
        intro h
        exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h).symm
      have hji' :
          inlFin (n := n) (m := m) j ≠ inrFin (n := n) (m := m) i' := by
        exact inlFin_ne_inrFin (n := n) (m := m) j i'
      simpa [σi] using
        (Equiv.swap_apply_of_ne_of_ne (a := inlFin (n := n) (m := m) i)
          (b := inrFin (n := n) (m := m) i') (x := inlFin (n := n) (m := m) j) hji hji')

    simpa [hpComb_perm_i, hqComb_perm_i, hσi_i, hσi_j] using hperm

  have hL2 :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inlFin (n := n) (m := m) j) h_inr_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr hpComb hqComb) := by
    have hperm :=
      hPermDeriv (σ := σj) (p := pComb) (q := qComb)
        (i := inrFin (n := n) (m := m) i') (j := inlFin (n := n) (m := m) j)
        (hij := h_inr_inl) (hp := hpComb) (hq := hqComb)
    have hσj_i :
        σj (inrFin (n := n) (m := m) i') = inrFin (n := n) (m := m) i' := by
      have hia :
          inrFin (n := n) (m := m) i' ≠ inlFin (n := n) (m := m) j := by
        intro h
        exact (inlFin_ne_inrFin (n := n) (m := m) j i') h.symm
      have hib :
          inrFin (n := n) (m := m) i' ≠ inrFin (n := n) (m := m) j' := by
        intro h
        exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h)
      simpa [σj] using
        (Equiv.swap_apply_of_ne_of_ne (a := inlFin (n := n) (m := m) j)
          (b := inrFin (n := n) (m := m) j') (x := inrFin (n := n) (m := m) i') hia hib)
    have hσj_j :
        σj (inlFin (n := n) (m := m) j) = inrFin (n := n) (m := m) j' := by
      simp [σj]
    simpa [hpComb_perm_j, hqComb_perm_j, hσj_i, hσj_j] using hperm

  have hLcomb :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr hpComb hqComb) :=
    hL1.trans hL2

  have hTransport_left' :
      Classical.choose (hDiff.deriv_exists pComb
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl
        (by
          intro k
          simpa [pComb] using hpComb k)
        (by
          intro k
          simpa [hCombEq] using hqComb k)) =
      Classical.choose (hDiff.deriv_exists p q i j hij hp hq) := by
    simpa [pComb] using
      (hTransport'.left (w := w) (hw0 := hw0) (hw1 := hw1)
        (p := p) (q := q) (p' := p') (q' := q')
        (i := i) (j := j) (hij := hij)
        (hp := hp) (hq := hq)
        (hpComb := by
          intro k
          simpa [pComb] using hpComb k)
        (hqComb := by
          intro k
          simpa [hCombEq] using hqComb k))

  have hTransport_left :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists p q i j hij hp hq) := by
    simpa [hCombEq] using hTransport_left'

  have hTransport_right' :
      Classical.choose (hDiff.deriv_exists pComb
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr
        (by
          intro k
          simpa [pComb] using hpComb k)
        (by
          intro k
          simpa [hCombEq] using hqComb k)) =
      Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq') := by
    simpa [pComb] using
      (hTransport'.right (w := w) (hw0 := hw0) (hw1 := hw1)
        (p := p) (q := q) (p' := p') (q' := q')
        (i' := i') (j' := j') (hi'j' := hi'j')
        (hp' := hp') (hq' := hq')
        (hpComb := by
          intro k
          simpa [pComb] using hpComb k)
        (hqComb := by
          intro k
          simpa [hCombEq] using hqComb k))

  have hTransport_right :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq') := by
    simpa [hCombEq] using hTransport_right'

  exact hTransport_left.symm.trans (hLcomb.trans hTransport_right)

end KnuthSkilling.ShoreJohnson.SJ3Locality
