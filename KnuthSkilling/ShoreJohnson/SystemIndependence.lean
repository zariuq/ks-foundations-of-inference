import KnuthSkilling.ShoreJohnson.Proof

/-!
# Shore–Johnson atom analysis: product additivity implies logarithmic form

This file exports a small but central piece of Shore–Johnson’s 1980 argument:

If an “atomic divergence” `d : ℝ → ℝ → ℝ` is

- **regular at 0** (`d 0 x = 0`), and
- **system independent** in the sense that the sum `∑ d(p_i,q_i)` is additive over product
  distributions,

then Dirac-delta test distributions force a **multiplicative Cauchy equation** for
`g(q) := d 1 q` on the probability domain `0 < q ≤ 1`.  With a minimal regularity gate
(Borel measurability of `g`), we obtain the logarithmic form `g(q) = C * log q`.

This is the clean point of contact with Knuth–Skilling Appendix C: both derivations reduce to
Cauchy-type functional equations, and both require an explicit “anti-pathology” regularity gate
to exclude Hamel-basis solutions.

We do **not** attempt a full formalization of Shore–Johnson Theorem 1 (global KL uniqueness) here.

For a stronger (but still explicitly-scoped) KL uniqueness statement--showing that any **ratio-form**
atom divergence `d(w,u)=w*g(w/u)` satisfying a multiplicative Cauchy equation is a constant multiple
of the KL atom (with a measurability regularity gate), and that uniqueness fails without such
regularity--see `KnuthSkilling/ShoreJohnson/KL.lean`.
-/

namespace KnuthSkilling.ShoreJohnson.SystemIndependence

open Real

open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Proof
open KnuthSkilling.Variational

/-- An atom-level product-additivity profile, distinct from factorization of
selected posteriors. The unrestricted variant is not satisfied by the total-real
KL atom; use the positive-reference profile for that application. -/
structure SJSystemIndependenceAtom (d : ℝ → ℝ → ℝ) : Prop where
  regularAtom : RegularAtom d
  add_over_products :
    ∀ {n m : ℕ} [NeZero n] [NeZero m], ∀ P Q : ProbDist n, ∀ R S : ProbDist m,
      ∑ ij : Fin n × Fin m, d ((P ⊗ R).p ij) ((Q ⊗ S).p ij) =
        (∑ i : Fin n, d (P.p i) (Q.p i)) + (∑ j : Fin m, d (R.p j) (S.p j))

/-- Atom product additivity with positive reference distributions. Full support
is a sufficient support condition. The Dirac/Cauchy theorem below uses this
profile directly, and KL has a concrete instance. -/
structure SJSystemIndependenceAtomPos (d : ℝ → ℝ → ℝ) : Prop where
  regularAtom : RegularAtom d
  add_over_products_pos :
    ∀ {n m : ℕ} [NeZero n] [NeZero m], ∀ P Q : ProbDist n, ∀ R S : ProbDist m,
      (∀ i, 0 < Q.p i) → (∀ j, 0 < S.p j) →
        ∑ ij : Fin n × Fin m, d ((P ⊗ R).p ij) ((Q ⊗ S).p ij) =
          (∑ i : Fin n, d (P.p i) (Q.p i)) + (∑ j : Fin m, d (R.p j) (S.p j))

/-- The strong (universal) system independence implies the weaker (positivity-restricted) version. -/
theorem SJSystemIndependenceAtomPos.of_SJSystemIndependenceAtom
    (h : SJSystemIndependenceAtom d) : SJSystemIndependenceAtomPos d where
  regularAtom := h.regularAtom
  add_over_products_pos := fun P Q R S _hQ _hS => h.add_over_products P Q R S

/-- **Main Shore–Johnson lemma used in this project**.

Under atomic system independence and measurability, `q ↦ d(1,q)` is forced to be logarithmic on
the probability domain `0 < q ≤ 1`. -/
theorem d_one_eq_const_mul_log_of_measurable
    (d : ℝ → ℝ → ℝ) (hSJ : SJSystemIndependenceAtom d)
    (hMeas : Measurable (d 1)) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → d 1 q = C * log q :=
  dirac_extraction_log_of_measurable d hSJ.regularAtom hSJ.add_over_products hMeas

/-- Repackage the log conclusion as a KS-style `entropyDerivative` (with `B = 0`). -/
theorem d_one_eq_entropyDerivative_of_measurable
    (d : ℝ → ℝ → ℝ) (hSJ : SJSystemIndependenceAtom d)
    (hMeas : Measurable (d 1)) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → d 1 q = entropyDerivative 0 C q := by
  rcases d_one_eq_const_mul_log_of_measurable d hSJ hMeas with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro q hq_pos hq_le1
  simpa [entropyDerivative] using hC q hq_pos hq_le1


/-- Positive references suffice for the Dirac/Cauchy argument. Endpoint probability
one is tested on one state, rather than by an unsupported binary reference. -/
theorem d_one_mul_cauchy_Ioc_of_pos (d : ℝ → ℝ → ℝ) (h : SJSystemIndependenceAtomPos d) :
    ∀ x y : ℝ, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → d 1 (x*y) = d 1 x + d 1 y := by
  let u : ProbDist 1 := diracDist 0
  have hu : ∀ i, 0 < u.p i := by intro i; fin_cases i; norm_num [u, diracDist]
  have h11 := dirac_extraction_at d h.regularAtom (0 : Fin 1) (0 : Fin 1) u u
    (h.add_over_products_pos u u u u hu hu)
  have hone : d 1 1 = 0 := by
    simp only [u, diracDist, ↓reduceIte, mul_one] at h11
    linarith
  intro x y hx hx1 hy hy1
  by_cases hxe : x = 1
  · simp [hxe, hone]
  by_cases hye : y = 1
  · simp [hye, hone]
  have hxlt : x < 1 := lt_of_le_of_ne hx1 hxe
  have hylt : y < 1 := lt_of_le_of_ne hy1 hye
  let q := binaryDist x hx.le hx1
  let s := binaryDist y hy.le hy1
  have hq : ∀ i, 0 < q.p i := by
    intro i; fin_cases i <;> simp [q, binaryDist] <;> linarith
  have hs : ∀ i, 0 < s.p i := by
    intro i; fin_cases i <;> simp [s, binaryDist] <;> linarith
  simpa [q, s, binaryDist] using dirac_extraction_at d h.regularAtom (0 : Fin 2) (0 : Fin 2) q s
    (h.add_over_products_pos (diracDist 0) q (diracDist 0) s hq hs)

theorem d_one_eq_const_mul_log_of_measurable_pos (d : ℝ → ℝ → ℝ)
    (h : SJSystemIndependenceAtomPos d) (hm : Measurable (d 1)) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 → d 1 x = C*Real.log x :=
  mul_cauchy_Ioc_eq_const_mul_log (d 1) (d_one_mul_cauchy_Ioc_of_pos d h) hm

end KnuthSkilling.ShoreJohnson.SystemIndependence
