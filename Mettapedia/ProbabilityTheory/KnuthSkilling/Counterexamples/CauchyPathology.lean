/-
# Counterexamples: Cauchy Equation Without Regularity

Appendix C reduces (after log-coordinates) to a Cauchy-style additive functional equation.
Without a regularity hypothesis (measurable / continuous / bounded-on-an-interval / ...),
Cauchy’s equation has **wild** solutions.

This file constructs an explicit additive function `f : ℝ → ℝ` that is *not* of the form
`x ↦ A * x`, hence cannot be continuous/measurable.

We then show how to turn such an `f` into a counterexample on positive reals:
`H'(m) := f (log m)` satisfies the multiplicative-additive equation on `m > 0`, but is not
`B + C * log m`.
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples

open Classical
open Set

/-! ## A concrete non-`A * x` additive map `ℝ → ℝ`

We work with `ℝ` as a vector space over `ℚ`.

We first prove `{1, √2}` is `ℚ`-linearly independent, then extend it to a Hamel basis and
define a `ℚ`-linear map that sends `1 ↦ 0` and `√2 ↦ 1` and vanishes on the other basis vectors.
-/

private theorem linearIndepOn_one_sqrt2 :
    LinearIndepOn ℚ id ({(1 : ℝ), Real.sqrt 2} : Set ℝ) := by
  classical
  -- Reduce to the two-coefficient criterion.
  have hne : (1 : ℝ) ≠ Real.sqrt 2 := ne_of_lt Real.one_lt_sqrt_two
  -- `LinearIndepOn.pair_iff` is stated for arbitrary index types; here indices are reals.
  have hpair :=
    (LinearIndepOn.pair_iff (R := ℚ) (f := id) (i := (1 : ℝ))
      (j := Real.sqrt 2) hne)
  -- Prove the two-coefficient condition using irrationality of `√2`.
  refine hpair.2 ?_
  intro c d hcd
  have hcd' : (c : ℝ) + (d : ℝ) * (Real.sqrt 2 : ℝ) = 0 := by
    simpa using hcd
  -- If `d = 0`, the equation forces `c = 0`.
  by_cases hd : d = 0
  · subst hd
    have hc : (c : ℝ) = 0 := by
      simpa using hcd'
    have hcq : c = 0 := by exact_mod_cast hc
    exact ⟨hcq, rfl⟩
  -- If `d ≠ 0`, solve for `√2` and contradict irrationality.
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have hsqrt : (Real.sqrt 2 : ℝ) = -((c : ℝ) / (d : ℝ)) := by
      have hmul : (d : ℝ) * (Real.sqrt 2 : ℝ) = -(c : ℝ) := by nlinarith [hcd']
      have hdiv : (Real.sqrt 2 : ℝ) = -(c : ℝ) / (d : ℝ) := by
        have : (Real.sqrt 2 : ℝ) * (d : ℝ) = -(c : ℝ) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        exact (eq_div_iff hdR).2 this
      simpa [neg_div] using hdiv
    have hsqrtRange : (Real.sqrt 2 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := by
      refine ⟨-(c / d), ?_⟩
      have hcast : ((-(c / d) : ℚ) : ℝ) = -((c : ℝ) / (d : ℝ)) := by simp
      exact hcast.trans hsqrt.symm
    exact (irrational_sqrt_two hsqrtRange).elim

/-- A Hamel basis of `ℝ` over `ℚ` extending `{1, √2}`.

The index type is a subtype of `ℝ` (a set of vectors), and `b i = (i : ℝ)`.
-/
noncomputable def hamelBasis :
    Module.Basis (↑((linearIndepOn_one_sqrt2).extend (Set.subset_univ _))) ℚ ℝ :=
  Module.Basis.extend linearIndepOn_one_sqrt2

/-- The `ℚ`-linear map that sends `1 ↦ 0`, `√2 ↦ 1`, and all other basis vectors to `0`. -/
noncomputable def weirdQLinear : ℝ →ₗ[ℚ] ℝ :=
  (hamelBasis).constr ℚ fun i =>
    if (i : ℝ) = Real.sqrt 2 then (1 : ℝ) else 0

/-- The underlying function of `weirdQLinear`. It satisfies Cauchy’s equation. -/
noncomputable def weirdAdditive : ℝ → ℝ := fun x => weirdQLinear x

theorem weirdAdditive_add (x y : ℝ) : weirdAdditive (x + y) = weirdAdditive x + weirdAdditive y := by
  simp [weirdAdditive]

/-- `weirdAdditive` is not of the form `x ↦ A * x`. -/
theorem weirdAdditive_not_mul (A : ℝ) : ∃ x : ℝ, weirdAdditive x ≠ A * x := by
  classical
  -- Evaluate at `x = 1` and `x = √2` by choosing the corresponding basis indices.
  let idxOne :
      ↑((linearIndepOn_one_sqrt2).extend (Set.subset_univ _)) :=
    ⟨(1 : ℝ),
      (linearIndepOn_one_sqrt2.subset_extend (Set.subset_univ _)) (by simp)⟩
  have h_idxOne : hamelBasis idxOne = (1 : ℝ) := by
    simp [hamelBasis, idxOne]
  have h1 : weirdAdditive 1 = 0 := by
    -- Since `idxOne ≠ √2`, `weirdQLinear` sends it to `0`.
    have hne : (idxOne : ℝ) ≠ Real.sqrt 2 := by
      simpa using (ne_of_lt Real.one_lt_sqrt_two)
    -- Evaluate on the basis element, then rewrite `hamelBasis idxOne = 1`.
    have : weirdAdditive (hamelBasis idxOne) = 0 := by
      simp [weirdAdditive, weirdQLinear, idxOne, hne]
    simpa [h_idxOne] using this

  let idxSqrt :
      ↑((linearIndepOn_one_sqrt2).extend (Set.subset_univ _)) :=
    ⟨(Real.sqrt 2 : ℝ),
      (linearIndepOn_one_sqrt2.subset_extend (Set.subset_univ _)) (by simp)⟩
  have h_idxSqrt : hamelBasis idxSqrt = (Real.sqrt 2 : ℝ) := by
    simp [hamelBasis, idxSqrt]
  have hs : weirdAdditive (Real.sqrt 2) = 1 := by
    have : weirdAdditive (hamelBasis idxSqrt) = 1 := by
      simp [weirdAdditive, weirdQLinear, idxSqrt]
    simpa [h_idxSqrt] using this
  by_cases hA : A = 0
  · subst hA
    exact ⟨Real.sqrt 2, by simp [hs]⟩
  · -- If `A ≠ 0`, then `A * 1 ≠ 0` but `weirdAdditive 1 = 0`.
    have hA0 : (0 : ℝ) ≠ A := by
      intro h0
      exact hA h0.symm
    exact ⟨1, by simpa [h1] using hA0⟩

/-! ## Turning an additive pathology into a positive-real counterexample

Define `H'(m) := weirdAdditive (log m)`. On `m_x, m_y > 0` we have:

`H'(m_x * m_y) = H'(m_x) + H'(m_y)`

but `H'` is not of the form `B + C * log m`.
-/

noncomputable def Hprime (m : ℝ) : ℝ := weirdAdditive (Real.log m)

theorem Hprime_mul (m_x m_y : ℝ) (hx : 0 < m_x) (hy : 0 < m_y) :
    Hprime (m_x * m_y) = Hprime m_x + Hprime m_y := by
  simp [Hprime, weirdAdditive_add, Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]

theorem Hprime_not_B_add_C_log :
    ¬ ∃ (B C : ℝ), ∀ m : ℝ, 0 < m → Hprime m = B + C * Real.log m := by
  rintro ⟨B, C, hBC⟩
  have h0 : weirdAdditive 0 = 0 := by
    have h := weirdAdditive_add 0 0
    simp at h
    linarith
  have hB : B = 0 := by
    -- plug `m = 1`
    have := hBC 1 one_pos
    simp [Hprime, Real.log_one, h0] at this
    linarith
  -- Then `weirdAdditive x = C*x` by testing `m = exp x`.
  have hlin : ∀ x : ℝ, weirdAdditive x = C * x := by
    intro x
    have := hBC (Real.exp x) (Real.exp_pos x)
    simpa [Hprime, Real.log_exp, hB] using this
  -- Contradiction with `weirdAdditive_not_mul`.
  rcases weirdAdditive_not_mul C with ⟨x, hx⟩
  exact hx (hlin x)

end Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples
