import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Regraduations preserving the same real addition

An additive monotone real map is scalar multiplication, hence continuous.
Strict order preservation makes its scalar positive; surjectivity is unnecessary.
This concerns maps preserving ordinary addition on both sides. An order change
may instead transport addition to a different operation. Without order or other
regularity, the additive pathology in `CauchyPathology` remains possible.
-/

namespace KnuthSkilling.Counterexamples

private def additiveHom {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) : ℝ →+ ℝ :=
  AddMonoidHom.mk' f h

theorem additive_zero {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y) :
    f 0 = 0 := (additiveHom hadd).map_zero

theorem additive_nsmul {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y)
    (n : ℕ) (x : ℝ) : f (n * x) = n * f x := by
  simpa [additiveHom, nsmul_eq_mul] using map_nsmul (additiveHom hadd) n x

theorem additive_neg {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y) (x : ℝ) :
    f (-x) = -f x := map_neg (additiveHom hadd) x

theorem additive_zsmul {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y)
    (n : ℤ) (x : ℝ) : f (n * x) = n * f x := by
  simpa [additiveHom, zsmul_eq_mul] using map_zsmul (additiveHom hadd) n x

theorem additive_qsmul {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y)
    (q : ℚ) (x : ℝ) : f (q * x) = q * f x := by
  simpa [additiveHom, smul_eq_mul] using map_ratCast_smul (additiveHom hadd) ℝ ℝ q x

/-- Monotonicity extends the rational scalar law to every real argument. -/
theorem monotone_additive_is_linear {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y) (hmono : Monotone f) :
    ∀ x, f x = f 1 * x := by
  have hfq (q : ℚ) : f q = (q : ℝ) * f 1 := by
    simpa using additive_qsmul hadd q 1
  have bound (x : ℝ) : f x ≤ f 1 * x := by
    by_contra! hx
    by_cases hz : f 1 = 0
    · obtain ⟨q, hq⟩ := exists_rat_gt x
      have hh := hmono hq.le
      rw [hfq, hz] at hh
      simp only [hz, zero_mul] at hx
      linarith
    · have hp : 0 < f 1 := lt_of_le_of_ne
        (by simpa only [additive_zero hadd] using hmono (show (0 : ℝ) ≤ 1 by norm_num)) (Ne.symm hz)
      obtain ⟨q, hxq, hq⟩ := exists_rat_btwn ((lt_div_iff₀ hp).mpr (by nlinarith : x * f 1 < f x))
      have hh := hmono hxq.le
      rw [hfq] at hh
      have hq' := (lt_div_iff₀ hp).mp hq
      linarith
  intro x
  apply (bound x).antisymm
  have hh := bound (-x)
  rw [additive_neg hadd] at hh
  linarith

theorem monotone_additive_bijection_is_pos_linear {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y) (hmono : StrictMono f) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, f x = c * x := by
  refine ⟨f 1, ?_, monotone_additive_is_linear hadd hmono.monotone⟩
  simpa only [additive_zero hadd] using hmono (show (0 : ℝ) < 1 by norm_num)

theorem regrade_preserving_sum_rule_is_continuous {Θ : ℝ → ℝ}
    (hΘ_add : ∀ x y, Θ (x + y) = Θ x + Θ y) (hΘ_mono : Monotone Θ) : Continuous Θ := by
  rw [funext (monotone_additive_is_linear hΘ_add hΘ_mono)]
  exact continuous_const.mul continuous_id

end KnuthSkilling.Counterexamples
