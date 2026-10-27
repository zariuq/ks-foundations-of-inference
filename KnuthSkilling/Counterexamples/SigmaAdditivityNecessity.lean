import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Boundaries of countable observation

Finite subsets are not closed under countable unions. Rational scales admit
bounded increasing approximations with unrepresented real limits. A free-ultrafilter
charge on all subsets of ℕ is normalized and finitely additive, but not countably
additive. These are separate obstructions, not a proof that every sufficient
hypothesis in the countable KS theorem is logically necessary for every model.
The finite/infinite indicator is retained as a weaker discontinuity example;
it is not finitely additive on the full powerset.
-/

namespace KnuthSkilling.Counterexamples.SigmaAdditivityNecessity
open scoped Classical
open Filter
open scoped Topology

private theorem singleton_cover : (⋃ n, ({n} : Set ℕ)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact ⟨x, rfl⟩

def FinSubsets := {A : Set ℕ | A.Finite}
theorem finSubsets_union_closed (A B : Set ℕ) (hA : A.Finite) (hB : B.Finite) :
    (A ∪ B).Finite := hA.union hB

theorem finSubsets_not_sigma_complete :
    let f : ℕ → Set ℕ := fun n => {n}
    (∀ n, (f n).Finite) ∧ ¬(⋃ n, f n).Finite := by
  constructor
  · exact Set.finite_singleton
  · rw [singleton_cover]; exact Set.infinite_univ

theorem sigma_completeness_required_to_state :
    ∃ f : ℕ → Set ℕ, (∀ n, (f n).Finite) ∧ ¬(⋃ n, f n).Finite :=
  ⟨fun n => {n}, finSubsets_not_sigma_complete⟩

namespace RationalScale

theorem rat_archimedean : ∀ x y : ℚ, 0 < x → ∃ n : ℕ, y < n * x := by
  intro x y hx
  obtain ⟨n, hn⟩ := exists_nat_gt (y / x)
  exact ⟨n, (div_lt_iff₀ hx).mp hn⟩

/-- A bounded sequence whose limit is rational; not an incompleteness witness. -/
def geometric_partial_sums : ℕ → ℚ := fun n => 2 - 1 / 2^n
theorem geometric_bounded : ∀ n, geometric_partial_sums n < 2 := by
  intro n
  dsimp [geometric_partial_sums]
  have h : (0 : ℚ) < 1 / 2^n := by positivity
  linarith

theorem sqrt2_irrational : ¬∃ q : ℚ, q^2 = 2 := by
  rintro ⟨q, hq⟩
  have hs : |(q : ℝ)| = Real.sqrt 2 := by
    rw [← Real.sqrt_sq_eq_abs, show (q : ℝ)^2 = 2 from by exact_mod_cast hq]
  rcases le_or_gt 0 (q : ℝ) with h | h
  · exact irrational_sqrt_two.ne_rat q (by simpa [abs_of_nonneg h] using hs.symm)
  · exact irrational_sqrt_two.ne_rat (-q) (by simpa [abs_of_neg h] using hs.symm)

theorem rational_scale_not_complete : ¬∃ q : ℚ, q^2 = 2 := sqrt2_irrational
theorem sqrt2_not_rational : ¬∃ q : ℚ, q * q = 2 := by simpa only [sq] using sqrt2_irrational
theorem rational_scale_incomplete_for_irrational_limits : ¬∃ s : ℚ, s * s = 2 := sqrt2_not_rational

/-- An actual bounded increasing rational sequence with no rational real limit. -/
theorem bounded_monotone_without_rational_limit :
    ∃ u : ℕ → ℚ, StrictMono u ∧ BddAbove (Set.range u) ∧
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (Real.sqrt 2)) ∧
      ¬∃ q : ℚ, Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (q : ℝ)) := by
  obtain ⟨u, hu, hb, ht⟩ := Rat.isDenseEmbedding_coe_real.dense.exists_seq_strictMono_tendsto
    (show Monotone ((↑) : ℚ → ℝ) from fun _ _ h => by exact_mod_cast h) (Real.sqrt 2)
  refine ⟨u, hu, ⟨2, ?_⟩, ht, ?_⟩
  · rintro _ ⟨n, rfl⟩
    have h : (u n : ℝ) ≤ 2 := (hb n).le.trans (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
    exact_mod_cast h
  · rintro ⟨q, hq⟩
    exact irrational_sqrt_two.ne_rat q (tendsto_nhds_unique ht hq)
end RationalScale

namespace DiscontinuousValuation

/-- A monotone finite/infinite indicator, not a finitely additive charge. -/
noncomputable def diffuse (A : Set ℕ) : ℝ := if A.Finite then 0 else 1

theorem diffuse_singleton (n : ℕ) : diffuse {n} = 0 := by simp [diffuse]
theorem diffuse_univ : diffuse Set.univ = 1 := if_neg Set.infinite_univ
theorem diffuse_finite (A : Set ℕ) (hA : A.Finite) : diffuse A = 0 := if_pos hA
theorem diffuse_infinite (A : Set ℕ) (hA : ¬A.Finite) : diffuse A = 1 := if_neg hA

theorem union_singletons_eq_univ : (⋃ n, ({n} : Set ℕ)) = Set.univ := singleton_cover

theorem diffuse_union_singletons : diffuse (⋃ n, ({n} : Set ℕ)) = 1 := by
  rw [union_singletons_eq_univ, diffuse_univ]

theorem diffuse_not_sigma_additive :
    let f : ℕ → Set ℕ := fun n => {n}
    (∀ i j, i ≠ j → Disjoint (f i) (f j)) ∧ (⋃ n, f n) = Set.univ ∧
      (∑' n, diffuse (f n)) ≠ diffuse (⋃ n, f n) := by
  refine ⟨fun i j h => Set.disjoint_singleton.mpr h, union_singletons_eq_univ, ?_⟩
  simp [diffuse_singleton, diffuse_union_singletons]

theorem union_finite_prefixes_eq_univ : (⋃ n, (Finset.range n : Set ℕ)) = Set.univ := by
  ext x; simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, Set.mem_univ, iff_true]
  exact ⟨x+1, Nat.lt_succ_self x⟩
theorem union_finite_prefixes_infinite : ¬(⋃ n, (Finset.range n : Set ℕ)).Finite := by
  rw [union_finite_prefixes_eq_univ]; exact Set.infinite_univ

theorem diffuse_not_scott_continuous :
    let partials : ℕ → Set ℕ := fun n => (Finset.range n : Set ℕ)
    Monotone partials ∧ (⋃ n, partials n) = Set.univ ∧
      (∀ n, diffuse (partials n) = 0) ∧ diffuse (⋃ n, partials n) = 1 := by
  refine ⟨fun _ _ h => by simpa using Set.Iio_subset_Iio h,
    union_finite_prefixes_eq_univ, fun n => diffuse_finite _ (Finset.finite_toSet _), ?_⟩
  rw [union_finite_prefixes_eq_univ, diffuse_univ]

/-- Its failure already occurs for a pair of disjoint infinite sets. -/
theorem diffuse_not_finitely_additive :
    ∃ A B : Set ℕ, Disjoint A B ∧ diffuse (A ∪ B) ≠ diffuse A + diffuse B := by
  let A := Set.range (fun n : ℕ => 2*n)
  let B := Set.range (fun n : ℕ => 2*n+1)
  have ha : A.Infinite := Set.infinite_range_of_injective (by intro a b h; dsimp at h; omega)
  have hb : B.Infinite := Set.infinite_range_of_injective (by intro a b h; dsimp at h; omega)
  refine ⟨A, B, Set.disjoint_left.mpr ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ ⟨b, h⟩; dsimp at h; omega
  · simp [diffuse, ha.not_finite, hb.not_finite, (ha.mono Set.subset_union_left).not_finite]
end DiscontinuousValuation

namespace UltrafilterCharge

/-- Membership in a free ultrafilter defines a normalized 0/1 charge. -/
noncomputable def charge (A : Set ℕ) : ℝ := by
  classical
  exact if A ∈ hyperfilter ℕ then 1 else 0

theorem charge_finite (A : Set ℕ) (h : A.Finite) : charge A = 0 := by
  simp [charge, h.notMem_hyperfilter]
@[simp] theorem charge_singleton (n : ℕ) : charge {n} = 0 := charge_finite _ (Set.finite_singleton _)
@[simp] theorem charge_empty : charge ∅ = 0 := charge_finite _ Set.finite_empty
@[simp] theorem charge_univ : charge Set.univ = 1 := by
  classical
  exact if_pos (show Set.univ ∈ hyperfilter ℕ from Filter.univ_mem)

theorem charge_nonneg (A : Set ℕ) : 0 ≤ charge A := by unfold charge; split_ifs <;> norm_num

theorem charge_mono : Monotone charge := by
  classical
  intro A B hab
  by_cases ha : A ∈ hyperfilter ℕ
  · have hb : B ∈ hyperfilter ℕ := mem_of_superset ha hab
    simp [charge, ha, hb]
  · simp only [charge, if_neg ha]; split_ifs <;> norm_num

theorem charge_additive (A B : Set ℕ) (hd : Disjoint A B) : charge (A ∪ B) = charge A + charge B := by
  classical
  have hnot : ¬(A ∈ hyperfilter ℕ ∧ B ∈ hyperfilter ℕ) := by
    rintro ⟨ha, hb⟩
    have hi := inter_mem ha hb
    rw [Set.disjoint_iff_inter_eq_empty.mp hd] at hi
    exact (empty_notMem (hyperfilter ℕ).toFilter) hi
  by_cases ha : A ∈ hyperfilter ℕ <;> by_cases hb : B ∈ hyperfilter ℕ
  · exact (hnot ⟨ha, hb⟩).elim
  all_goals simp [charge, Ultrafilter.union_mem_iff, ha, hb]

theorem charge_not_sigma_additive :
    (∑' n, charge {n}) ≠ charge (⋃ n, ({n} : Set ℕ)) := by
  rw [DiscontinuousValuation.union_singletons_eq_univ]; simp

/-- The same normalized finitely additive observation fails at increasing prefixes. -/
theorem charge_not_continuous_from_below :
    (∀ n, charge (Finset.range n) = 0) ∧ charge (⋃ n, (Finset.range n : Set ℕ)) = 1 := by
  exact ⟨fun _ => charge_finite _ (Finset.finite_toSet _), by
    rw [DiscontinuousValuation.union_finite_prefixes_eq_univ, charge_univ]⟩
end UltrafilterCharge
end KnuthSkilling.Counterexamples.SigmaAdditivityNecessity
