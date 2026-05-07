import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Sqrt
import KnuthSkilling.Additive.Proofs.GridInduction.Core.Induction.Construction

/-!
This file was originally drafted as a quick “incommensurate δ breaks ZQuantized” counterexample.
The first attempt became too messy and is archived below.

The code that follows the archived block is the actual (working) counterexample.
-/

/- BEGIN ARCHIVED BROKEN DRAFT

namespace KnuthSkilling.Additive.Counterexamples

open Classical
open scoped BigOperators
open scoped NNReal

/-!
This file exhibits a concrete “B-empty” situation where `chooseδ` is forced to be > 1, but
`ZQuantized F R (chooseδ …)` fails.

This demonstrates that treating `ZQuantized` (with step `δ := chooseδ …`) as an inductive
invariant across a B-empty extension is not justified in general: in the B-empty regime,
`δ` is determined as a supremum of A-statistics and can be incommensurate with the old grid.
-/

section NNRealAdd

local instance : KnuthSkilling.KnuthSkillingAlgebra ℝ≥0 where
  op := (· + ·)
  ident := 0
  op_assoc := by intro x y z; simp [add_assoc]
  op_ident_right := by intro x; simp
  op_ident_left := by intro x; simp
  op_strictMono_left := by
    intro y
    intro x₁ x₂ hx
    exact add_lt_add_right hx y
  op_strictMono_right := by
    intro x
    intro y₁ y₂ hy
    exact add_lt_add_left hy x
  ident_le := by intro x; exact bot_le

open KnuthSkilling
open KnuthSkillingAlgebra

local notation "⊕" => KnuthSkillingAlgebraBase.op

local lemma iterate_op_add_eq_nsmul (x : ℝ≥0) : ∀ n : ℕ, iterate_op x n = n • x
  | 0 => by simp [KnuthSkillingAlgebra.iterate_op]
  | n + 1 => by
      simp [KnuthSkillingAlgebra.iterate_op, iterate_op_add_eq_nsmul x n, Nat.succ_eq_add_one,
        add_nsmul, add_comm, add_left_comm, add_assoc]

local lemma iterate_op_add_eq_mul (x : ℝ≥0) (n : ℕ) : iterate_op x n = (n : ℝ≥0) * x := by
  simpa [iterate_op_add_eq_nsmul, nsmul_eq_mul] using (iterate_op_add_eq_nsmul x n)

noncomputable def F1 : AtomFamily ℝ≥0 1 :=
  singletonAtomFamily (α := ℝ≥0) 1 (by simpa using (show (0 : ℝ≥0) < 1 from zero_lt_one))

noncomputable def R1 : MultiGridRep F1 where
  Θ_grid := fun x => (x.1 : ℝ)
  strictMono := by
    intro x y hxy
    exact_mod_cast hxy
  add := by
    intro r s
    classical
    -- Reduce μ on k=1 and use `iterate_op_add` (which is just addition here).
    let i0 : Fin 1 := ⟨0, by decide⟩
    have hμ_r : mu F1 r = iterate_op 1 (r i0) := by
      simp [F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero, op_ident_left]
    have hμ_s : mu F1 s = iterate_op 1 (s i0) := by
      simp [F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero, op_ident_left]
    have hμ_rs :
        mu F1 (fun i => r i + s i) = iterate_op 1 (r i0 + s i0) := by
      simp [F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero, op_ident_left]
    -- Cast `iterate_op_add` to ℝ.
    have haddNN : iterate_op 1 (r i0) ⊕ iterate_op 1 (s i0) = iterate_op 1 (r i0 + s i0) := by
      simpa using (iterate_op_add (a := (1 : ℝ≥0)) (m := r i0) (n := s i0))
    have haddℝ :
        ((iterate_op 1 (r i0 + s i0) : ℝ≥0) : ℝ) =
          ((iterate_op 1 (r i0) : ℝ≥0) : ℝ) + ((iterate_op 1 (s i0) : ℝ≥0) : ℝ) := by
      have := congrArg (fun t : ℝ≥0 => (t : ℝ)) haddNN.symm
      simpa using this
    -- Finish by rewriting all μ’s and unfolding Θ_grid.
    simp [R1, hμ_r, hμ_s, hμ_rs, haddℝ, add_comm, add_left_comm, add_assoc]
  ident_eq_zero := by simp [R1, ident_mem_kGrid (F := F1)]

noncomputable def d : ℝ≥0 := ⟨Real.sqrt 5, by
  have : (0 : ℝ) ≤ Real.sqrt 5 := by positivity
  exact this⟩

lemma d_pos : (0 : ℝ≥0) < d := by
  -- `sqrt 5 > 0`
  have : (0 : ℝ) < Real.sqrt 5 := by
    have : (0 : ℝ) < (5 : ℝ) := by norm_num
    simpa using Real.sqrt_pos.2 this
  exact_mod_cast this

lemma B_empty_for_F1_d : ∀ r u, 0 < u → r ∉ extensionSetB F1 d u := by
  intro r u hu hrB
  -- In this model: μ(F1,r) is an integer; d^u = u * √5 is irrational.
  have hirr : Irrational (Real.sqrt 5) := by
    simpa using (Nat.Prime.irrational_sqrt (p := 5) (by norm_num))
  have hirr_mul : Irrational (Real.sqrt 5 * (u : ℕ)) :=
    hirr.mul_natCast (m := u) (Nat.ne_of_gt hu)
  -- Rewrite the B equation in ℝ.
  have hEq : (mu F1 r : ℝ) = (iterate_op d u : ℝ) := congrArg (fun x : ℝ≥0 => (x : ℝ)) hrB
  -- `iterate_op d u = u * d` (Nat multiplication) and `d` coerces to `√5`.
  have h_iter : iterate_op d u = (u : ℝ≥0) * d := by
    simpa using (iterate_op_add_eq_mul d u)
  have h_rhs : (iterate_op d u : ℝ) = Real.sqrt 5 * (u : ℕ) := by
    -- coe ((u:ℝ≥0) * d) = (u:ℝ) * √5
    simp [h_iter, d, mul_comm, mul_left_comm, mul_assoc]
  have hEq' : (mu F1 r : ℝ) = Real.sqrt 5 * (u : ℕ) := by simpa [h_rhs] using hEq
  -- LHS is rational (an integer), RHS is irrational: contradiction.
  have : ¬ Irrational (mu F1 r : ℝ) := by
    -- Any NNReal coerces to a rational when it is a natural number; we only need:
    -- an irrational real cannot equal a rational one.
    exact (hirr_mul.ne_ratCast ((mu F1 r).toReal).ratCast).elim
  -- Use the fact directly: `hirr_mul` implies RHS is not equal to any rational, in particular `mu F1 r`.
  exact (hirr_mul.ne_ratCast ((mu F1 r).toReal).ratCast) (by
    -- `mu F1 r` is a real; present it as a rational cast using `Rat.cast_def` via `Real.toRat` is messy.
    -- Instead, just contradict irrationality by rewriting hEq' as an equality.
    -- (A simpler route is to use `hirr_mul.ne_intCast`.)
    simpa using hEq').elim

/-!
The previous lemma is intentionally conservative: it only needs to show that **some**
B-empty scenario exists. For the `ZQuantized` refutation below, we only need B-empty
as a hypothesis to force `chooseδ` into its B-empty branch.

The next result is the actual “do not treat this as an invariant” witness:
`chooseδ` is forced to be ≥ 2
(since `2 ∈ A` at level `u=1`), so `ZQuantized` cannot hold because `Θ(1)=1` is not an
integer multiple of any `δ ≥ 2`.
-/

theorem not_ZQuantized_chooseδ_in_B_empty_example :
    ¬ ZQuantized F1 R1 (chooseδ (α := ℝ≥0) (hk := (le_rfl : (1 : ℕ) ≥ 1)) R1 d (by
      simpa [KnuthSkillingAlgebraBase.ident] using d_pos)) := by
  classical
  -- Let δ be the chosen delta.
  set δ : ℝ := chooseδ (α := ℝ≥0) (hk := (le_rfl : (1 : ℕ) ≥ 1)) R1 d (by
    simpa [KnuthSkillingAlgebraBase.ident] using d_pos) with hδ
  -- Show δ ≥ 2, using the fact that `2 ∈ A(1)` when d = √5.
  have h2_lt_d : (2 : ℝ≥0) < d := by
    have h2_lt : (2 : ℝ) < Real.sqrt 5 := by
      -- 2 < √5 ↔ 2^2 < 5
      have : ((2 : ℝ) ^ 2) < (5 : ℝ) := by norm_num
      exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))).2 (by simpa using this)
    exact_mod_cast h2_lt
  -- Build an explicit A-statistic equal to 2.
  let r2 : Multi 1 := fun _ => 2
  have hr2A : r2 ∈ extensionSetA F1 d 1 := by
    -- μ(r2) = 2 and d^1 = d
    simp [extensionSetA, r2, F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero,
      op_ident_left, h2_lt_d, iterate_op_one, KnuthSkillingAlgebra.iterate_op, d]
  let AStats : Set ℝ :=
    {s : ℝ | ∃ r u, 0 < u ∧ r ∈ extensionSetA F1 d u ∧ s = R1.Θ_grid ⟨mu F1 r, mu_mem_kGrid F1 r⟩ / u}
  have hAStats_bdd : BddAbove AStats := by
    refine ⟨(d : ℝ), ?_⟩
    intro s hs
    rcases hs with ⟨r, u, hu, hrA, rfl⟩
    have huℝ : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
    have hμlt : (mu F1 r : ℝ) < (iterate_op d u : ℝ) := by exact_mod_cast hrA
    have h_iter : (iterate_op d u : ℝ) = (Real.sqrt 5) * (u : ℕ) := by
      have : iterate_op d u = (u : ℝ≥0) * d := iterate_op_add_eq_mul d u
      simp [this, d, mul_comm, mul_left_comm, mul_assoc]
    have : (mu F1 r : ℝ) / (u : ℝ) < (d : ℝ) := by
      -- Divide `μr < u*d` by u>0.
      have hμlt' : (mu F1 r : ℝ) < (u : ℝ) * (d : ℝ) := by
        -- Rewrite `iterate_op d u` as `(u:ℝ)*d`.
        have : (iterate_op d u : ℝ) = (u : ℝ) * (d : ℝ) := by
          simp [iterate_op_add_eq_mul, d, mul_assoc, mul_comm, mul_left_comm]
        simpa [this] using hμlt
      have := (div_lt_iff₀ huℝ).2 hμlt'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    exact le_of_lt this
  have h2_mem : (2 : ℝ) ∈ AStats := by
    refine ⟨r2, 1, Nat.one_pos, hr2A, ?_⟩
    simp [AStats, R1, r2, F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero,
      op_ident_left, KnuthSkillingAlgebra.iterate_op, div_eq_mul_inv]
  have h2_le : (2 : ℝ) ≤ δ := by
    -- In the B-empty branch, `chooseδ` is the sSup of AStats (definition of `B_empty_delta`).
    -- `le_csSup` gives any member is ≤ sSup.
  -- We don't need to compute δ exactly; this lower bound is enough to refute
  -- `ZQuantized F1 R1 (chooseδ …)` in this B-empty example.
    -- Unfold `chooseδ` and reduce to the B-empty branch.
    -- Note: here we avoid proving B-empty for all u; it's sufficient to show the branch selector is false.
    -- We show there is no B-witness for u=1 by irrationality; this implies the global `hB` is false.
    have hB_false : ¬ ∃ r u, 0 < u ∧ r ∈ extensionSetB F1 d u := by
      intro hB
      rcases hB with ⟨r, u, hu, hrB⟩
      -- But `u*√5` is irrational, so cannot equal μ(F1,r), which is in NNReal.
      have hirr : Irrational (Real.sqrt 5) := by
        simpa using (Nat.Prime.irrational_sqrt (p := 5) (by norm_num))
      have hirr_mul : Irrational (Real.sqrt 5 * (u : ℕ)) :=
        hirr.mul_natCast (m := u) (Nat.ne_of_gt hu)
      have hEq : (mu F1 r : ℝ) = (iterate_op d u : ℝ) := congrArg (fun x : ℝ≥0 => (x : ℝ)) hrB
      have h_iter : iterate_op d u = (u : ℝ≥0) * d := iterate_op_add_eq_mul d u
      have h_rhs : (iterate_op d u : ℝ) = Real.sqrt 5 * (u : ℕ) := by
        simp [h_iter, d, mul_comm, mul_left_comm, mul_assoc]
      have : (mu F1 r : ℝ) = Real.sqrt 5 * (u : ℕ) := by simpa [h_rhs] using hEq
      exact (hirr_mul.ne_intCast (mu F1 r)) (by simpa using this)
    -- Now unfold `chooseδ` into the B-empty branch, and apply `le_csSup`.
    -- (We reuse the exact definition of the AStats set from `B_empty_delta`.)
    -- The proof witnesses for A/C nonemptiness are irrelevant to the value; they only ensure the set is nonempty.
    have hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F1 d u := ⟨r2, 1, Nat.one_pos, hr2A⟩
    have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F1 d u := by
      -- Take r = 3 at u = 1: d = √5 < 3.
      let r3 : Multi 1 := fun _ => 3
      have hμ3 : mu F1 r3 = (3 : ℝ≥0) := by
        simp [r3, F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero, op_ident_left,
          KnuthSkillingAlgebra.iterate_op]
      have h_d_lt_3 : d < (3 : ℝ≥0) := by
        have h : (Real.sqrt 5) < (3 : ℝ) := by
          have : (Real.sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by
            -- 5 < 9
            simp
          -- Use `sqrt_lt` equivalence.
          have : Real.sqrt 5 < (3 : ℝ) := by
            have : (5 : ℝ) < (9 : ℝ) := by norm_num
            -- √5 < √9 = 3
            have : Real.sqrt 5 < Real.sqrt 9 := (Real.sqrt_lt_sqrt (by norm_num) this)
            simpa using this
          exact this
        exact_mod_cast h
      have hr3C : r3 ∈ extensionSetC F1 d 1 := by
        simp [extensionSetC, r3, F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero,
          op_ident_left, KnuthSkillingAlgebra.iterate_op, iterate_op_one, h_d_lt_3, d]
      exact ⟨r3, 1, Nat.one_pos, hr3C⟩
    -- Replace δ by B_empty_delta’s sSup and apply `le_csSup`.
    rw [hδ]
    unfold chooseδ
    split_ifs with hB
    · exact (hB_false hB).elim
    · -- This branch is `B_empty_delta = sSup AStats`; apply `le_csSup`.
      -- Unfold `B_empty_delta` and use the identical `AStats` set.
      unfold B_empty_delta
      -- The set used in `B_empty_delta` is `AStats` by definition, and `2 ∈ AStats`.
      -- So `2 ≤ sSup AStats`.
      -- Need to show bounded above to use `le_csSup`.
      exact le_csSup hAStats_bdd h2_mem
  -- Now show ZQuantized fails because Θ(1) is not an integer multiple of any δ ≥ 2.
  intro hZQ
  -- Apply ZQuantized to r=1.
  let r1 : Multi 1 := fun _ => 1
  rcases hZQ r1 with ⟨m, hm⟩
  have hμ1 : mu F1 r1 = (1 : ℝ≥0) := by
    simp [r1, F1, mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero, op_ident_left,
      KnuthSkillingAlgebra.iterate_op]
  have hθ1 : R1.Θ_grid ⟨mu F1 r1, mu_mem_kGrid F1 r1⟩ = 1 := by
    simp [R1, hμ1]
  have hδ_ge : (2 : ℝ) ≤ δ := h2_le
  have hδ_pos : 0 < δ := by
    -- δ ≥ 2 > 0
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hδ_ge
  -- Rewrite hm using hθ1 and derive contradiction.
  have hm' : (1 : ℝ) = (m : ℝ) * δ := by simpa [hθ1] using hm
  have : False := by
    -- If m ≤ 0 then RHS ≤ 0; if m ≥ 1 then RHS ≥ δ ≥ 2.
    have hm_cases : m ≤ 0 ∨ 1 ≤ m := le_total m 0 |> fun h => Or.imp_left id (fun h => by omega) ? PROOF_HOLE
    -- We'll just do a direct `linarith` split.
    by_cases hm0 : m ≤ 0
    · have : (m : ℝ) * δ ≤ 0 := by
        have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
        exact mul_le_mul_of_nonneg_right this (le_of_lt hδ_pos)
      have : (1 : ℝ) ≤ 0 := by linarith [hm', this]
      linarith
    · have hm1 : 1 ≤ m := by omega
      have : (2 : ℝ) ≤ (m : ℝ) * δ := by
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        have : δ ≤ (m : ℝ) * δ := by
          exact mul_le_mul_of_nonneg_right this (le_of_lt hδ_pos) |> by simpa [one_mul]
        exact le_trans hδ_ge this
      linarith [hm', this]
  exact this.elim

end NNRealAdd

end KnuthSkilling.Additive.Counterexamples

-/
-- END ARCHIVED BROKEN DRAFT

namespace KnuthSkilling.Additive.Counterexamples

open Classical
open scoped NNReal

open KnuthSkilling
open KnuthSkillingAlgebra

namespace ZQuantizedBEmpty

section

private lemma nat_iterate_add_left_eq_mul (x : ℝ≥0) :
    ∀ n : ℕ, Nat.iterate (fun z : ℝ≥0 => x + z) n x = ((n + 1 : ℕ) : ℝ≥0) * x
  | 0 => by simp
  | n + 1 => by
      have ih := nat_iterate_add_left_eq_mul x n
      -- `f^[n+1] x = x + f^[n] x`
      have h_step :
          Nat.iterate (fun z : ℝ≥0 => x + z) (n + 1) x
            = x + Nat.iterate (fun z : ℝ≥0 => x + z) n x := by
        simp [Function.iterate_succ_apply']
      rw [h_step, ih]
      -- Rearrange and use distributivity.
      have hcoeff : (((n + 1 : ℕ) : ℝ≥0) + 1) = ((n + 2 : ℕ) : ℝ≥0) := by
        have hn : (n + 1 + 1 : ℕ) = n + 2 := by omega
        calc
          ((n + 1 : ℕ) : ℝ≥0) + 1 = ((n + 1 + 1 : ℕ) : ℝ≥0) := by
            simp [Nat.cast_add]
          _ = ((n + 2 : ℕ) : ℝ≥0) := by
            simp [hn]
      calc
        x + ((n + 1 : ℕ) : ℝ≥0) * x
            = ((n + 1 : ℕ) : ℝ≥0) * x + x := by
                simp [add_comm]
        _ = (((n + 1 : ℕ) : ℝ≥0) + 1) * x := by
                simp [add_mul, one_mul]
        _ = ((n + 2 : ℕ) : ℝ≥0) * x := by
                exact congrArg (fun a : ℝ≥0 => a * x) hcoeff

-- A concrete Knuth–Skilling algebra: `ℝ≥0` with `op := (· + ·)` and `ident := 0`.
-- We keep this `noncomputable` because the underlying `LinearOrder` on `ℝ` is noncomputable.
noncomputable local instance : KnuthSkillingAlgebra ℝ≥0 where
  op := (· + ·)
  ident := 0
  op_assoc := by intro x y z; simp [add_assoc]
  op_ident_right := by intro x; simp
  op_ident_left := by intro x; simp
  op_strictMono_left := by
    intro y x₁ x₂ hx
    exact add_lt_add_right hx y
  op_strictMono_right := by
    intro x y₁ y₂ hy
    exact add_lt_add_left hy x
  ident_le := by intro x; exact bot_le

-- Singleton atom family with atom `1`.
noncomputable def F1 : AtomFamily ℝ≥0 1 :=
  singletonAtomFamily (α := ℝ≥0) 1 (by
    -- `ident = 0` in this local instance.
    simp [KnuthSkillingAlgebraBase.ident])

private noncomputable def i0 : Fin 1 := ⟨0, by decide⟩

private lemma multi1_eq_const (t : Multi 1) : t = fun _ : Fin 1 => t i0 := by
  funext i
  simpa [i0] using congrArg t (Fin.eq_zero i)

private lemma iterate_op_add_eq_mul (x : ℝ≥0) : ∀ n : ℕ, iterate_op x n = (n : ℝ≥0) * x
  | 0 => by
      simp [iterate_op, KnuthSkillingAlgebraBase.ident]
  | n + 1 => by
      -- `iterate_op x (n+1) = x + iterate_op x n` and `((n+1):ℝ≥0)*x = n*x + x`.
      have ih := iterate_op_add_eq_mul x n
      -- Work in the semiring structure of `ℝ≥0`.
      calc
        iterate_op x (n + 1) = x + iterate_op x n := by
          simp [iterate_op, KnuthSkillingAlgebraBase.op]
        _ = x + (n : ℝ≥0) * x := by simp [ih]
        _ = (n : ℝ≥0) * x + x := by
              simp [add_comm]
        _ = ((n : ℝ≥0) + 1) * x := by
              simp [add_mul, one_mul]
        _ = ((n + 1 : ℕ) : ℝ≥0) * x := by
              simp [Nat.cast_add, Nat.cast_one]

private lemma iterate_op_one_eq_natCast (n : ℕ) : iterate_op (1 : ℝ≥0) n = (n : ℝ≥0) := by
  -- `iterate_op 1 n = (n : ℝ≥0) * 1 = n`.
  simp [iterate_op_add_eq_mul]

private lemma mu_F1 (t : Multi 1) : mu F1 t = (t i0 : ℝ≥0) := by
  -- Reduce to the constant multi-index case.
  have ht : t = fun _ : Fin 1 => t i0 := multi1_eq_const t
  have h_ident_lt_one : (KnuthSkillingAlgebraBase.ident : ℝ≥0) < 1 := by
    simp [KnuthSkillingAlgebraBase.ident]
  calc
    mu F1 t = mu F1 (fun _ : Fin 1 => t i0) := by
      simpa using congrArg (fun r : Multi 1 => mu F1 r) ht
    _ = iterate_op (1 : ℝ≥0) (t i0) := by
          simpa [F1] using (mu_singleton (α := ℝ≥0) (a := (1 : ℝ≥0)) (ha := h_ident_lt_one) (n := t i0))
    _ = (t i0 : ℝ≥0) := by
          simp [iterate_op_one_eq_natCast]

-- A simple representation on the μ-grid: `Θ_grid(x) = (x : ℝ)`.
noncomputable def R1 : MultiGridRep F1 where
  Θ_grid := fun x => (x.1 : ℝ)
  strictMono := by
    intro x y hxy
    exact_mod_cast hxy
  add := by
    intro r s
    -- On k=1, μ is the single coordinate, so additivity is just `Nat.cast_add`.
    have hμr : mu F1 r = (r i0 : ℝ≥0) := mu_F1 r
    have hμs : mu F1 s = (s i0 : ℝ≥0) := mu_F1 s
    have hμrs : mu F1 (fun i => r i + s i) = ((r i0 + s i0 : ℕ) : ℝ≥0) := by
      -- `mu_F1` reads off the single coordinate.
      simpa using (mu_F1 (fun i => r i + s i))
    -- Unfold `Θ_grid` (it's just coercion to `ℝ`) and finish.
    change ((mu F1 (fun i => r i + s i) : ℝ≥0) : ℝ) =
        ((mu F1 r : ℝ≥0) : ℝ) + ((mu F1 s : ℝ≥0) : ℝ)
    -- Rewrite μ-values and simplify.
    simp [hμr, hμs, hμrs, Nat.cast_add]
  ident_eq_zero := by
    -- ident = 0 and `Θ_grid` is coercion to ℝ.
    simp [KnuthSkillingAlgebraBase.ident]

-- The new atom `d = √5` (positive, and irrational over the old singleton grid).
noncomputable def d : ℝ≥0 := ⟨Real.sqrt 5, by positivity⟩

lemma d_pos : (KnuthSkillingAlgebraBase.ident : ℝ≥0) < d := by
  have : (0 : ℝ) < Real.sqrt 5 := by
    have : (0 : ℝ) < (5 : ℝ) := by norm_num
    exact Real.sqrt_pos.2 this
  exact_mod_cast this

lemma B_empty_for_F1_d : ∀ r u, 0 < u → r ∉ extensionSetB F1 d u := by
  intro r u hu hrB
  -- Compute μ(F1,r) = (r 0) and iterate_op d u = u * d.
  have hB : mu F1 r = iterate_op d u := by simpa [extensionSetB] using hrB
  have hμ : mu F1 r = (r i0 : ℝ≥0) := mu_F1 r
  have h_iter : iterate_op d u = (u : ℝ≥0) * d := iterate_op_add_eq_mul d u
  have hEq_nn : (r i0 : ℝ≥0) = (u : ℝ≥0) * d := by
    simpa [hμ, h_iter] using hB
  have hEq : (r i0 : ℝ) = (Real.sqrt 5) * (u : ℕ) := by
    have : ((r i0 : ℝ≥0) : ℝ) = (((u : ℝ≥0) * d : ℝ≥0) : ℝ) :=
      congrArg (fun x : ℝ≥0 => (x : ℝ)) hEq_nn
    -- Coe d = √5, and (u:ℝ) = (u:ℕ) as a real.
    simpa [d, mul_assoc, mul_comm, mul_left_comm] using this
  have hirr : Irrational (Real.sqrt 5) := by
    simpa using (Nat.Prime.irrational_sqrt (p := 5) (by norm_num))
  have hirr_mul : Irrational (Real.sqrt 5 * (u : ℕ)) :=
    hirr.mul_natCast (m := u) (Nat.ne_of_gt hu)
  -- An irrational cannot equal an integer.
  have : (Real.sqrt 5) * (u : ℕ) = ((r i0 : ℤ) : ℝ) := by
    -- `(r i0 : ℤ)` and `(r i0 : ℕ)` cast to the same real.
    simpa using (show (Real.sqrt 5) * (u : ℕ) = (r i0 : ℝ) from hEq.symm)
  exact (hirr_mul.ne_int (r i0 : ℤ)) this

theorem not_ZQuantized_chooseδ_in_B_empty_example :
    ¬ ZQuantized F1 R1 (chooseδ (α := ℝ≥0) (hk := (le_rfl : (1 : ℕ) ≥ 1)) R1 d d_pos) := by
  classical
  set δ : ℝ :=
    chooseδ (α := ℝ≥0) (hk := (le_rfl : (1 : ℕ) ≥ 1)) R1 d d_pos with hδ

  -- First, `δ ≥ 2` because `2 ∈ A(1)` and `δ` is the supremum of A-statistics in the B-empty branch.
  have hB_false : ¬ ∃ r u, 0 < u ∧ r ∈ extensionSetB F1 d u := by
    intro hB
    rcases hB with ⟨r, u, hu, hrB⟩
    exact B_empty_for_F1_d r u hu hrB

  have h2_lt_d : (2 : ℝ) < (d : ℝ) := by
    have : ((2 : ℝ) ^ 2) < (5 : ℝ) := by norm_num
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))).2 (by simpa using this)

  let r2 : Multi 1 := fun _ => 2
  have hr2A : r2 ∈ extensionSetA F1 d 1 := by
    have hμ : mu F1 r2 = (2 : ℝ≥0) := by
      simpa [r2] using (mu_F1 r2)
    -- `iterate_op d 1 = d`, so this is just `2 < d`.
    have : (2 : ℝ≥0) < d := by exact_mod_cast h2_lt_d
    simpa [extensionSetA, hμ, iterate_op_one] using this

  -- The A-statistics set used by `B_empty_delta`.
  let AStats : Set ℝ :=
    {s : ℝ |
      ∃ r u, 0 < u ∧ r ∈ extensionSetA F1 d u ∧
        s = R1.Θ_grid ⟨mu F1 r, mu_mem_kGrid F1 r⟩ / u}

  have hAStats_bdd : BddAbove AStats := by
    refine ⟨(d : ℝ), ?_⟩
    intro s hs
    rcases hs with ⟨r, u, hu, hrA, rfl⟩
    have huℝ : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
    have hμlt : ((mu F1 r : ℝ≥0) : ℝ) < ((iterate_op d u : ℝ≥0) : ℝ) := by
      exact_mod_cast hrA
    have h_iter : ((iterate_op d u : ℝ≥0) : ℝ) = (u : ℝ) * (d : ℝ) := by
      have : iterate_op d u = (u : ℝ≥0) * d := iterate_op_add_eq_mul d u
      simp [this]
    have hμlt' : ((mu F1 r : ℝ≥0) : ℝ) < (u : ℝ) * (d : ℝ) := by
      simpa [h_iter] using hμlt
    have : ((mu F1 r : ℝ≥0) : ℝ) / (u : ℝ) < (d : ℝ) := by
      have hμlt'' : ((mu F1 r : ℝ≥0) : ℝ) < (d : ℝ) * (u : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hμlt'
      have := (div_lt_iff₀ huℝ).2 hμlt''
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    exact le_of_lt this

  have h2_mem : (2 : ℝ) ∈ AStats := by
    refine ⟨r2, 1, Nat.one_pos, hr2A, ?_⟩
    have hμ : mu F1 r2 = (2 : ℝ≥0) := by
      simpa [r2] using (mu_F1 r2)
    have hθ : R1.Θ_grid ⟨mu F1 r2, mu_mem_kGrid F1 r2⟩ = (2 : ℝ) := by
      simp [R1, hμ]
    simp [hθ]

  have h2_le : (2 : ℝ) ≤ δ := by
    -- Unfold `chooseδ` and go to the B-empty branch.
    rw [hδ]
    unfold chooseδ
    by_cases hB : ∃ r u, 0 < u ∧ r ∈ extensionSetB F1 d u
    · exact (hB_false hB).elim
    · -- This branch is `B_empty_delta = sSup AStats`.
      simp [hB, B_empty_delta]
      exact le_csSup hAStats_bdd h2_mem

  -- Now `ZQuantized` would force Θ(1) to be an integer multiple of δ ≥ 2; impossible.
  intro hZQ
  let r1 : Multi 1 := fun _ => 1
  rcases hZQ r1 with ⟨m, hm⟩
  have hμ1 : mu F1 r1 = (1 : ℝ≥0) := by
    simpa [r1] using (mu_F1 r1)
  have hθ1 : R1.Θ_grid ⟨mu F1 r1, mu_mem_kGrid F1 r1⟩ = 1 := by
    simp [R1, hμ1]
  have hδ_ge : (2 : ℝ) ≤ δ := h2_le
  have hδ_pos : 0 < δ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hδ_ge
  have hm' : (1 : ℝ) = (m : ℝ) * δ := by simpa [hθ1, hδ] using hm
  -- Take absolute values: `1 = |m| * δ ≥ δ ≥ 2`, contradiction.
  have hm_ne : m ≠ 0 := by
    intro hm0
    have : (1 : ℝ) = 0 := by
      have hm'' := hm'
      simp [hm0] at hm''
    linarith
  have hm_abs : (1 : ℝ) ≤ |(m : ℝ)| := by
    have hm_abs_int : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
    have hm_abs_real : (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast hm_abs_int
    have hcast : ((|m| : ℤ) : ℝ) = |(m : ℝ)| := by
      simp [Int.cast_abs]
    simpa [hcast] using hm_abs_real
  have hδ_le : δ ≤ |(m : ℝ)| * δ := by
    have : (1 : ℝ) ≤ |(m : ℝ)| := hm_abs
    simpa [one_mul] using (mul_le_mul_of_nonneg_right this (le_of_lt hδ_pos))
  have habs_eq : (1 : ℝ) = |(m : ℝ)| * δ := by
    have := congrArg abs hm'
    simpa [abs_mul, abs_of_pos hδ_pos] using this
  have : δ ≤ 1 := by
    simpa [habs_eq] using hδ_le
  linarith [hδ_ge, this]

/-- There exists a (B-empty) atom-family extension in the additive model where
`ZQuantized F R (chooseδ hk R d hd)` fails. This blocks treating `ZQuantized` with
`δ := chooseδ …` as a general extension invariant. -/
theorem exists_B_empty_chooseδ_not_ZQuantized :
    ∃ (F : AtomFamily ℝ≥0 1) (R : MultiGridRep F) (d : ℝ≥0) (hd : ident < d),
      (¬ ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u) ∧
      ¬ ZQuantized F R (chooseδ (α := ℝ≥0) (hk := (le_rfl : (1 : ℕ) ≥ 1)) R d hd) := by
  refine ⟨F1, R1, d, d_pos, ?_, ?_⟩
  · intro hB
    rcases hB with ⟨r, u, hu, hrB⟩
    exact B_empty_for_F1_d r u hu hrB
  · simpa using not_ZQuantized_chooseδ_in_B_empty_example

end

end ZQuantizedBEmpty

end KnuthSkilling.Additive.Counterexamples
