import KnuthSkilling.Additive.Counterexamples.RankObstructionLinear

namespace KnuthSkilling.Additive.Counterexamples

open Classical KnuthSkillingAlgebra KnuthSkillingAlgebraBase

/-!
# A reusable obstruction to `KSSeparation`

This file factors the core pattern used in `SemidirectNoSeparation.lean`:

If the order admits a “rank” map `rk : α → ℕ` that:
- is monotone w.r.t. `≤`,
- scales under `iterate_op` as `rk (x^n) = n * rk x`,
- is positive above `ident`,

then *any* triple `a < x < y` with the same rank forces `¬ KSSeparation α`.

This is not a full impossibility proof for K&S (it only rules out a broad and common family of
noncommutative constructions that come with such a rank), but it is a clean way to keep search
efforts on track: if a proposed countermodel carries this kind of rank, it cannot satisfy
`KSSeparation`.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

structure RankData (α : Type*) [KnuthSkillingAlgebra α] where
  rk : α → ℕ
  rk_le_of_le : ∀ {x y : α}, x ≤ y → rk x ≤ rk y
  rk_iterate : ∀ x n, rk (iterate_op x n) = n * rk x
  rk_pos_of_ident_lt : ∀ {x : α}, ident < x → 0 < rk x

theorem not_KSSeparation_of_same_rank
    (R : RankData α)
    (hChain :
      ∃ a x y : α,
        ident < a ∧ ident < x ∧ ident < y ∧ a < x ∧ x < y ∧
        R.rk a = R.rk x ∧ R.rk x = R.rk y) :
    ¬ KSSeparation α := by
  let R' : RankDataLinear (α := α) ℕ :=
    { rk := R.rk
      rk_le_of_le := R.rk_le_of_le
      rk_iterate := by simpa only [smul_eq_mul] using R.rk_iterate
      rk_pos_of_ident_lt := R.rk_pos_of_ident_lt }
  exact not_KSSeparation_of_same_rank_linear R' hChain

end KnuthSkilling.Additive.Counterexamples
