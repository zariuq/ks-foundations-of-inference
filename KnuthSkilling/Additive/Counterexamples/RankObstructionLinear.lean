import KnuthSkilling.Core.Algebra

namespace KnuthSkilling.Additive.Counterexamples

open Classical KnuthSkillingAlgebra KnuthSkillingAlgebraBase

/-!
# A reusable obstruction to `KSSeparation` (rank into an ordered additive monoid)

`RankObstruction.lean` records a common reason `KSSeparation` fails in noncommutative models:
there is a “rank” coordinate that scales under `iterate_op`, and distinct elements can share the
same rank. Then the `KSSeparation.separation` sandwich forces an impossible strict inequality.

This variant packages the same argument with a more general rank codomain `β`.  We avoid relying
on any bundled “LinearOrdered…Monoid” typeclasses (which have been removed upstream in Mathlib);
instead we require exactly what the proof uses:

- an additive monoid structure on `β` with a preorder, and
- strict monotonicity of left addition (`AddLeftStrictMono β`) so `nsmul` is strictly monotone for
  positive elements.

This is still not a full impossibility theorem for K&S: it only rules out models admitting such a
rank structure.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

structure RankDataLinear (β : Type*) [AddCommMonoid β] [PartialOrder β] [AddLeftStrictMono β] where
  rk : α → β
  rk_le_of_le : ∀ {x y : α}, x ≤ y → rk x ≤ rk y
  rk_iterate : ∀ x n, rk (iterate_op x n) = n • rk x
  rk_pos_of_ident_lt : ∀ {x : α}, ident < x → 0 < rk x

theorem not_KSSeparation_of_same_rank_linear
    {β : Type*} [AddCommMonoid β] [PartialOrder β] [AddLeftStrictMono β]
    (R : RankDataLinear (α := α) β)
    (hChain :
      ∃ a x y : α,
        ident < a ∧ ident < x ∧ ident < y ∧ a < x ∧ x < y ∧
        R.rk a = R.rk x ∧ R.rk x = R.rk y) :
    ¬ KSSeparation α := by
  intro hSep
  rcases hChain with ⟨a, x, y, ha, hx, hy, hax, hxy, haxr, hxyr⟩
  obtain ⟨n, m, hm, hlo, hhi⟩ := hSep.separation ha hx hy hxy
  have hlo' := R.rk_le_of_le hlo.le
  have hhi' := R.rk_le_of_le hhi
  rw [R.rk_iterate, R.rk_iterate, ← haxr] at hlo'
  rw [R.rk_iterate, R.rk_iterate, ← hxyr, ← haxr] at hhi'
  have heq : m = n := by
    apply (nsmul_left_strictMono (R.rk_pos_of_ident_lt ha)).injective
    exact le_antisymm hlo' hhi'
  subst n
  exact (not_lt_of_ge (KnuthSkillingAlgebra.iterate_op_strictMono_base m hm a x hax).le) hlo

/-!
## Corollary: `KSSeparation` forbids rank-collisions along a chain

If a candidate model admits a monotone additive “rank” into an ordered additive monoid `β`, then
any triple `a < x < y` of positive elements sharing the same rank would contradict
`KSSeparation.separation`.

This is a convenient “obstruction checklist” lemma when hunting for noncommutative models:
many natural noncommutative constructions (shortlex words, semidirect products, …) have such a
rank coordinate, and this corollary explains why they systematically fail `KSSeparation`.
-/
theorem KSSeparation.no_same_rank_chain_linear
    {β : Type*} [AddCommMonoid β] [PartialOrder β] [AddLeftStrictMono β]
    [KSSeparation α] (R : RankDataLinear (α := α) β) :
    ¬ (∃ a x y : α,
        ident < a ∧ ident < x ∧ ident < y ∧ a < x ∧ x < y ∧
        R.rk a = R.rk x ∧ R.rk x = R.rk y) := by
  exact fun h => not_KSSeparation_of_same_rank_linear R h inferInstance

end KnuthSkilling.Additive.Counterexamples
