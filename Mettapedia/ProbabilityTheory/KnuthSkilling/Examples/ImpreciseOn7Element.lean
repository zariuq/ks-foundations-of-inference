import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.NonModularDistributive

/-!
# Cautionary Example: 7-Element Lattice vs Boolean Event Modeling

This file accompanies the 7-element distributive lattice from
`Counterexamples/NonModularDistributive.lean`.  It is kept as a *modeling* example:
it explains why this lattice should not be used as evidence that ``imprecise probability is
mathematically required.''

## Key Point

The ideal-lattice operations in the 7-element example are **not** Boolean conjunction/disjunction
of independent feature-variables.  If you want an event semantics on four features
`{a,b,c,d}` with prerequisites (e.g. `c` and `d` require `a ∧ b`), the natural event space is a
Boolean algebra, and prerequisites are represented by *constraints* (certain atoms have probability
zero).  In that Boolean setting, standard probability works as usual.

This file contrasts:
1) a Boolean event model (6 atoms, excluding the optional ``cores-only'' state), and
2) a 7-state model which includes that additional state and illustrates how different
   interpretations of meet/join lead to different algebraic identities.

## Takeaway

This is a useful cautionary example about **semantics** (what the algebraic operations mean),
not a canonical example motivating imprecise probability.
Earlier drafts of this file mistakenly framed it as evidence for imprecise probability; the correct
lesson is about modeling choices (Boolean events vs.\ ideal-lattice operations).

## References

- NonModularDistributive.lean - the original counterexample
- This analysis clarifies when Boolean probability suffices
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.ImpreciseOn7Element

open Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.IdealLattice
open Finset BigOperators

/-! ## The 7 Possible States

With prerequisites "c requires a∧b" and "d requires a∧b", only 7 states are possible:
-/

/-- The 7 possible states in the software configuration model -/
inductive ConfigState
  | nothing    -- ¬a ∧ ¬b ∧ ¬c ∧ ¬d
  | justA      -- a ∧ ¬b ∧ ¬c ∧ ¬d
  | justB      -- ¬a ∧ b ∧ ¬c ∧ ¬d
  | coresOnly  -- a ∧ b ∧ ¬c ∧ ¬d  (optional intermediate state)
  | analytics  -- a ∧ b ∧ c ∧ ¬d
  | alerts     -- a ∧ b ∧ ¬c ∧ d
  | full       -- a ∧ b ∧ c ∧ d
  deriving DecidableEq, Fintype

namespace ConfigState

/-! ## Approach 1: Boolean Probability (6 atoms)

If we model the system such that "cores-only" never happens (you always
deploy at least one advanced feature once cores are installed), then
we have 6 atoms and standard probability works perfectly.
-/

/-- A probability distribution on 6 states (excluding cores-only) -/
structure BooleanProb where
  p_nothing : ℝ
  p_justA : ℝ
  p_justB : ℝ
  p_analytics : ℝ
  p_alerts : ℝ
  p_full : ℝ
  all_nonneg : 0 ≤ p_nothing ∧ 0 ≤ p_justA ∧ 0 ≤ p_justB ∧
               0 ≤ p_analytics ∧ 0 ≤ p_alerts ∧ 0 ≤ p_full
  sum_one : p_nothing + p_justA + p_justB + p_analytics + p_alerts + p_full = 1

namespace BooleanProb

variable (P : BooleanProb)

/-- P(a) = probability that feature a is enabled -/
noncomputable def prob_a : ℝ :=
  P.p_justA + P.p_analytics + P.p_alerts + P.p_full

/-- P(b) = probability that feature b is enabled -/
noncomputable def prob_b : ℝ :=
  P.p_justB + P.p_analytics + P.p_alerts + P.p_full

/-- P(a ∧ b) = probability both cores enabled -/
noncomputable def prob_ab : ℝ :=
  P.p_analytics + P.p_alerts + P.p_full

/-- P(a ∧ b ∧ c) = probability cores + analytics -/
noncomputable def prob_abc : ℝ :=
  P.p_analytics + P.p_full

/-- P(a ∧ b ∧ d) = probability cores + alerts -/
noncomputable def prob_abd : ℝ :=
  P.p_alerts + P.p_full

/-- P(a ∧ b ∧ c ∧ d) = probability everything -/
noncomputable def prob_abcd : ℝ :=
  P.p_full

/-- P(a ∧ b ∧ (c ∨ d)) = probability cores + at least one advanced -/
noncomputable def prob_ab_cor_d : ℝ :=
  P.p_analytics + P.p_alerts + P.p_full

/-- **The modular law HOLDS in the Boolean model!**

P(abc ∨ abd) + P(abc ∧ abd) = P(abc) + P(abd)

where ∨ and ∧ are Boolean operations. -/
theorem modular_law_holds :
    P.prob_ab_cor_d + P.prob_abcd = P.prob_abc + P.prob_abd := by
  simp only [prob_ab_cor_d, prob_abcd, prob_abc, prob_abd]
  ring

/-- Note: In the Boolean model, abc ∧ abd = abcd (not ab!)

This is different from the 7-element lattice where abc ∧ abd = ab.
The semantics are subtly different. -/
theorem boolean_meet_is_abcd :
    P.prob_abcd = P.p_full := rfl

end BooleanProb

/-! ## Approach 2: Full 7-State Model (allows cores-only)

If we allow the "cores-only" state, we need to be more careful about
what the lattice operations mean.
-/

/-- A probability distribution on all 7 states -/
structure FullProb where
  p : ConfigState → ℝ
  nonneg : ∀ s, 0 ≤ p s
  sum_one : ∑ s : ConfigState, p s = 1

namespace FullProb

variable (P : FullProb)

/-- P(a is enabled) -/
noncomputable def prob_a : ℝ :=
  P.p justA + P.p coresOnly + P.p analytics + P.p alerts + P.p full

/-- P(b is enabled) -/
noncomputable def prob_b : ℝ :=
  P.p justB + P.p coresOnly + P.p analytics + P.p alerts + P.p full

/-- P(a ∧ b) in Boolean sense -/
noncomputable def prob_ab_bool : ℝ :=
  P.p coresOnly + P.p analytics + P.p alerts + P.p full

/-- P(abc) = P(a ∧ b ∧ c) in Boolean sense -/
noncomputable def prob_abc_bool : ℝ :=
  P.p analytics + P.p full

/-- P(abd) = P(a ∧ b ∧ d) in Boolean sense -/
noncomputable def prob_abd_bool : ℝ :=
  P.p alerts + P.p full

/-- P(abcd) = P(a ∧ b ∧ c ∧ d) in Boolean sense -/
noncomputable def prob_abcd_bool : ℝ :=
  P.p full

/-- P(a ∧ b ∧ (c ∨ d)) -/
noncomputable def prob_ab_cor_d : ℝ :=
  P.p analytics + P.p alerts + P.p full

/-- **Boolean modular law still holds!**

Even with 7 states, if we use Boolean ∧ and ∨, modularity holds. -/
theorem boolean_modular_holds :
    P.prob_ab_cor_d + P.prob_abcd_bool = P.prob_abc_bool + P.prob_abd_bool := by
  simp only [prob_ab_cor_d, prob_abcd_bool, prob_abc_bool, prob_abd_bool]
  ring

/-- **Lattice modular law fails when p(coresOnly) > 0**

If we interpret the 7-element lattice operations:
- abc ∨ᴸ abd = top (in lattice)
- abc ∧ᴸ abd = ab (in lattice)

And use prob_ab_bool for P(ab), we get a mismatch. -/
theorem lattice_modular_fails_iff (h : P.p coresOnly > 0) :
    P.prob_abcd_bool + P.prob_ab_bool ≠ P.prob_abc_bool + P.prob_abd_bool := by
  simp only [prob_abcd_bool, prob_ab_bool, prob_abc_bool, prob_abd_bool]
  -- LHS = p_full + (p_coresOnly + p_analytics + p_alerts + p_full)
  -- RHS = (p_analytics + p_full) + (p_alerts + p_full)
  -- Difference = p_coresOnly ≠ 0
  intro heq
  have : P.p coresOnly = 0 := by linarith
  linarith

/-- **Key insight**: The "failure" comes from using LATTICE operations
    where BOOLEAN operations should be used.

    If abc ∧ abd means "Boolean AND" (= abcd), modular law holds.
    If abc ∧ abd means "lattice meet" (= ab), and p(coresOnly) > 0, it fails.

    This is a MODELING choice, not a fundamental limitation! -/
theorem modeling_choice_summary :
    -- Boolean interpretation always works
    P.prob_ab_cor_d + P.prob_abcd_bool = P.prob_abc_bool + P.prob_abd_bool ∧
    -- Lattice interpretation fails iff coresOnly has positive probability
    (P.p coresOnly > 0 ↔
      P.prob_abcd_bool + P.prob_ab_bool ≠ P.prob_abc_bool + P.prob_abd_bool) := by
  constructor
  · exact boolean_modular_holds P
  · constructor
    · exact lattice_modular_fails_iff P
    · intro hne
      by_contra h
      push_neg at h
      simp only [prob_abcd_bool, prob_ab_bool, prob_abc_bool, prob_abd_bool] at hne
      have heq : P.p coresOnly = 0 := le_antisymm h (P.nonneg coresOnly)
      simp only [heq] at hne
      apply hne
      ring

end FullProb

/-! ## Concrete Example: Matching the Original Valuation

The original counterexample had m(ab) = 3, m(abc) = 10, m(abd) = 20, m(top) = 30.

Those numbers are valuations of lattice elements, not probabilities of Boolean events.
If one *insists* on reading `abc`, `abd`, `abcd` as Boolean events in the 6-atom model
(excluding \texttt{coresOnly}), then modularity forces:
\[
P(ab) = P(abc) + P(abd) - P(abcd).
\]
So choosing $P(abc)=10/30$, $P(abd)=20/30$, and $P(abcd)=3/30$ forces $P(ab)=27/30$.
This is one concrete way to see that the lattice values do not directly define Boolean
probabilities on the intended feature space.
-/

/-- Example: A valid 6-state Boolean probability (no cores-only) -/
noncomputable def exampleBooleanProb : BooleanProb where
  p_nothing := 0
  p_justA := 1/30
  p_justB := 2/30
  p_analytics := 7/30  -- abc contribution beyond ab
  p_alerts := 17/30    -- abd contribution beyond ab
  p_full := 3/30       -- the "interaction" part
  all_nonneg := by constructor <;> norm_num
  sum_one := by norm_num

/-- With this distribution:
- P(ab) = 7/30 + 17/30 + 3/30 = 27/30 = 0.9
- P(abc) = 7/30 + 3/30 = 10/30
- P(abd) = 17/30 + 3/30 = 20/30
- P(abcd) = 3/30

And the modular law holds:
P(abc ∨ abd) + P(abc ∧ abd) = P(abc) + P(abd)
(27/30) + (3/30) = (10/30) + (20/30)
30/30 = 30/30 ✓
-/
theorem example_modular_check :
    exampleBooleanProb.prob_ab_cor_d + exampleBooleanProb.prob_abcd =
    exampleBooleanProb.prob_abc + exampleBooleanProb.prob_abd := by
  simp only [BooleanProb.prob_ab_cor_d, BooleanProb.prob_abcd,
             BooleanProb.prob_abc, BooleanProb.prob_abd, exampleBooleanProb]
  norm_num

end ConfigState

/-! ## Summary

| Aspect | Boolean Prob (6 states) | 7-State with Lattice Ops |
|--------|------------------------|--------------------------|
| Prerequisites | ✓ Captured by zero atoms | ✓ Captured by zero atoms |
| Cores-only state | Excluded (p=0) | Allowed (p>0 possible) |
| Modular law | ✓ Always holds | ✗ Fails if p(coresOnly)>0 |
| Imprecise needed? | No | Only if insisting on lattice ops |

**Conclusion**: This example is primarily about semantics.  With an appropriate Boolean event model:
- Set impossible configurations to probability 0
- If cores-only state doesn't occur, use 6-state model
- Standard probability theory handles everything

The "modular law failure" in the original example came from mixing
lattice operations (∧ᴸ, ∨ᴸ) with probability expectations that
assume Boolean operations. This is a modeling mismatch, not a
fundamental limitation of probability theory.

In other settings, imprecise probability can still be mathematically and practically appropriate
(e.g. when constraints do not determine a unique distribution).  The point here is only that the
7-element lattice example, by itself, is primarily a warning about semantics rather than a
motivation for imprecision.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.ImpreciseOn7Element
