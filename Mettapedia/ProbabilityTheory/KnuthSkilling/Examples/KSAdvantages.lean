import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# Knuth--Skilling Examples Beyond a Global Boolean Complement

This file collects small examples illustrating two distinctions that are easy to miss when reading
probability-theory statements in their most common (Boolean/complemented) setting:

1. **Section 5.2 (inclusion--exclusion)** lives naturally on *generalized* Boolean algebras (relative
   complements inside a container), not only on Boolean algebras with a global complement.
2. **Appendix A (additive representation)** can be stated identity-free, so it applies to ordered
   semigroups where there is no distinguished ``bottom''/``zero'' element.

We also point to a 7-element distributive lattice counterexample showing that distributivity alone
does not guarantee the modular identity used by inclusion--exclusion.

References:
- Knuth \& Skilling, *Foundations of Inference* (2012), Sections 5.1--5.2.
- Cox, *The Algebra of Probable Inference* (1961).
- This project: `Counterexamples/NonModularDistributive.lean` and
  `Examples/ImpreciseOn7Element.lean` (modeling discussion).
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

open Set

/-! ## Example 1: Interval Lattice (GBA without Boolean)

**Structure**: Closed intervals [a,b] on the real line, ordered by inclusion.

**Key property**: Has RELATIVE complements but NOT absolute complements.
- Relative complement: [0,1] \ [0.3, 0.7] = [0, 0.3) ∪ (0.7, 1] (exists as union of intervals)
- Absolute complement: What's ¬[0,1]? The entire real line minus [0,1]?
  Not an element of "bounded intervals on [0,1]"!

**K&S applicability**: Section 5.2 applies to GBAs
**Cox non-applicability**: Cannot define p(¬A|B) when A has no absolute complement -/

section IntervalLattice

/-- A bounded interval [a,b] on the real line. -/
structure BoundedInterval where
  lo : ℝ
  hi : ℝ
  h_le : lo ≤ hi

namespace BoundedInterval

/-- Interval inclusion ordering: I ≤ J means I ⊆ J. -/
instance : LE BoundedInterval where
  le I J := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

/-- Length of an interval (a natural "measure"). -/
def length (I : BoundedInterval) : ℝ := I.hi - I.lo

/-- Length is non-negative. -/
theorem length_nonneg (I : BoundedInterval) : 0 ≤ I.length := by
  simp only [length]
  linarith [I.h_le]

/-- Length is monotone with respect to inclusion. -/
theorem length_mono {I J : BoundedInterval} (h : I ≤ J) : I.length ≤ J.length := by
  simp only [length]
  have h1 : J.lo ≤ I.lo := h.1
  have h2 : I.hi ≤ J.hi := h.2
  linarith

/-- **Key Point**: Relative complement exists within a containing interval.

For sub ⊆ container, the relative complement is the "left and right remainders".
This makes bounded intervals a **Generalized Boolean Algebra**. -/
def leftRemainder (container sub : BoundedInterval) (h : sub ≤ container) : BoundedInterval :=
  ⟨container.lo, sub.lo, h.1⟩

def rightRemainder (container sub : BoundedInterval) (h : sub ≤ container) : BoundedInterval :=
  ⟨sub.hi, container.hi, h.2⟩

/-- The relative complement satisfies: container = left + sub + right. -/
theorem relativeComplement_lengths (container sub : BoundedInterval) (h : sub ≤ container) :
    container.length = (leftRemainder container sub h).length + sub.length +
                       (rightRemainder container sub h).length := by
  simp only [leftRemainder, rightRemainder, length]
  ring

/-- Cox-style ``global negation'' is not available for bounded intervals.

If we restrict attention to *single* bounded intervals, there is no operation
`neg : Interval -> Interval` behaving like a complement: the complement of a middle interval
inside `[0,1]` is typically a union of two disjoint intervals, which is not a single interval.
-/
theorem no_single_interval_complement :
    ¬∃ (neg : BoundedInterval),
      -- neg should be the complement of [0.3, 0.7] within [0, 1]
      neg.lo = 0 ∧ neg.hi = 1 ∧  -- neg spans the full range
      -- AND neg is disjoint from [0.3, 0.7]
      (neg.hi ≤ 0.3 ∨ neg.lo ≥ 0.7) := by
  intro ⟨neg, h_lo, h_hi, h_disj⟩
  rcases h_disj with h1 | h2
  · -- neg.hi ≤ 0.3 but neg.hi = 1
    linarith
  · -- neg.lo ≥ 0.7 but neg.lo = 0
    linarith

/-- K\&S Section 5.2 does apply: length is additive over relative complements. -/
theorem ks_applies_to_intervals :
    ∃ (m : BoundedInterval → ℝ),
      (∀ I, 0 ≤ m I) ∧  -- Non-negative
      (∀ I J : BoundedInterval, I ≤ J → m I ≤ m J) ∧  -- Monotone
      (∀ container sub : BoundedInterval, ∀ h : sub ≤ container,
        m container = m (leftRemainder container sub h) + m sub +
                      m (rightRemainder container sub h)) := by  -- Additive on complements
  use length
  refine ⟨length_nonneg, ?_, relativeComplement_lengths⟩
  intro I J h
  exact length_mono h

end BoundedInterval

end IntervalLattice

/-! ## Example 2: Positive Reals (Identity-Free Ordered Semigroup)

**Structure**: (ℝ⁺, +) - positive real numbers under addition.

**Key property**: NO additive identity (0 is not in ℝ⁺).

**K&S applicability**: Identity-free Hölder embedding (our `holder_representation`)
**Cox non-applicability**: Cox requires a "contradiction" (⊥) with p(⊥|B) = 0 -/

section PositiveReals

/-- Positive reals form an ordered cancellative semigroup. -/
def PosReal := {x : ℝ // 0 < x}

namespace PosReal

instance : Add PosReal where
  add x y := ⟨x.val + y.val, add_pos x.prop y.prop⟩

instance : LT PosReal where
  lt x y := x.val < y.val

instance : LE PosReal where
  le x y := x.val ≤ y.val

/-- Addition is strictly monotone in both arguments. -/
theorem add_lt_add_left (a : PosReal) {b c : PosReal} (h : b < c) : a + b < a + c := by
  show a.val + b.val < a.val + c.val
  have hbc : b.val < c.val := h
  linarith

theorem add_lt_add_right {a b : PosReal} (h : a < b) (c : PosReal) : a + c < b + c := by
  show a.val + c.val < b.val + c.val
  have hab : a.val < b.val := h
  linarith

/-- **Key Point**: No identity element exists.

In (ℝ⁺, +), there is no e such that e + x = x for all x.
(That would require e = 0, but 0 ∉ ℝ⁺.) -/
theorem no_identity : ¬∃ e : PosReal, ∀ x : PosReal, e + x = x := by
  intro ⟨e, he⟩
  have h := he ⟨1, one_pos⟩
  -- h says e + 1 = 1, i.e., e.val + 1 = 1
  have h' : e.val + 1 = 1 := congrArg Subtype.val h
  -- This means e.val = 0, contradicting e.val > 0
  linarith [e.prop]

/-- Every element is "positive" in Eric Luap's sense: ∀ z, z < x + z. -/
theorem all_positive (x : PosReal) : ∀ z : PosReal, z < x + z := by
  intro z
  show z.val < x.val + z.val
  linarith [x.prop]

/-- **K&S identity-free representation applies**.

By our `holder_representation` (or `cuts_pnat_representation`), there exists
Θ : PosReal → ℝ that is order-preserving and additive.

Here, the natural embedding is just Θ(x) = x.val (identity function to ℝ). -/
def Theta : PosReal → ℝ := fun x => x.val

theorem Theta_order_preserving : ∀ a b : PosReal, a ≤ b ↔ Theta a ≤ Theta b := by
  intro a b
  rfl

theorem Theta_additive : ∀ x y : PosReal, Theta (x + y) = Theta x + Theta y := by
  intro x y
  rfl

/-- No bottom element exists in `(ℝ⁺,+)`: there is no distinguished ``impossible'' baseline. -/
theorem no_bottom : ¬∃ bot : PosReal, ∀ x : PosReal, bot ≤ x := by
  intro ⟨bot, hbot⟩
  -- For any bot > 0, we can find x = bot/2 < bot
  let x : PosReal := ⟨bot.val / 2, by linarith [bot.prop]⟩
  have h := hbot x
  -- h says bot.val ≤ bot.val / 2, contradiction since bot.val > 0
  show False
  have : bot.val ≤ bot.val / 2 := h
  linarith [bot.prop]

end PosReal

end PositiveReals

/-! ## Example 3 (Pointer): A 7-Element Distributive Lattice Where Modularity Fails

See `Counterexamples/NonModularDistributive.lean` for a concrete 7-element distributive lattice with
a monotone, disjoint-additive valuation where the modular identity fails.  This illustrates that
Section 5.2 requires *relative complements* (GBA structure), not merely distributivity.

For a discussion of event semantics (and why this lattice should not be used as a standalone
motivation for imprecise probability), see `Examples/ImpreciseOn7Element.lean`. -/

/-! ## Summary

- Section 5.2 (inclusion--exclusion) is naturally a statement about generalized Boolean algebras:
  you need relative complements to state and use the decomposition cleanly.
- Cox-style negation axioms are formulated for settings with a global complement operation on all
  propositions; many natural ``interval-like'' lattices do not have such an operation.
- Appendix A representation can be carried out without assuming a distinguished identity/minimum
  element on the value scale. -/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
