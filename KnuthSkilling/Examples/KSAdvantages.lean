import KnuthSkilling.Additive.Representation
import Mathlib.Order.Interval.Set.Basic

/-!
# Decomposition and identity-free examples

Closed intervals have an additive length decomposition into three pieces,
but single nonempty closed intervals do not form a generalized Boolean algebra:
relative complements can be disconnected. The first example proves length laws
only. Finite sets provide a genuine generalized Boolean algebra instead.
Positive reals under addition form an inhabited identity-free KS scale, with
an explicit faithful representation and no identity or least element.
-/

namespace KnuthSkilling.Examples

open Set

section IntervalLattice

structure BoundedInterval where
  lo : ℝ
  hi : ℝ
  h_le : lo ≤ hi

namespace BoundedInterval

instance : LE BoundedInterval where
  le I J := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

def length (I : BoundedInterval) : ℝ := I.hi - I.lo

theorem length_nonneg (I : BoundedInterval) : 0 ≤ I.length := by
  simp only [length]
  linarith [I.h_le]

theorem length_mono {I J : BoundedInterval} (h : I ≤ J) : I.length ≤ J.length := by
  simp only [length]
  have h1 : J.lo ≤ I.lo := h.1
  have h2 : I.hi ≤ J.hi := h.2
  linarith

/-- The two pieces overlap their middle interval only at endpoints. -/
def leftRemainder (container sub : BoundedInterval) (h : sub ≤ container) : BoundedInterval :=
  ⟨container.lo, sub.lo, h.1⟩

def rightRemainder (container sub : BoundedInterval) (h : sub ≤ container) : BoundedInterval :=
  ⟨sub.hi, container.hi, h.2⟩

theorem relativeComplement_lengths (container sub : BoundedInterval) (h : sub ≤ container) :
    container.length = (leftRemainder container sub h).length + sub.length +
                       (rightRemainder container sub h).length := by
  simp only [leftRemainder, rightRemainder, length]
  ring

theorem no_single_interval_complement :
    ¬∃ (neg : BoundedInterval),
      neg.lo = 0 ∧ neg.hi = 1 ∧  -- neg spans the full range
      (neg.hi ≤ 0.3 ∨ neg.lo ≥ 0.7) := by
  intro ⟨neg, h_lo, h_hi, h_disj⟩
  rcases h_disj with h1 | h2
  · -- neg.hi ≤ 0.3 but neg.hi = 1
    linarith
  · -- neg.lo ≥ 0.7 but neg.lo = 0
    linarith

/-- A length decomposition; it does not assert a Boolean algebra of intervals. -/
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

section PositiveReals

def PosReal := {x : ℝ // 0 < x}

namespace PosReal

instance : Add PosReal where
  add x y := ⟨x.val + y.val, add_pos x.prop y.prop⟩

instance : LT PosReal where
  lt x y := x.val < y.val

instance : LE PosReal where
  le x y := x.val ≤ y.val

theorem add_lt_add_left (a : PosReal) {b c : PosReal} (h : b < c) : a + b < a + c := by
  show a.val + b.val < a.val + c.val
  have hbc : b.val < c.val := h
  linarith

theorem add_lt_add_right {a b : PosReal} (h : a < b) (c : PosReal) : a + c < b + c := by
  show a.val + c.val < b.val + c.val
  have hab : a.val < b.val := h
  linarith

theorem no_identity : ¬∃ e : PosReal, ∀ x : PosReal, e + x = x := by
  intro ⟨e, he⟩
  have h := he ⟨1, one_pos⟩
  have h' : e.val + 1 = 1 := congrArg Subtype.val h
  linarith [e.prop]

theorem all_positive (x : PosReal) : ∀ z : PosReal, z < x + z := by
  intro z
  show z.val < x.val + z.val
  linarith [x.prop]

def Theta : PosReal → ℝ := fun x => x.val

theorem Theta_order_preserving : ∀ a b : PosReal, a ≤ b ↔ Theta a ≤ Theta b := by
  intro a b
  rfl

theorem Theta_additive : ∀ x y : PosReal, Theta (x + y) = Theta x + Theta y := by
  intro x y
  rfl

theorem no_bottom : ¬∃ bot : PosReal, ∀ x : PosReal, bot ≤ x := by
  intro ⟨bot, hbot⟩
  let x : PosReal := ⟨bot.val / 2, by linarith [bot.prop]⟩
  have h := hbot x
  show False
  have : bot.val ≤ bot.val / 2 := h
  linarith [bot.prop]

/-- An inhabited identity-free KS profile on the actual positive-addition operation. -/
@[instance_reducible] noncomputable def profile : KnuthSkilling.KSSemigroupBase PosReal where
  toLinearOrder := inferInstanceAs (LinearOrder {x : ℝ // 0 < x})
  op := (· + ·)
  op_assoc x y z := Subtype.ext (add_assoc x.val y.val z.val)
  op_strictMono_left := fun y _ _ h => add_lt_add_right h y
  op_strictMono_right := fun x _ _ h => add_lt_add_left x h

noncomputable def representation : letI := profile;
    KnuthSkilling.Additive.RepresentationResult PosReal := by
  let := profile
  exact ⟨Theta, fun _ _ => Iff.rfl, fun _ _ => rfl⟩

end PosReal

end PositiveReals

end KnuthSkilling.Examples
