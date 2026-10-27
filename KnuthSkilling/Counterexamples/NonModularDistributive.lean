/-
# Disjoint additivity without modularity

The seven ideals of the poset with `a,b < c,d` form a distributive lattice.
The risk weights `0,1,2,3,10,20,30` are monotone and disjoint-additive, but
`m(abc ∨ abd) + m(abc ∧ abd) = 33 ≠ 30 = m(abc) + m(abd)`.
Relative complements would provide the missing decomposition; distributivity
alone does not. These risk weights are not probabilities of Boolean events.
Correlated probability distributions still obey the modular event law.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KnuthSkilling.Counterexamples

inductive IdealLattice
  | bot     -- ∅
  | a       -- {a}
  | b       -- {b}
  | ab      -- {a, b}
  | abc     -- {a, b, c}
  | abd     -- {a, b, d}
  | top     -- {a, b, c, d}
  deriving DecidableEq

namespace IdealLattice

open IdealLattice

def le : IdealLattice → IdealLattice → Prop
  | bot, _      => True
  | a, a        => True
  | a, ab       => True
  | a, abc      => True
  | a, abd      => True
  | a, top      => True
  | b, b        => True
  | b, ab       => True
  | b, abc      => True
  | b, abd      => True
  | b, top      => True
  | ab, ab      => True
  | ab, abc     => True
  | ab, abd     => True
  | ab, top     => True
  | abc, abc    => True
  | abc, top    => True
  | abd, abd    => True
  | abd, top    => True
  | top, top    => True
  | _, _        => False

def sup : IdealLattice → IdealLattice → IdealLattice
  | bot, x      => x
  | x, bot      => x
  | a, a        => a
  | a, b        => ab
  | a, ab       => ab
  | a, abc      => abc
  | a, abd      => abd
  | a, top      => top
  | b, a        => ab
  | b, b        => b
  | b, ab       => ab
  | b, abc      => abc
  | b, abd      => abd
  | b, top      => top
  | ab, a       => ab
  | ab, b       => ab
  | ab, ab      => ab
  | ab, abc     => abc
  | ab, abd     => abd
  | ab, top     => top
  | abc, a      => abc
  | abc, b      => abc
  | abc, ab     => abc
  | abc, abc    => abc
  | abc, abd    => top
  | abc, top    => top
  | abd, a      => abd
  | abd, b      => abd
  | abd, ab     => abd
  | abd, abc    => top
  | abd, abd    => abd
  | abd, top    => top
  | top, _      => top

def inf : IdealLattice → IdealLattice → IdealLattice
  | bot, _      => bot
  | _, bot      => bot
  | a, a        => a
  | a, b        => bot
  | a, ab       => a
  | a, abc      => a
  | a, abd      => a
  | a, top      => a
  | b, a        => bot
  | b, b        => b
  | b, ab       => b
  | b, abc      => b
  | b, abd      => b
  | b, top      => b
  | ab, a       => a
  | ab, b       => b
  | ab, ab      => ab
  | ab, abc     => ab
  | ab, abd     => ab
  | ab, top     => ab
  | abc, a      => a
  | abc, b      => b
  | abc, ab     => ab
  | abc, abc    => abc
  | abc, abd    => ab
  | abc, top    => abc
  | abd, a      => a
  | abd, b      => b
  | abd, ab     => ab
  | abd, abc    => ab
  | abd, abd    => abd
  | abd, top    => abd
  | top, x      => x

instance : PartialOrder IdealLattice where
  le := le
  le_refl := by intro x; cases x <;> simp [le]
  le_trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;> simp [le] at hxy hyz ⊢
  le_antisymm := by
    intro x y hxy hyx
    cases x <;> cases y <;> simp [le] at hxy hyx ⊢

instance : Lattice IdealLattice where
  sup := sup
  inf := inf
  le_sup_left := by
    intro x y
    change IdealLattice.le x (IdealLattice.sup x y)
    cases x <;> cases y <;> simp [IdealLattice.sup, IdealLattice.le]
  le_sup_right := by
    intro x y
    change IdealLattice.le y (IdealLattice.sup x y)
    cases x <;> cases y <;> simp [IdealLattice.sup, IdealLattice.le]
  sup_le := by
    intro x y z hx hy
    change IdealLattice.le (IdealLattice.sup x y) z
    cases x <;> cases y <;> cases z <;>
      simp [IdealLattice.sup, IdealLattice.le] at hx hy ⊢ <;>
      tauto
  inf_le_left := by
    intro x y
    change IdealLattice.le (IdealLattice.inf x y) x
    cases x <;> cases y <;> simp [IdealLattice.inf, IdealLattice.le]
  inf_le_right := by
    intro x y
    change IdealLattice.le (IdealLattice.inf x y) y
    cases x <;> cases y <;> simp [IdealLattice.inf, IdealLattice.le]
  le_inf := by
    intro x y z hx hy
    change IdealLattice.le x (IdealLattice.inf y z)
    cases x <;> cases y <;> cases z <;>
      simp [IdealLattice.inf, IdealLattice.le] at hx hy ⊢ <;>
      tauto

instance : OrderBot IdealLattice where
  bot := bot
  bot_le := by
    intro x
    change IdealLattice.le bot x
    cases x <;> simp [IdealLattice.le]

instance : OrderTop IdealLattice where
  top := top
  le_top := by
    intro x
    change IdealLattice.le x top
    cases x <;> simp [IdealLattice.le]

theorem abc_sup_abd_eq_top : sup abc abd = top := rfl

theorem abc_inf_abd_eq_ab : inf abc abd = ab := rfl

theorem a_inf_b_eq_bot : inf a b = bot := rfl

theorem a_sup_b_eq_ab : sup a b = ab := rfl

def m : IdealLattice → ℝ
  | bot => 0
  | a   => 1
  | b   => 2
  | ab  => 3
  | abc => 10
  | abd => 20
  | top => 30

theorem m_monotone : ∀ x y : IdealLattice, le x y → m x ≤ m y := by
  intro x y hxy
  cases x <;> cases y <;>
    cases hxy <;> (simp [m] <;> norm_num)

theorem m_disjoint_additive : m (sup a b) = m a + m b := by
  simp [m, sup]
  norm_num

theorem only_disjoint_pair_is_a_b :
    ∀ x y : IdealLattice, x ≠ bot → y ≠ bot → inf x y = bot → (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  intro x y hx hy hinf
  cases x <;> cases y <;>
    simp [inf] at hx hy hinf ⊢

theorem modular_law_fails_abc_abd :
    m (sup abc abd) + m (inf abc abd) ≠ m abc + m abd := by
  simp [m, sup, inf]
  norm_num

instance : DistribLattice IdealLattice where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> trivial

/-- Distributivity and disjoint additivity do not imply modularity. -/
theorem counterexample_to_modular_law :
    ∃ (α : Type) (_ : DistribLattice α) (_ : OrderBot α),
      ∃ (m : α → ℝ),
        (∀ x y : α, x ≤ y → m x ≤ m y) ∧
        (∀ x y : α, x ⊓ y = ⊥ → m (x ⊔ y) = m x + m y) ∧
        (∃ x y : α, m (x ⊔ y) + m (x ⊓ y) ≠ m x + m y) := by
  use IdealLattice, inferInstance, inferInstance
  use m
  constructor
  · exact m_monotone
  constructor
  · intro x y hdisj
    by_cases hx : x = bot
    · subst hx
      change m (IdealLattice.sup bot y) = m bot + m y
      simp [IdealLattice.sup, m]
    by_cases hy : y = bot
    · subst hy
      change m (IdealLattice.sup x bot) = m x + m bot
      simp [IdealLattice.sup, m]
    have := only_disjoint_pair_is_a_b x y hx hy hdisj
    cases this with
    | inl h =>
        rcases h with ⟨rfl, rfl⟩
        exact m_disjoint_additive
    | inr h =>
        rcases h with ⟨rfl, rfl⟩
        change m (IdealLattice.sup b a) = m b + m a
        simp [IdealLattice.sup, m]
        norm_num
  · use abc, abd
    exact modular_law_fails_abc_abd

end IdealLattice

end KnuthSkilling.Counterexamples
