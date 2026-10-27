import KnuthSkilling.Core.HeytingValuation
import KnuthSkilling.Core.HeytingIntervalRepresentation
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Boolean incomparability and nonfaithful scalar observations

The four-element diamond is Boolean. Its two middle elements are incomparable,
while normalized modular real observations can order them in either direction.
This separates total order of numerical answers from order reflection of events;
neither incomparability nor a scalar ordering proves failure of complementation.
-/

namespace KnuthSkilling.Counterexamples
open KnuthSkilling.Heyting

inductive DiamondLattice
  | bot : DiamondLattice
  | left : DiamondLattice
  | right : DiamondLattice
  | top : DiamondLattice
  deriving DecidableEq, Repr

namespace DiamondLattice

def le : DiamondLattice → DiamondLattice → Prop
  | .bot, _ => True
  | _, .top => True
  | .left, .left => True
  | .right, .right => True
  | _, _ => False

instance : LE DiamondLattice where
  le := le

instance decidableLE : DecidableRel (α := DiamondLattice) (· ≤ ·) := by
  intro a b
  change Decidable (le a b)
  cases a <;> cases b <;> dsimp only [le] <;> infer_instance

theorem le_refl (a : DiamondLattice) : a ≤ a := by
  cases a <;> trivial

theorem le_trans {a b c : DiamondLattice} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> trivial

theorem le_antisymm {a b : DiamondLattice} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a <;> cases b <;> (first | rfl | exact absurd hba (fun h => h) | exact absurd hab (fun h => h))

instance : Preorder DiamondLattice where
  le_refl := le_refl
  le_trans := @le_trans

instance : PartialOrder DiamondLattice where
  le_antisymm := @le_antisymm

@[simp] def inf (a b : DiamondLattice) : DiamondLattice :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, b => b
  | a, .top => a
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .bot
  | .right, .left => .bot

@[simp] def sup (a b : DiamondLattice) : DiamondLattice :=
  match a, b with
  | .top, _ => .top
  | _, .top => .top
  | .bot, b => b
  | a, .bot => a
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .top
  | .right, .left => .top

theorem inf_le_left' (a b : DiamondLattice) : inf a b ≤ a := by
  cases a <;> cases b <;> simp only [inf] <;> trivial

theorem inf_le_right' (a b : DiamondLattice) : inf a b ≤ b := by
  cases a <;> cases b <;> simp only [inf] <;> trivial

theorem le_inf' {a b c : DiamondLattice} (hab : a ≤ b) (hac : a ≤ c) : a ≤ inf b c := by
  cases a <;> cases b <;> cases c <;> simp only [inf] at * <;> trivial

theorem le_sup_left' (a b : DiamondLattice) : a ≤ sup a b := by
  cases a <;> cases b <;> simp only [sup] <;> trivial

theorem le_sup_right' (a b : DiamondLattice) : b ≤ sup a b := by
  cases a <;> cases b <;> simp only [sup] <;> trivial

theorem sup_le' {a b c : DiamondLattice} (hac : a ≤ c) (hbc : b ≤ c) : sup a b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp only [sup] at * <;> trivial

theorem sup_inf_distrib (a b c : DiamondLattice) : sup a (inf b c) = inf (sup a b) (sup a c) := by
  cases a <;> cases b <;> cases c <;> rfl

instance : Lattice DiamondLattice where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := @le_inf'
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := @sup_le'

instance : DistribLattice DiamondLattice where
  le_sup_inf := fun a b c => by
    cases a <;> cases b <;> cases c <;> trivial

instance : OrderBot DiamondLattice where
  bot := .bot
  bot_le x := by cases x <;> trivial

instance : OrderTop DiamondLattice where
  top := .top
  le_top x := by cases x <;> trivial

instance : BoundedOrder DiamondLattice where

/-- The four-element diamond is Boolean despite its incomparable middle elements. -/
instance : BooleanAlgebra DiamondLattice where
  compl
    | .bot => .top | .top => .bot | .left => .right | .right => .left
  inf_compl_le_bot x := by cases x <;> trivial
  top_le_sup_compl x := by cases x <;> trivial
  le_top x := by cases x <;> trivial
  bot_le x := by cases x <;> trivial

def diamondLeft : DiamondLattice := .left
def diamondRight : DiamondLattice := .right
theorem not_left_le_right : ¬(diamondLeft ≤ diamondRight) := fun h => h
theorem not_right_le_left : ¬(diamondRight ≤ diamondLeft) := fun h => h
theorem diamond_has_incomparable : Incomparable diamondLeft diamondRight :=
  ⟨not_left_le_right, not_right_le_left⟩

def weight (p : ℝ) : DiamondLattice → ℝ
  | .bot => 0 | .left => p | .right => 1-p | .top => 1

/-- Actual normalized modular observations can order the incomparable pair either way. -/
def valuation (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : ModularValuation DiamondLattice where
  val := weight p
  monotone := by
    intro a b hab
    change le a b at hab
    cases a <;> cases b <;> simp_all [weight, le]
  val_bot := rfl
  val_top := rfl
  modular a b := by
    change weight p a + weight p b = weight p (sup a b) + weight p (inf a b)
    cases a <;> cases b <;> simp [weight, sup, inf] <;> ring

theorem opposite_valuation_orders : ∃ ν μ : ModularValuation DiamondLattice,
    ν.val diamondLeft < ν.val diamondRight ∧ μ.val diamondRight < μ.val diamondLeft := by
  refine ⟨valuation 0 (by norm_num) (by norm_num), valuation 1 (by norm_num) (by norm_num), ?_⟩
  norm_num [valuation, weight, diamondLeft, diamondRight]

theorem point_valuation_forces_ordering : ∀ ν : ModularValuation DiamondLattice,
    ν.val diamondLeft ≤ ν.val diamondRight ∨ ν.val diamondRight ≤ ν.val diamondLeft :=
  fun ν => le_total (ν.val diamondLeft) (ν.val diamondRight)

theorem diamond_partial_order_collapsed :
    Incomparable diamondLeft diamondRight ∧
    (∀ ν : ModularValuation DiamondLattice,
      ν.val diamondLeft ≤ ν.val diamondRight ∨ ν.val diamondRight ≤ ν.val diamondLeft) :=
  ⟨diamond_has_incomparable, point_valuation_forces_ordering⟩

/-- Historical total-order observation; `opposite_valuation_orders` supplies the witnesses. -/
theorem diamond_no_canonical_ordering :
    Incomparable diamondLeft diamondRight ∧
    (∀ ν : ModularValuation DiamondLattice,
      ν.val diamondLeft ≤ ν.val diamondRight ∨ ν.val diamondRight ≤ ν.val diamondLeft) :=
  diamond_partial_order_collapsed

end DiamondLattice
end KnuthSkilling.Counterexamples
