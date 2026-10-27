import Mathlib.Algebra.Order.Monoid.Prod
import KnuthSkilling.Core.Algebra

namespace KnuthSkilling.Additive.Counterexamples

open Classical
open Prod.Lex
open KnuthSkilling
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# A Product-Lex Model Fails the Separation (“Sandwich”) Axiom

This file proves that the iterate/power “sandwich” axiom `KSSeparation` fails in a simple
commutative product-like model. Intuitively, `KSSeparation` rules out “independent dimensions”:
even when the operation is commutative, there can be no fixed base `a` that can sandwich an
`x < y` comparison that lives entirely in a different coordinate.

## Model

We use `NatProdLex := ℕ ×ₗ ℕ` (lexicographically ordered pairs) with componentwise addition:
`(u₁,u₂) ⊕ (v₁,v₂) := (u₁+v₁, u₂+v₂)`.

This is a perfectly reasonable commutative ordered monoid, but it is not Archimedean (it has
infinitesimals in the second coordinate relative to the first), and it fails `KSSeparation`.
-/

namespace ProductFailsSeparation

/-- ℕ × ℕ with lexicographic order (Mathlib `Prod.Lex`). -/
abbrev NatProdLex := ℕ ×ₗ ℕ

/-- Componentwise addition on `NatProdLex`. -/
def natProdAdd (x y : NatProdLex) : NatProdLex :=
  toLex ((ofLex x).1 + (ofLex y).1, (ofLex x).2 + (ofLex y).2)

/-- The identity element `(0,0)`. -/
def natProdIdent : NatProdLex := toLex (0, 0)

theorem natProdAdd_def (x y : NatProdLex) :
    natProdAdd x y = toLex ((ofLex x).1 + (ofLex y).1, (ofLex x).2 + (ofLex y).2) :=
  rfl

/-- `NatProdLex` is a `KnuthSkillingAlgebraBase`: ordered associative monoid with strict monotonicity. -/
instance : KnuthSkillingAlgebraBase NatProdLex where
  op := natProdAdd
  ident := natProdIdent
  op_assoc := by
    intro x y z
    simp [natProdAdd_def, Nat.add_left_comm, Nat.add_comm]
  op_ident_right := by
    intro x
    simp [natProdAdd_def, natProdIdent]
  op_ident_left := by
    intro x
    simp [natProdAdd_def, natProdIdent]
  op_strictMono_left := by
    intro y a b h
    change a + y < b + y
    exact _root_.add_lt_add_left h y
  op_strictMono_right := by
    intro x a b h
    change x + a < x + b
    exact _root_.add_lt_add_right h x
  ident_le := fun _ => bot_le

/-- In the product model, `ident` is definitionally `natProdIdent`. -/
@[simp] theorem ident_eq_natProdIdent : (ident (α := NatProdLex)) = natProdIdent := rfl

/-- In the product model, `op` is definitionally `natProdAdd`. -/
@[simp] theorem op_eq_natProdAdd : (op (α := NatProdLex)) = natProdAdd := rfl

/-- Compute iterates in the product model: `p^n = (n*p.1, n*p.2)`. -/
theorem iterate_op_natProd (p : NatProdLex) (n : ℕ) :
    iterate_op p n = toLex (n * (ofLex p).1, n * (ofLex p).2) := by
  induction n with
  | zero =>
    simp [KnuthSkillingAlgebra.iterate_op, natProdIdent]
  | succ n ih =>
    -- Unfold once, then compute using the IH.
    simp [KnuthSkillingAlgebra.iterate_op, natProdAdd_def, ih, Nat.succ_mul, Nat.add_comm]

/-!
## Main theorem: separation fails

Take:
- `x = (0,1)`, `y = (0,2)` so `x < y` (both in the “second coordinate”)
- `a = (1,0)` as a base (in the “first coordinate”)

Then `x^m = (0,m)` and `y^m = (0,2m)` live in the second coordinate, while `a^n = (n,0)` lives
in the first. There is no way to have `(0,m) < (n,0) ≤ (0,2m)` in lex order.
-/

theorem natProdLex_fails_KSSeparation : ¬ KSSeparation NatProdLex := by
  intro hSep
  classical
  -- Unpack the class field.
  rcases hSep with ⟨sep⟩

  let x : NatProdLex := toLex (0, 1)
  let y : NatProdLex := toLex (0, 2)
  let a : NatProdLex := toLex (1, 0)

  have ha : natProdIdent < a := by
    simp [natProdIdent, a, Prod.Lex.toLex_lt_toLex]
  have hx : natProdIdent < x := by
    simp [natProdIdent, x, Prod.Lex.toLex_lt_toLex]
  have hy : natProdIdent < y := by
    simp [natProdIdent, y, Prod.Lex.toLex_lt_toLex]
  have hxy : x < y := by
    simp [x, y, Prod.Lex.toLex_lt_toLex]

  -- Apply separation to x < y with base a.
  rcases sep (a := a) (x := x) (y := y) (by simpa [KnuthSkillingAlgebraBase.ident, natProdIdent] using ha)
      (by simpa [KnuthSkillingAlgebraBase.ident, natProdIdent] using hx)
      (by simpa [KnuthSkillingAlgebraBase.ident, natProdIdent] using hy) hxy with
    ⟨n, m, hm_pos, h_lower, h_upper⟩

  -- Rewrite the iterates into explicit coordinates.
  have h_lower' : toLex (0, m) < toLex (n, 0) := by
    simpa [x, a, iterate_op_natProd] using h_lower
  have h_upper' : toLex (n, 0) ≤ toLex (0, m * 2) := by
    simpa [a, y, iterate_op_natProd] using h_upper

  -- From (0,m) < (n,0) we get 0 < n (the other case would force m < 0).
  have hn_pos : 0 < n := by
    have h' : 0 < n ∨ 0 = n ∧ m < 0 := by
      simpa [Prod.Lex.toLex_lt_toLex] using h_lower'
    rcases h' with hn_pos | hn0
    · exact hn_pos
    · rcases hn0 with ⟨_, hm_lt0⟩
      exact (Nat.not_lt_zero m hm_lt0).elim

  -- From (n,0) ≤ (0,2m) we get n = 0 (since n < 0 is impossible in ℕ).
  have hn_zero : n = 0 := by
    have h' : n < 0 ∨ n = 0 ∧ (0 : ℕ) ≤ m * 2 := by
      simpa [Prod.Lex.toLex_le_toLex] using h_upper'
    rcases h' with hn_lt0 | hn0
    · exact (Nat.not_lt_zero n hn_lt0).elim
    · exact hn0.1

  exact (lt_irrefl 0) (hn_zero ▸ hn_pos)

end ProductFailsSeparation

end KnuthSkilling.Additive.Counterexamples
