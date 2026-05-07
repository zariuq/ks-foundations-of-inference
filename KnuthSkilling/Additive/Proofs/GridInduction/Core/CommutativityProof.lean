import KnuthSkilling.Core.Algebra

namespace KnuthSkilling.Additive.Proofs.GridInduction.Core

open Classical
open KSSemigroupBase KnuthSkillingMonoidBase KnuthSkillingAlgebra

/-!
# Formal Proof: KSSeparation Implies Commutativity

NO informal arguments. ONLY formal Lean proofs.
-/

variable {α : Type*} [KnuthSkillingMonoidBase α]

/-!
## Step 1: Basic Facts About Powers
-/

theorem iterate_op_strictMono (a : α) (ha : KnuthSkillingMonoidBase.ident < a) :
    StrictMono (iterate_op a) :=
  KnuthSkillingAlgebra.iterate_op_strictMono a ha

theorem iterate_op_lt_of_base_lt {a b : α} (hab : a < b) (k : ℕ) (hk : 0 < k) :
    iterate_op a k < iterate_op b k := by
  induction k with
  | zero => exact absurd hk (Nat.not_lt_zero 0)
  | succ k ih =>
    cases Nat.eq_zero_or_pos k with
    | inl hzero =>
      subst hzero
      simp [iterate_op_one]
      exact hab
    | inr hpos =>
      calc iterate_op a (k + 1)
          = op a (iterate_op a k) := rfl
        _ < op a (iterate_op b k) := op_strictMono_right a (ih hpos)
        _ < op b (iterate_op b k) := op_strictMono_left (iterate_op b k) hab
        _ = iterate_op b (k + 1) := rfl

section Separation

variable [KSSeparation α]

/-!
## Step 2: The Separation Constraint

If x⊕y < y⊕x, we can apply separation with base (x⊕y).
-/

theorem separation_with_self_base (x y : α) (hx : ident < x) (hy : ident < y)
    (hlt : op x y < op y x) :
    ∃ n m : ℕ, 0 < m ∧ m < n ∧
    iterate_op (op x y) n ≤ iterate_op (op y x) m := by
  -- First prove x⊕y > ident
  have hxy : ident < op x y := by
    calc ident
        = op ident ident := (op_ident_left ident).symm
      _ < op x ident := op_strictMono_left ident hx
      _ = x := op_ident_right x
      _ < op x y := by
        calc x
            = op x ident := (op_ident_right x).symm
          _ < op x y := op_strictMono_right x hy

  -- And y⊕x > ident
  have hyx : ident < op y x := by
    calc ident
        = op ident ident := (op_ident_left ident).symm
      _ < op y ident := op_strictMono_left ident hy
      _ = y := op_ident_right y
      _ < op y x := by
        calc y
            = op y ident := (op_ident_right y).symm
          _ < op y x := op_strictMono_right y hx

  -- Apply KSSeparation with base a = (x⊕y)
  obtain ⟨n, m, hm_pos, h_left, h_right⟩ := KSSeparation.separation hxy hxy hyx hlt

  -- From h_left: (x⊕y)^m < (x⊕y)^n, which gives m < n
  have hmn : m < n := by
    by_contra h_not
    push_neg at h_not
    -- If m ≥ n, then (x⊕y)^m ≥ (x⊕y)^n by monotonicity
    rcases Nat.le_iff_lt_or_eq.mp h_not with hgt | heq
    · -- m > n case
      have : iterate_op (op x y) n < iterate_op (op x y) m :=
        iterate_op_strictMono (op x y) hxy hgt
      exact not_le.mpr this (le_of_lt h_left)
    · -- m = n case
      subst heq
      exact LT.lt.false h_left

  exact ⟨n, m, hm_pos, hmn, h_right⟩

/-!
## Step 3: Apply Separation with Different Base

Use y⊕x as base instead.
-/

theorem separation_with_reverse_base (x y : α) (hx : ident < x) (hy : ident < y)
    (hlt : op x y < op y x) :
    ∃ n' m' : ℕ, 0 < m' ∧
    iterate_op (op x y) m' < iterate_op (op y x) n' ∧
    iterate_op (op y x) n' ≤ iterate_op (op y x) m' := by
  -- Same ident < bounds as before
  have hxy : ident < op x y := by
    calc ident
        = op ident ident := (op_ident_left ident).symm
      _ < op x ident := op_strictMono_left ident hx
      _ = x := op_ident_right x
      _ < op x y := by
        calc x = op x ident := (op_ident_right x).symm
             _ < op x y := op_strictMono_right x hy

  have hyx : ident < op y x := by
    calc ident
        = op ident ident := (op_ident_left ident).symm
      _ < op y ident := op_strictMono_left ident hy
      _ = y := op_ident_right y
      _ < op y x := by
        calc y = op y ident := (op_ident_right y).symm
             _ < op y x := op_strictMono_right y hx

  -- Apply KSSeparation with base b = (y⊕x)
  exact KSSeparation.separation hyx hxy hyx hlt

/-!
## Step 4: Derive the Contradiction

From Step 3: (y⊕x)^n' ≤ (y⊕x)^m'
This implies n' ≤ m' (by strict monotonicity).

If n' < m', then (y⊕x)^n' < (y⊕x)^m', contradicting the inequality.
So n' = m'.

Then we have (x⊕y)^m' < (y⊕x)^m' and (y⊕x)^m' ≤ (y⊕x)^m' (trivial).

But this is consistent! No contradiction yet...

Let me try combining constraints from both separations.
-/

/-!
## Step 5: Use Separation with x as Base

Let me try using x as the base.
-/

theorem separation_with_x_base (x y : α) (hx : ident < x) (hy : ident < y)
    (hlt : op x y < op y x) :
    ∃ nx mx : ℕ, 0 < mx ∧
    iterate_op (op x y) mx < iterate_op x nx ∧
    iterate_op x nx ≤ iterate_op (op y x) mx := by
  have hxy : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op x ident := op_strictMono_left ident hx
         _ = x := op_ident_right x
         _ < op x y := by
           calc x = op x ident := (op_ident_right x).symm
                _ < op x y := op_strictMono_right x hy

  have hyx : ident < op y x := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op y ident := op_strictMono_left ident hy
         _ = y := op_ident_right y
         _ < op y x := by
           calc y = op y ident := (op_ident_right y).symm
                _ < op y x := op_strictMono_right y hx

  exact KSSeparation.separation hx hxy hyx hlt

/-!
## Step 6: Analyze Relationships Between Bases

Key facts:
- x < op x y (since y > ident and monotone)
- y < op y x (since x > ident and monotone)
- op x y < op y x (assumption)

Therefore: x < op x y < op y x
-/

omit [KSSeparation α] in
theorem base_ordering (x y : α) (hy : KnuthSkillingMonoidBase.ident < y)
    (hlt : op x y < op y x) :
    x < op x y ∧ op x y < op y x := by
  constructor
  · calc x = op x ident := (op_ident_right x).symm
         _ < op x y := op_strictMono_right x hy
  · exact hlt

/-!
## Step 7: Combine Constraints from Multiple Separations

From separation with base x:
- (x⊕y)^mx < x^nx ≤ (y⊕x)^mx

From separation with base (x⊕y):
- (x⊕y)^m₁ < (x⊕y)^n₁ ≤ (y⊕x)^m₁  where m₁ < n₁

Key insight: Since x < x⊕y, we have x^k < (x⊕y)^k for all k.

From (x⊕y)^mx < x^nx:
- This means x^nx beats (x⊕y)^mx even though x < x⊕y
- This requires nx >> mx (much larger exponent overcomes smaller base)

From x^nx ≤ (y⊕x)^mx:
- Since x < y⊕x, we have x^k < (y⊕x)^k for all k
- In particular: x^mx < (y⊕x)^mx
- So x^nx ≤ (y⊕x)^mx means x^nx ≤ (y⊕x)^mx

Now, if nx > mx, then:
- x^mx < x^nx (by strictMono)
- x^nx < (y⊕x)^nx (since x < y⊕x)

We have: x^nx ≤ (y⊕x)^mx

Since mx < nx (required for the first inequality to hold), we'd have:
- (y⊕x)^mx < (y⊕x)^nx

So: x^nx ≤ (y⊕x)^mx < (y⊕x)^nx

This gives: x^nx < (y⊕x)^nx which is just x < y⊕x. Still no contradiction!

Actually wait. Let me check if mx < nx is really required.
-/

theorem separation_x_base_exponent_constraint (x y : α) (hx : ident < x) (hy : ident < y)
    (hlt : op x y < op y x) :
    ∃ nx mx : ℕ, 0 < mx ∧ mx < nx ∧
    iterate_op x nx ≤ iterate_op (op y x) mx := by
  obtain ⟨nx, mx, hmx_pos, h_left, h_right⟩ := separation_with_x_base x y hx hy hlt

  -- Prove x < x⊕y
  have hx_xy : x < op x y := by
    calc x = op x ident := (op_ident_right x).symm
         _ < op x y := op_strictMono_right x hy

  -- Prove x^k < (x⊕y)^k for all k > 0
  have hpow : ∀ k > 0, iterate_op x k < iterate_op (op x y) k := by
    intro k hk
    exact iterate_op_lt_of_base_lt hx_xy k hk

  -- From h_left: (x⊕y)^mx < x^nx
  -- This means nx must beat mx significantly

  -- Claim: mx < nx
  have hmx_nx : mx < nx := by
    by_contra h_not
    push_neg at h_not
    cases Nat.le_iff_lt_or_eq.mp h_not with
    | inl h_gt =>
      -- mx > nx case
      have : iterate_op x nx < iterate_op x mx := iterate_op_strictMono x hx h_gt
      have : iterate_op (op x y) mx < iterate_op x mx := by
        exact lt_trans h_left this
      have : iterate_op x mx < iterate_op (op x y) mx := hpow mx (Nat.zero_lt_of_lt h_gt)
      exact absurd this (not_lt.mpr (le_of_lt ‹iterate_op (op x y) mx < iterate_op x mx›))
    | inr h_eq =>
      -- mx = nx case
      subst h_eq
      have : iterate_op (op x y) nx < iterate_op x nx := h_left
      have : iterate_op x nx < iterate_op (op x y) nx := hpow nx hmx_pos
      exact absurd ‹iterate_op x nx < iterate_op (op x y) nx› (not_lt.mpr (le_of_lt ‹iterate_op (op x y) nx < iterate_op x nx›))

  exact ⟨nx, mx, hmx_pos, hmx_nx, h_right⟩

/-!
## Step 8: Try Using y as Base Too

Now use y as the base as well.
-/

theorem separation_with_y_base (x y : α) (hx : ident < x) (hy : ident < y)
    (hlt : op x y < op y x) :
    ∃ ny my : ℕ, 0 < my ∧
    iterate_op (op x y) my < iterate_op y ny ∧
    iterate_op y ny ≤ iterate_op (op y x) my := by
  have hxy : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op x ident := op_strictMono_left ident hx
         _ = x := op_ident_right x
         _ < op x y := by
           calc x = op x ident := (op_ident_right x).symm
                _ < op x y := op_strictMono_right x hy

  have hyx : ident < op y x := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op y ident := op_strictMono_left ident hy
         _ = y := op_ident_right y
         _ < op y x := by
           calc y = op y ident := (op_ident_right y).symm
                _ < op y x := op_strictMono_right y hx

  exact KSSeparation.separation hy hxy hyx hlt

/-!
## Status

This file contains a collection of *formalized constraints* obtainable from `KSSeparation` under
an assumed noncommutativity witness `x⊕y < y⊕x`.

The missing “final contradiction” has since been supplied by the mass-counting proof:
- `KnuthSkilling/Additive/Axioms/SandwichSeparation.lean`
- `KnuthSkilling/Additive/Proofs/GridInduction/Core/SeparationImpliesCommutative.lean`

Accordingly, this file is now a *historical appendix* of intermediate lemmas. -/

end Separation

end KnuthSkilling.Additive.Proofs.GridInduction.Core
