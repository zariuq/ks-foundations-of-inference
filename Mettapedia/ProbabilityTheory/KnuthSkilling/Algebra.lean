/-
# Knuth-Skilling Algebra: Basic Operations

Basic lemmas for KnuthSkillingAlgebra including:
- iterate_op function
- Commutativity for commutative operations
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

namespace KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-- Iterate the operation: x ⊕ x ⊕ ... ⊕ x (n times).
This builds the sequence: ident, x, x⊕x, x⊕(x⊕x), ... -/
def iterate_op (x : α) : ℕ → α
  | 0 => ident
  | n + 1 => op x (iterate_op x n)

/-- iterate_op 0 = ident -/
theorem iterate_op_zero (a : α) : iterate_op a 0 = ident := rfl

/-- iterate_op 1 = a -/
theorem iterate_op_one (a : α) : iterate_op a 1 = a := by
  simp [iterate_op, op_ident_right]

/-- For commutative K&S algebras, iterate_op respects addition.
Note: The minimal KnuthSkillingAlgebra doesn't assume commutativity.
For the probability case (combine_fn is commutative), this holds. -/
theorem iterate_op_add_comm (x : α) (h_comm : ∀ a b : α, op a b = op b a)
    (m n : ℕ) :
    iterate_op x (m + n) = op (iterate_op x m) (iterate_op x n) := by
  induction n with
  | zero => simp [iterate_op, op_ident_right]
  | succ n ih =>
    -- Use commutativity to swap arguments and apply associativity
    calc iterate_op x (m + (n + 1))
        = iterate_op x ((m + n) + 1) := by ring_nf
      _ = op x (iterate_op x (m + n)) := rfl
      _ = op x (op (iterate_op x m) (iterate_op x n)) := by rw [ih]
      _ = op (op x (iterate_op x m)) (iterate_op x n) := by rw [← op_assoc]
      _ = op (op (iterate_op x m) x) (iterate_op x n) := by rw [h_comm x]
      _ = op (iterate_op x m) (op x (iterate_op x n)) := by rw [op_assoc]
      _ = op (iterate_op x m) (iterate_op x (n + 1)) := rfl

/-- Relation between Nat.iterate (op a) and iterate_op.
Nat.iterate (op a) n a = iterate_op a (n+1) -/
theorem nat_iterate_eq_iterate_op_succ (a : α) (n : ℕ) :
    Nat.iterate (op a) n a = iterate_op a (n + 1) := by
  induction n with
  | zero => simp [iterate_op, op_ident_right]
  | succ k ih =>
    -- Goal: (op a)^[k+1] a = iterate_op a (k+2)
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [ih]
    -- Now: op a (iterate_op a (k+1)) = iterate_op a (k+2)
    -- By definition: iterate_op a (k+2) = op a (iterate_op a (k+1))
    rfl

/-- For any x in α, x is bounded above by some iterate of a.
This follows directly from Archimedean property (no totality needed). -/
theorem bounded_by_iterate (a : α) (ha : ident < a) (x : α) :
    ∃ n : ℕ, x < iterate_op a n := by
  -- Archimedean gives x < Nat.iterate (op a) n a for some n
  obtain ⟨n, hn⟩ := op_archimedean a x ha
  rw [nat_iterate_eq_iterate_op_succ] at hn
  exact ⟨n + 1, hn⟩

/-- iterate_op is strict mono in its iteration count for a > ident -/
theorem iterate_op_strictMono (a : α) (ha : ident < a) : StrictMono (iterate_op a) := by
  intro m n hmn
  induction n with
  | zero => exact (Nat.not_lt_zero m hmn).elim
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
    · -- m < k case: use IH and then show iterate_op a k < iterate_op a (k+1)
      have h1 : iterate_op a m < iterate_op a k := ih hlt
      have h2 : iterate_op a k < iterate_op a (k + 1) := by
        conv_lhs => rw [← op_ident_left (iterate_op a k)]
        exact op_strictMono_left (iterate_op a k) ha
      exact lt_trans h1 h2
    · -- m = k case: show iterate_op a m < iterate_op a (k+1)
      rw [heq]
      conv_lhs => rw [← op_ident_left (iterate_op a k)]
      exact op_strictMono_left (iterate_op a k) ha

/-- op is monotone in the left argument (from strict monotonicity). -/
theorem op_mono_left (y : α) {x₁ x₂ : α} (h : x₁ ≤ x₂) : op x₁ y ≤ op x₂ y := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (op_strictMono_left y hlt)
  · rw [heq]

/-- op is monotone in the right argument (from strict monotonicity). -/
theorem op_mono_right (x : α) {y₁ y₂ : α} (h : y₁ ≤ y₂) : op x y₁ ≤ op x y₂ := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (op_strictMono_right x hlt)
  · rw [heq]

/-- iterate_op preserves the operation: a^{n+1} = a ⊕ a^n -/
theorem iterate_op_succ (a : α) (n : ℕ) : iterate_op a (n + 1) = op a (iterate_op a n) := rfl

/-- Addition law for iterate_op: a^m ⊕ a^n = a^{m+n} -/
theorem iterate_op_add (a : α) (m n : ℕ) :
    op (iterate_op a m) (iterate_op a n) = iterate_op a (m + n) := by
  induction m with
  | zero =>
    simp only [iterate_op_zero, op_ident_left, Nat.zero_add]
  | succ m ih =>
    calc op (iterate_op a (m + 1)) (iterate_op a n)
        = op (op a (iterate_op a m)) (iterate_op a n) := by rw [iterate_op_succ]
      _ = op a (op (iterate_op a m) (iterate_op a n)) := by rw [op_assoc]
      _ = op a (iterate_op a (m + n)) := by rw [ih]
      _ = iterate_op a (m + n + 1) := by rw [← iterate_op_succ]
      _ = iterate_op a (m + 1 + n) := by ring_nf

/-- Multiplication law: (a^n)^m = a^{nm} -/
theorem iterate_op_mul (x : α) (n m : ℕ) :
    iterate_op (iterate_op x n) m = iterate_op x (n * m) := by
  induction m with
  | zero => simp only [iterate_op_zero, Nat.mul_zero]
  | succ m ih =>
    calc iterate_op (iterate_op x n) (m + 1)
        = op (iterate_op x n) (iterate_op (iterate_op x n) m) := rfl
      _ = op (iterate_op x n) (iterate_op x (n * m)) := by rw [ih]
      _ = iterate_op x (n + n * m) := by rw [iterate_op_add]
      _ = iterate_op x (n * (m + 1)) := by ring_nf

/-- Repetition lemma (≤ version): If a^n ≤ x^m then a^{nk} ≤ x^{mk} -/
theorem repetition_lemma_le (a x : α) (n m k : ℕ) (h : iterate_op a n ≤ iterate_op x m) :
    iterate_op a (n * k) ≤ iterate_op x (m * k) := by
  induction k with
  | zero => simp only [Nat.mul_zero, iterate_op_zero]; exact le_refl _
  | succ k ih =>
    have eq_a : n * (k + 1) = n * k + n := by ring
    have eq_x : m * (k + 1) = m * k + m := by ring
    rw [eq_a, eq_x, ← iterate_op_add, ← iterate_op_add]
    calc op (iterate_op a (n * k)) (iterate_op a n)
        ≤ op (iterate_op a (n * k)) (iterate_op x m) := op_mono_right _ h
      _ ≤ op (iterate_op x (m * k)) (iterate_op x m) := op_mono_left _ ih

/-- Repetition lemma (< version): If a^n < x^m then a^{nk} < x^{mk} for k > 0 -/
theorem repetition_lemma_lt (a x : α) (n m k : ℕ) (hk : k > 0) (h : iterate_op a n < iterate_op x m) :
    iterate_op a (n * k) < iterate_op x (m * k) := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero =>
      rw [Nat.zero_add, Nat.mul_one, Nat.mul_one]
      exact h
    | succ k ih =>
      have eq_a : n * (k + 1 + 1) = n * (k + 1) + n := by ring
      have eq_x : m * (k + 1 + 1) = m * (k + 1) + m := by ring
      rw [eq_a, eq_x, ← iterate_op_add, ← iterate_op_add]
      calc op (iterate_op a (n * (k + 1))) (iterate_op a n)
          < op (iterate_op a (n * (k + 1))) (iterate_op x m) :=
            op_strictMono_right _ h
        _ < op (iterate_op x (m * (k + 1))) (iterate_op x m) :=
            op_strictMono_left _ (ih (Nat.succ_pos k))

/-- iterate_op is strictly monotone in base for positive iterations -/
theorem iterate_op_strictMono_base (m : ℕ) (hm : 0 < m) (x y : α) (hxy : x < y) :
    iterate_op x m < iterate_op y m := by
  cases m with
  | zero => omega
  | succ n =>
    induction n with
    | zero =>
      simp only [Nat.zero_add, iterate_op_one]
      exact hxy
    | succ n ih =>
      have hm_pos : 0 < n + 1 := Nat.succ_pos n
      calc iterate_op x (n + 1 + 1)
          = op x (iterate_op x (n + 1)) := rfl
        _ < op x (iterate_op y (n + 1)) := op_strictMono_right x (ih hm_pos)
        _ < op y (iterate_op y (n + 1)) := op_strictMono_left (iterate_op y (n + 1)) hxy
        _ = iterate_op y (n + 1 + 1) := rfl

/-- Positive iterations are strictly greater than identity -/
theorem iterate_op_pos (y : α) (hy : ident < y) (m : ℕ) (hm : m > 0) :
    ident < iterate_op y m := by
  calc ident = iterate_op y 0 := (iterate_op_zero y).symm
    _ < iterate_op y m := iterate_op_strictMono y hy hm

end KnuthSkillingAlgebra

/-! ## Separation Typeclass

The KSSeparation typeclass captures the property that we can always find rational witnesses
separating any two distinct positive elements. This is proven from the K-S axioms in
SeparationProof.lean and used by the representation theorem in RepTheorem.lean.
-/

/-- **Separation Typeclass**: The property that we can always find rational witnesses
separating any two distinct positive elements.

This is NOT a primitive axiom - it is derivable from the Knuth-Skilling axioms above.
However, for organizational clarity, we factor it into a typeclass:

**Layer A (RepTheorem.lean)**: Assumes this property holds, proves representation theorem
**Layer B (SeparationProof.lean)**: Proves this property from K-S axioms (discharges the spec)

This factorization avoids circularity:
- The representation theorem uses separation to prove Θ is strictly monotonic
- Separation is proven using direct Archimedean arguments (without using Θ)

**Mathematical content**: If x < y, then the gap between y^m and x^m grows unboundedly.
Eventually this gap contains a full step from a^n to a^{n+1}, giving witnesses with
x^m < a^n ≤ y^m. -/
class KSSeparation (α : Type*) [KnuthSkillingAlgebra α] where
  /-- For any positive x < y and any base a > ident, we can find exponents (n, m)
  such that x^m < a^n ≤ y^m. This is the key property enabling representation. -/
  separation : ∀ {a x y : α}, KnuthSkillingAlgebra.ident < a →
      KnuthSkillingAlgebra.ident < x → KnuthSkillingAlgebra.ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
      KnuthSkillingAlgebra.iterate_op a n ≤ KnuthSkillingAlgebra.iterate_op y m

end Mettapedia.ProbabilityTheory.KnuthSkilling
