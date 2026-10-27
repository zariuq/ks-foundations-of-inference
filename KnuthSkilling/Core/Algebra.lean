/-
# Knuth-Skilling Algebra: Basic Operations

Basic lemmas for KnuthSkillingAlgebra including:
- iterate_op function
- Commutativity for commutative operations
-/

import KnuthSkilling.Core.Basic
import Mathlib.Algebra.Group.Commute.Basic

namespace KnuthSkilling

open KSSemigroupBase KnuthSkillingMonoidBase KnuthSkillingAlgebraBase

namespace KnuthSkillingAlgebra

section Base

variable {α : Type*} [KnuthSkillingMonoidBase α]

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

/-- The independently defined iteration agrees with powers of the supplied monoid. -/
theorem iterate_op_eq_pow (x : α) (n : ℕ) :
    let _ : Monoid α := KnuthSkillingMonoidBase.toMonoid
    iterate_op x n = x ^ n := by
  let _ : Monoid α := KnuthSkillingMonoidBase.toMonoid
  change iterate_op x n = x ^ n
  induction n with
  | zero => rfl
  | succ n ih =>
    change op x (iterate_op x n) = x ^ (n + 1)
    rw [ih, pow_succ']
    rfl

/-- Relation between Nat.iterate (op a) and iterate_op.
Nat.iterate (op a) n a = iterate_op a (n+1) -/
theorem nat_iterate_eq_iterate_op_succ (a : α) (n : ℕ) :
    Nat.iterate (op a) n a = iterate_op a (n + 1) := by
  induction n with
  | zero => simp [iterate_op, op_ident_right]
  | succ k ih =>
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [ih]
    rfl

/-- iterate_op is strict mono in its iteration count for a > ident -/
theorem iterate_op_strictMono (a : α) (ha : ident < a) : StrictMono (iterate_op a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change iterate_op a n < op a (iterate_op a n)
  simpa only [op_ident_left] using op_strictMono_left (iterate_op a n) ha

/-- op is monotone in the left argument (from strict monotonicity). -/
theorem op_mono_left (y : α) {x₁ x₂ : α} (h : x₁ ≤ x₂) : op x₁ y ≤ op x₂ y := by
  exact KSSemigroupBase.op_mono_left y h

/-- op is monotone in the right argument (from strict monotonicity). -/
theorem op_mono_right (x : α) {y₁ y₂ : α} (h : y₁ ≤ y₂) : op x y₁ ≤ op x y₂ := by
  exact KSSemigroupBase.op_mono_right x h

/-- iterate_op preserves the operation: a^{n+1} = a ⊕ a^n -/
theorem iterate_op_succ (a : α) (n : ℕ) : iterate_op a (n + 1) = op a (iterate_op a n) := rfl

/-- Addition law for iterate_op: a^m ⊕ a^n = a^{m+n} -/
theorem iterate_op_add (a : α) (m n : ℕ) :
    op (iterate_op a m) (iterate_op a n) = iterate_op a (m + n) := by
  let _ : Monoid α := KnuthSkillingMonoidBase.toMonoid
  change (iterate_op a m) * iterate_op a n = iterate_op a (m + n)
  simp only [iterate_op_eq_pow]
  exact (pow_add a m n).symm

/-- Multiplication law: (a^n)^m = a^{nm} -/
theorem iterate_op_mul (x : α) (n m : ℕ) :
    iterate_op (iterate_op x n) m = iterate_op x (n * m) := by
  let _ : Monoid α := KnuthSkillingMonoidBase.toMonoid
  simpa only [iterate_op_eq_pow] using (pow_mul x n m).symm

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

/-- iterate_op is monotone in base: x ≤ y → x^m ≤ y^m -/
theorem iterate_op_mono_base (m : ℕ) (x y : α) (hxy : x ≤ y) :
    iterate_op x m ≤ iterate_op y m := by
  induction m with
  | zero => simp only [iterate_op_zero]; exact le_refl _
  | succ n ih =>
    calc iterate_op x (n + 1)
        = op x (iterate_op x n) := rfl
      _ ≤ op x (iterate_op y n) := op_mono_right x ih
      _ ≤ op y (iterate_op y n) := op_mono_left (iterate_op y n) hxy
      _ = iterate_op y (n + 1) := rfl

/-- For commutative K&S algebras, iterate_op respects addition.
Note: The minimal KnuthSkillingAlgebra doesn't assume commutativity.
For the probability case (combine_fn is commutative), this holds. -/
theorem iterate_op_add_comm (x : α) (h_comm : ∀ a b : α, op a b = op b a)
    (m n : ℕ) :
    iterate_op x (m + n) = op (iterate_op x m) (iterate_op x n) := by
  calc iterate_op x (m + n) = op (iterate_op x n) (iterate_op x m) := by
         rw [Nat.add_comm]; exact (iterate_op_add x n m).symm
       _ = op (iterate_op x m) (iterate_op x n) := h_comm _ _

/-- Repetition lemma (≤ version): If a^n ≤ x^m then a^{nk} ≤ x^{mk} -/
theorem repetition_lemma_le (a x : α) (n m k : ℕ) (h : iterate_op a n ≤ iterate_op x m) :
    iterate_op a (n * k) ≤ iterate_op x (m * k) := by
  have hi := iterate_op_mono_base k (iterate_op a n) (iterate_op x m) h
  simpa only [iterate_op_mul] using hi

/-- Repetition lemma (< version): If a^n < x^m then a^{nk} < x^{mk} for k > 0 -/
theorem repetition_lemma_lt (a x : α) (n m k : ℕ) (hk : k > 0) (h : iterate_op a n < iterate_op x m) :
    iterate_op a (n * k) < iterate_op x (m * k) := by
  have hi := iterate_op_strictMono_base k hk (iterate_op a n) (iterate_op x m) h
  simpa only [iterate_op_mul] using hi

/-- Positive iterations are strictly greater than identity -/
theorem iterate_op_pos (y : α) (hy : ident < y) (m : ℕ) (hm : m > 0) :
    ident < iterate_op y m := by
  calc ident = iterate_op y 0 := (iterate_op_zero y).symm
    _ < iterate_op y m := iterate_op_strictMono y hy hm

/-- Negative iterates stay below the identity: if `y` is negative (in the identity-free sense),
then `y^m < ident` for all `m > 0`. -/
theorem iterate_op_lt_ident_of_isNegative (y : α) (hy : IsNegative y) (m : ℕ) (hm : 0 < m) :
    iterate_op y m < ident := by
  have hanti : StrictAnti (iterate_op y) := strictAnti_nat_of_succ_lt fun n => hy (iterate_op y n)
  exact hanti hm

/-- Connection: `iterate_op_pnat` equals `iterate_op` when n is positive.
    This bridges identity-free ℕ+ iteration with identity-based ℕ iteration. -/
theorem iterate_op_pnat_eq (x : α) (n : ℕ+) :
    iterate_op_pnat x n = iterate_op x n.val := by
  induction n using PNat.recOn with
  | one =>
    rw [iterate_op_pnat_one]
    have h1 : (1 : ℕ+).val = 1 := rfl
    rw [h1]
    exact (iterate_op_one x).symm
  | succ n ih =>
    rw [iterate_op_pnat_succ, ih]
    have hsucc : (n + 1 : ℕ+).val = n.val + 1 := PNat.add_coe n 1
    rw [hsucc, ← iterate_op_succ]

/-- **Distribution lemma**: `(x ⊕ y)^m = x^m ⊕ y^m` when op is commutative.

This is the key lemma for expanding iterates of sums. Note that this is FALSE without
commutativity (noncommutative `op` does not distribute over iterated sums). -/
theorem iterate_op_op_distrib_of_comm (x y : α) (h_comm : ∀ a b : α, op a b = op b a) (m : ℕ) :
    iterate_op (op x y) m = op (iterate_op x m) (iterate_op y m) := by
  let _ : Monoid α := KnuthSkillingMonoidBase.toMonoid
  have hxy : Commute x y := h_comm x y
  change iterate_op (x * y) m = iterate_op x m * iterate_op y m
  simp only [iterate_op_eq_pow]
  exact hxy.mul_pow m

/-- Variant: op distributes over iterate_op in opposite order -/
theorem iterate_op_op_distrib_of_comm' (x y : α) (h_comm : ∀ a b : α, op a b = op b a) (m : ℕ) :
    op (iterate_op x m) (iterate_op y m) = iterate_op (op x y) m :=
  (iterate_op_op_distrib_of_comm x y h_comm m).symm

end Base

end KnuthSkillingAlgebra

/-- **Separation property (identity-free, semigroup version)**.
    For positive elements `a, x, y` with `x < y`, there exist `n, m ∈ ℕ+` such that
    `x^m < a^n ≤ y^m`. -/
def SeparationSemigroupProp [KSSemigroupBase α] : Prop :=
  ∀ {a x y : α}, IsPositive a → IsPositive x → IsPositive y → x < y →
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
               iterate_op_pnat a n ≤ iterate_op_pnat y m

/-- **Strict separation property (identity-free, semigroup version)**.
    For positive elements `a, x, y` with `x < y`, there exist `n, m ∈ ℕ+` such that
    `x^m < a^n < y^m` (strict on both sides). -/
def SeparationSemigroupStrictProp [KSSemigroupBase α] : Prop :=
  ∀ {a x y : α}, IsPositive a → IsPositive x → IsPositive y → x < y →
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
               iterate_op_pnat a n < iterate_op_pnat y m

/-- **KSSeparationSemigroup**: Identity-free version of the separation axiom.

Uses `IsPositive` instead of `ident < a` and `iterate_op_pnat` instead of `iterate_op`.
This works on `KSSemigroupBase` without requiring identity.

When identity exists, this is equivalent to `KSSeparation` (see theorems below). -/
class KSSeparationSemigroup (α : Type*) [KSSemigroupBase α] where
  /-- For any positive elements a, x, y with x < y, we can find exponents (n, m) ∈ ℕ+
      such that x^m < a^n ≤ y^m. -/
  separation : ∀ {a x y : α}, IsPositive a → IsPositive x → IsPositive y → x < y →
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
               iterate_op_pnat a n ≤ iterate_op_pnat y m

namespace KSSeparationSemigroup

variable {α : Type*} [KSSemigroupBase α] [KSSeparationSemigroup α]

/-- The `KSSeparationSemigroup` instance satisfies the unbundled `SeparationSemigroupProp` predicate. -/
theorem separationSemigroupProp : SeparationSemigroupProp (α := α) := KSSeparationSemigroup.separation

/-- Convenience: extraction of the separation property. -/
theorem sep {a x y : α} (ha : IsPositive a) (hx : IsPositive x) (hy : IsPositive y) (hxy : x < y) :
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
               iterate_op_pnat a n ≤ iterate_op_pnat y m :=
  KSSeparationSemigroup.separation ha hx hy hxy

end KSSeparationSemigroup

/-- **KSSeparationSemigroupStrict**: Identity-free version of the STRICT separation axiom.

This gives `x^m < a^n < y^m` (strict on both sides), which is needed for strict monotonicity
of Θ in the cuts construction.

When identity exists, this is equivalent to `KSSeparationStrict`. -/
class KSSeparationSemigroupStrict (α : Type*) [KSSemigroupBase α]
    extends KSSeparationSemigroup α where
  /-- For any positive elements a, x, y with x < y, we can find exponents (n, m) ∈ ℕ+
      such that x^m < a^n < y^m (strict on both sides). -/
  separation_strict : ∀ {a x y : α}, IsPositive a → IsPositive x → IsPositive y → x < y →
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
               iterate_op_pnat a n < iterate_op_pnat y m
  /-- `KSSeparationSemigroupStrict` implies `KSSeparationSemigroup` by weakening. -/
  separation := by
    intro a x y ha hx hy hxy
    rcases separation_strict ha hx hy hxy with ⟨n, m, hlt, hgt⟩
    exact ⟨n, m, hlt, le_of_lt hgt⟩

namespace KSSeparationSemigroupStrict

variable {α : Type*} [KSSemigroupBase α] [KSSeparationSemigroupStrict α]

/-- Convenience: extraction of the strict separation property. -/
theorem sep_strict {a x y : α} (ha : IsPositive a) (hx : IsPositive x) (hy : IsPositive y) (hxy : x < y) :
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
               iterate_op_pnat a n < iterate_op_pnat y m :=
  KSSeparationSemigroupStrict.separation_strict ha hx hy hxy

end KSSeparationSemigroupStrict

/-- **Separation property (identity-based version)**.
    For `ident < a`, `ident < x`, `ident < y` with `x < y`, there exist `n, m ∈ ℕ`
    with `0 < m` such that `x^m < a^n ≤ y^m`. -/
def SeparationProp [KnuthSkillingMonoidBase α] : Prop :=
  ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
      KnuthSkillingAlgebra.iterate_op a n ≤ KnuthSkillingAlgebra.iterate_op y m

/-- **Strict separation property (identity-based version)**.
    For `ident < a`, `ident < x`, `ident < y` with `x < y`, there exist `n, m ∈ ℕ`
    with `0 < m` such that `x^m < a^n < y^m` (strict on both sides). -/
def SeparationStrictProp [KnuthSkillingMonoidBase α] : Prop :=
  ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
      KnuthSkillingAlgebra.iterate_op a n < KnuthSkillingAlgebra.iterate_op y m

/-- **Negative separation property (identity-free, semigroup version)**.

This is the negative-cone analogue of `SeparationSemigroupProp`: for negative elements
`a, x, y` with `x < y`, some power of `a` can be sandwiched between powers of `x` and `y`.

We use `IsNegative` and ℕ+ iteration (`iterate_op_pnat`) so the statement makes sense without
an identity element. -/
def SeparationNegProp [KSSemigroupBase α] : Prop :=
  ∀ {a x y : α}, IsNegative a → IsNegative x → IsNegative y → x < y →
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
               iterate_op_pnat a n ≤ iterate_op_pnat y m

/-- **Bilateral separation property (identity-free, semigroup version)**.

Positive-side separation together with negative-side separation.
The mixed-sign “crossing” case is intentionally excluded: the rational-sandwich statement
is formulated cone-wise. -/
def SeparationBilateralProp [KSSemigroupBase α] : Prop :=
  SeparationSemigroupProp (α := α) ∧ SeparationNegProp (α := α)

theorem separationNegProp_of_identIsMinimum
    {α : Type*} [KnuthSkillingAlgebraBase α] :
    SeparationNegProp (α := α) := by
  intro a x y _ha hx _hy _hxy
  have hx_lt : x < ident := (isNegative_iff_lt_ident (a := x)).1 hx
  exact (False.elim (not_lt_of_ge (ident_le x) hx_lt))

theorem separationBilateralProp_iff_separationSemigroupProp_of_identIsMinimum
    {α : Type*} [KnuthSkillingAlgebraBase α] :
    SeparationBilateralProp (α := α) ↔ SeparationSemigroupProp (α := α) := by
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, separationNegProp_of_identIsMinimum (α := α)⟩

/-- **KSSeparation**: the iterate/power "sandwich" axiom.

Paper cross-reference:
- `paper/ks-formalization.tex`, Subsection “The Separation Property” and Subsection
  “The Separation Type Classes” (inside Section `sec:main`).

This is the statement that for any positive `a` and `ident < x < y`, there exist exponents `n,m`
with `0 < m` such that `x^m < a^n ≤ y^m`.

Important meta-fact (formalized):
`KSSeparation` is **not** derivable from the bare `KnuthSkillingAlgebra` axioms in general.
See the semidirect-product countermodel in
`KnuthSkilling/Additive/Counterexamples/KSSeparationNotDerivable.lean`.

Related files:
- `_archive/ProbabilityTheory/KnuthSkilling/Separation/Derivation.lean`
  explores additional structured hypotheses under which `KSSeparation` *can* be derived. -/

class KSSeparation (α : Type*) [KnuthSkillingMonoidBase α] where
  /-- For any positive x < y and any base a > ident, we can find exponents (n, m)
  such that x^m < a^n ≤ y^m. This is the key property enabling representation. -/
  separation : ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
      KnuthSkillingAlgebra.iterate_op a n ≤ KnuthSkillingAlgebra.iterate_op y m

/-- **KSSeparationBilateral**: `KSSeparation` plus the corresponding negative-side sandwich.

This is an *optional* strengthening that is useful when working without the
probability-theory assumption that `ident` is the minimum element.

In the probability setting (`[KnuthSkillingAlgebraBase α]`), the extra field is vacuous, so
`KSSeparationBilateral` is equivalent in strength to `KSSeparation`. -/
class KSSeparationBilateral (α : Type*) [KnuthSkillingMonoidBase α] : Prop extends KSSeparation α where
  /-- Negative-side sandwich: `SeparationNegProp`. -/
  separation_neg : SeparationNegProp (α := α)

namespace KSSeparationBilateral

variable {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparationBilateral α]

theorem separationNegProp : SeparationNegProp (α := α) :=
  KSSeparationBilateral.separation_neg

theorem separationBilateralProp : SeparationBilateralProp (α := α) :=
by
  classical
  refine ⟨?_, KSSeparationBilateral.separation_neg⟩
  intro a x y ha hx hy hxy
  have ha' : ident < a := (isPositive_iff_ident_lt a).1 ha
  have hx' : ident < x := (isPositive_iff_ident_lt x).1 hx
  have hy' : ident < y := (isPositive_iff_ident_lt y).1 hy
  obtain ⟨n, m, hm_pos, h_lo, h_hi⟩ := KSSeparation.separation ha' hx' hy' hxy
  by_cases hn : n = 0
  · -- n = 0: contradiction since `x^m < ident` is impossible for positive `x`.
    exfalso
    simp only [hn, KnuthSkillingAlgebra.iterate_op_zero] at h_lo
    have hxm_pos : ident < KnuthSkillingAlgebra.iterate_op x m :=
      KnuthSkillingAlgebra.iterate_op_pos x hx' m hm_pos
    exact not_lt.mpr (le_of_lt hxm_pos) h_lo
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    let n' : ℕ+ := ⟨n, hn_pos⟩
    let m' : ℕ+ := ⟨m, hm_pos⟩
    have hx_eq : iterate_op_pnat x m' = KnuthSkillingAlgebra.iterate_op x m :=
      KnuthSkillingAlgebra.iterate_op_pnat_eq x m'
    have ha_eq : iterate_op_pnat a n' = KnuthSkillingAlgebra.iterate_op a n :=
      KnuthSkillingAlgebra.iterate_op_pnat_eq a n'
    have hy_eq : iterate_op_pnat y m' = KnuthSkillingAlgebra.iterate_op y m :=
      KnuthSkillingAlgebra.iterate_op_pnat_eq y m'
    refine ⟨n', m', ?_, ?_⟩
    · simpa [hx_eq, ha_eq] using h_lo
    · simpa [ha_eq, hy_eq] using h_hi

end KSSeparationBilateral

theorem ksSeparationBilateral_of_ksSeparation
    {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α] :
    KSSeparationBilateral α :=
  { toKSSeparation := ‹KSSeparation α›
    separation_neg := separationNegProp_of_identIsMinimum (α := α) }

namespace KSSeparation

open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparation α]

/-- The `KSSeparation` instance satisfies the unbundled `SeparationProp` predicate. -/
theorem separationProp : SeparationProp (α := α) := KSSeparation.separation

/-- Strengthening of `KSSeparation.separation`: we can request an arbitrarily large exponent `m`.

This follows by applying `separation` to `x^(N+1) < y^(N+1)` and unfolding with `iterate_op_mul`. -/
theorem separation_large_m {a x y : α} (ha : ident < a) (hx : ident < x) (hy : ident < y) (hxy : x < y)
    (N : ℕ) :
    ∃ n m : ℕ, N < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  classical
  set p : ℕ := N + 1
  have hp_pos : 0 < p := Nat.succ_pos N
  have hx_p : ident < iterate_op x p := iterate_op_pos x hx p hp_pos
  have hy_p : ident < iterate_op y p := iterate_op_pos y hy p hp_pos
  have hxy_p : iterate_op x p < iterate_op y p := iterate_op_strictMono_base p hp_pos x y hxy
  rcases (KSSeparation.separation (a := a) (x := iterate_op x p) (y := iterate_op y p) ha hx_p hy_p hxy_p) with
    ⟨n, m₁, hm₁_pos, h_gap, h_in⟩
  refine ⟨n, p * m₁, ?_, ?_, ?_⟩
  · -- N < p * m₁
    have hp_lt : N < p := Nat.lt_succ_self N
    have hm₁_pos' : 0 < m₁ := hm₁_pos
    have : p ≤ p * m₁ := Nat.le_mul_of_pos_right p hm₁_pos'
    exact lt_of_lt_of_le hp_lt this
  · -- unfold the left inequality
    simpa [iterate_op_mul, Nat.mul_assoc] using h_gap
  · -- unfold the right inequality
    simpa [iterate_op_mul, Nat.mul_assoc] using h_in

/-- A convenient “one-sided commensurability” corollary of `KSSeparation`:
for any positive base `a` and positive element `x`, some power of `a` sits above a power of `x`
and below a *square-power* of `x`.

This is the schematic inequality `x^m < a^n ≤ (x⊕x)^m = x^(2m)` that mimics the fact that
`log_a(x)` lies in some rational interval of width `1`. -/
theorem separation_between_self_and_square {a x : α} (ha : ident < a) (hx : ident < x) :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op x (2 * m) := by
  have hx2 : ident < iterate_op x 2 := iterate_op_pos x hx 2 (by decide)
  have hx_lt_x2 : x < iterate_op x 2 := by
    simpa [iterate_op_one] using (iterate_op_strictMono x hx (by decide : (1 : ℕ) < 2))
  rcases KSSeparation.separation (a := a) (x := x) (y := iterate_op x 2) ha hx hx2 hx_lt_x2 with
    ⟨n, m, hm_pos, hlt, hle⟩
  refine ⟨n, m, hm_pos, hlt, ?_⟩
  simpa [iterate_op_mul, Nat.mul_assoc] using hle

end KSSeparation

/-- **KSSeparationStrict**: strengthen `KSSeparation` by making the upper bound strict.

Paper cross-reference:
- `paper/ks-formalization.tex`, Subsection “The Separation Type Classes” (Section `sec:main`).
- The informal “density implies strict separation” remark corresponds to
  `KSSeparation.toKSSeparationStrict_of_denselyOrdered` below. -/
class KSSeparationStrict (α : Type*) [KnuthSkillingMonoidBase α] extends KSSeparation α where
  /-- For any positive `x < y` and any base `a > ident`, find exponents `(n,m)` with `0 < m` and
  `x^m < a^n < y^m`. -/
  separation_strict : ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
      KnuthSkillingAlgebra.iterate_op a n < KnuthSkillingAlgebra.iterate_op y m
  /-- `KSSeparationStrict` implies `KSSeparation` by weakening the strict upper bound. -/
  separation := by
    intro a x y ha hx hy hxy
    rcases separation_strict (a := a) (x := x) (y := y) ha hx hy hxy with
      ⟨n, m, hm_pos, hlt, hgt⟩
    exact ⟨n, m, hm_pos, hlt, le_of_lt hgt⟩

namespace KSSeparationStrict

open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparationStrict α]

end KSSeparationStrict

namespace KSSeparation

open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparation α]

/-- If we can pick an intermediate point between any `ident < x < y`, then `KSSeparation` upgrades to
the strict variant `KSSeparationStrict`.

This is a weaker hypothesis than `[DenselyOrdered α]`: we only need density *above* `ident`, since
`KSSeparation` is only stated for positive `x,y`. -/
theorem toKSSeparationStrict_of_exists_between_pos
    (hBetween : ∀ {x y : α}, ident < x → x < y → ∃ z, x < z ∧ z < y) :
    KSSeparationStrict α := by
  classical
  refine ⟨?_⟩
  intro a x y ha hx hy hxy
  rcases hBetween (x := x) (y := y) hx hxy with ⟨z, hxz, hzy⟩
  have hz : ident < z := lt_trans hx hxz
  rcases (KSSeparation.separation (a := a) (x := x) (y := z) ha hx hz hxz) with
    ⟨n, m, hm_pos, hlt, hle⟩
  have hz_lt_y : iterate_op z m < iterate_op y m :=
    iterate_op_strictMono_base m hm_pos z y hzy
  have hlt' : iterate_op a n < iterate_op y m := lt_of_le_of_lt hle hz_lt_y
  exact ⟨n, m, hm_pos, hlt, hlt'⟩

/-- If the order on `α` is dense, then `KSSeparation` upgrades to the strict variant
`KSSeparationStrict`.

Paper cross-reference:
- `paper/ks-formalization.tex`, listing “Density implies strict separation” in Subsection
  “The Separation Type Classes” (Section `sec:main`).

This isolates an extra hypothesis that suffices to rule out the “upper-bound equality” corner case:
pick `z` with `x < z < y`, apply separation to `(x,z)`, then use `z^m < y^m` to make the upper
bound strict. -/
theorem toKSSeparationStrict_of_denselyOrdered [DenselyOrdered α] : KSSeparationStrict α := by
  exact
    toKSSeparationStrict_of_exists_between_pos (α := α)
      (hBetween := fun {x y} _hx hxy => exists_between hxy)

end KSSeparation

section SeparationEquivalence

open KnuthSkillingMonoidBase KnuthSkillingAlgebra

/-- `KSSeparation` implies `KSSeparationSemigroup` when identity exists.
    This is the easy direction: ident < a ↔ IsPositive a, and iterate_op restricted to ℕ+. -/
instance KSSeparationSemigroup_of_KSSeparation {α : Type*} [KnuthSkillingMonoidBase α]
    [KSSeparation α] : KSSeparationSemigroup α where
  separation := by
    intro a x y ha hx hy hxy
    have ha' : ident < a := (isPositive_iff_ident_lt a).mp ha
    have hx' : ident < x := (isPositive_iff_ident_lt x).mp hx
    have hy' : ident < y := (isPositive_iff_ident_lt y).mp hy
    obtain ⟨n, m, hm_pos, h_lo, h_hi⟩ := KSSeparation.separation ha' hx' hy' hxy
    by_cases hn : n = 0
    · -- n = 0 case: contradiction since iterate_op a 0 = ident and x^m < ident is impossible
      exfalso
      simp only [hn, iterate_op_zero] at h_lo
      have hxm_pos : ident < iterate_op x m := iterate_op_pos x hx' m hm_pos
      exact not_lt.mpr (le_of_lt hxm_pos) h_lo
    · -- n > 0 case: can convert to ℕ+
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      use ⟨n, hn_pos⟩, ⟨m, hm_pos⟩
      have h1 : iterate_op_pnat x ⟨m, hm_pos⟩ = iterate_op x m := iterate_op_pnat_eq x ⟨m, hm_pos⟩
      have h2 : iterate_op_pnat a ⟨n, hn_pos⟩ = iterate_op a n := iterate_op_pnat_eq a ⟨n, hn_pos⟩
      have h3 : iterate_op_pnat y ⟨m, hm_pos⟩ = iterate_op y m := iterate_op_pnat_eq y ⟨m, hm_pos⟩
      rw [h1, h2, h3]
      exact ⟨h_lo, h_hi⟩

/-- `KSSeparationStrict` implies `KSSeparationSemigroupStrict` when identity exists.

This is the strict analogue of `KSSeparationSemigroup_of_KSSeparation`.

The key technical point is that the strict sandwich condition forces the exponent `n` on the
base `a` to be positive: if `n = 0`, then `a^n = ident` and the lower strict inequality
`x^m < a^n` would contradict `ident < x^m` for positive `x`. -/
instance KSSeparationSemigroupStrict_of_KSSeparationStrict {α : Type*} [KnuthSkillingMonoidBase α]
    [KSSeparationStrict α] : KSSeparationSemigroupStrict α where
  separation_strict := by
    intro a x y ha hx hy hxy
    have ha' : ident < a := (isPositive_iff_ident_lt a).mp ha
    have hx' : ident < x := (isPositive_iff_ident_lt x).mp hx
    have hy' : ident < y := (isPositive_iff_ident_lt y).mp hy
    obtain ⟨n, m, hm_pos, h_lo, h_hi⟩ :=
      KSSeparationStrict.separation_strict (α := α) (a := a) (x := x) (y := y) ha' hx' hy' hxy
    by_cases hn : n = 0
    · subst hn
      have hxm_pos : ident < iterate_op x m := iterate_op_pos x hx' m hm_pos
      have : ¬ iterate_op x m < ident := not_lt.mpr (le_of_lt hxm_pos)
      exfalso
      simpa [iterate_op_zero] using this h_lo
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      let m' : ℕ+ := ⟨m, hm_pos⟩
      let n' : ℕ+ := ⟨n, hn_pos⟩
      have hx_eq : iterate_op_pnat x m' = iterate_op x m := iterate_op_pnat_eq x m'
      have ha_eq : iterate_op_pnat a n' = iterate_op a n := iterate_op_pnat_eq a n'
      have hy_eq : iterate_op_pnat y m' = iterate_op y m := iterate_op_pnat_eq y m'
      refine ⟨n', m', ?_, ?_⟩
      · simpa [hx_eq, ha_eq] using h_lo
      · simpa [ha_eq, hy_eq] using h_hi

/-- `KSSeparationSemigroup` implies `KSSeparation` when identity exists.
    This is the converse: we convert ℕ+ back to ℕ. -/
theorem KSSeparation_of_KSSeparationSemigroup {α : Type*} [KnuthSkillingMonoidBase α]
    [KSSeparationSemigroup α] : KSSeparation α where
  separation := by
    intro a x y ha hx hy hxy
    have ha' : IsPositive a := (isPositive_iff_ident_lt a).mpr ha
    have hx' : IsPositive x := (isPositive_iff_ident_lt x).mpr hx
    have hy' : IsPositive y := (isPositive_iff_ident_lt y).mpr hy
    obtain ⟨n, m, h_lo, h_hi⟩ := KSSeparationSemigroup.sep ha' hx' hy' hxy
    use n.val, m.val, m.pos
    have h1 : iterate_op x m.val = iterate_op_pnat x m := (iterate_op_pnat_eq x m).symm
    have h2 : iterate_op a n.val = iterate_op_pnat a n := (iterate_op_pnat_eq a n).symm
    have h3 : iterate_op y m.val = iterate_op_pnat y m := (iterate_op_pnat_eq y m).symm
    rw [h1, h2, h3]
    exact ⟨h_lo, h_hi⟩

/-- `KSSeparationSemigroupStrict` implies `KSSeparationStrict` when identity exists.

This is the converse of `KSSeparationSemigroupStrict_of_KSSeparationStrict`.
We convert `ident <` hypotheses to `IsPositive`, apply the identity-free strict sandwich axiom,
and then translate back from `ℕ+` iteration to the identity-based `iterate_op`. -/
theorem KSSeparationStrict_of_KSSeparationSemigroupStrict {α : Type*} [KnuthSkillingMonoidBase α]
    [KSSeparationSemigroupStrict α] : KSSeparationStrict α where
  separation := KSSeparation.separation (self := KSSeparation_of_KSSeparationSemigroup)
  separation_strict := by
    intro a x y ha hx hy hxy
    have ha' : IsPositive a := (isPositive_iff_ident_lt a).mpr ha
    have hx' : IsPositive x := (isPositive_iff_ident_lt x).mpr hx
    have hy' : IsPositive y := (isPositive_iff_ident_lt y).mpr hy
    obtain ⟨n, m, h_lo, h_hi⟩ :=
      KSSeparationSemigroupStrict.sep_strict (a := a) (x := x) (y := y) ha' hx' hy' hxy
    refine ⟨n.val, m.val, m.pos, ?_, ?_⟩
    ·
      have hx_eq : iterate_op x m.val = iterate_op_pnat x m := (iterate_op_pnat_eq x m).symm
      have ha_eq : iterate_op a n.val = iterate_op_pnat a n := (iterate_op_pnat_eq a n).symm
      simpa [hx_eq, ha_eq] using h_lo
    ·
      have ha_eq : iterate_op a n.val = iterate_op_pnat a n := (iterate_op_pnat_eq a n).symm
      have hy_eq : iterate_op y m.val = iterate_op_pnat y m := (iterate_op_pnat_eq y m).symm
      simpa [ha_eq, hy_eq] using h_hi
end SeparationEquivalence

end KnuthSkilling

namespace KnuthSkilling

open KSSemigroupBase KnuthSkillingMonoidBase
open KnuthSkillingAlgebra

namespace KSSemigroupBase

variable {α : Type*} [KSSemigroupBase α]

/-- `x` and `y` commute with respect to `KnuthSkillingAlgebraBase.op`. -/
def Commutes (x y : α) : Prop :=
  op x y = op y x

namespace Commutes

theorem symm {x y : α} (h : Commutes (α := α) x y) : Commutes (α := α) y x := by
  dsimp [Commutes] at h ⊢
  exact h.symm

theorem refl (x : α) : Commutes (α := α) x x :=
  rfl

/-- If `x` commutes with `y` and `z`, then it commutes with `y ⊕ z`. -/
theorem op_right {x y z : α} (hxy : Commutes (α := α) x y) (hxz : Commutes (α := α) x z) :
    Commutes (α := α) x (op y z) := by
  let _ : Semigroup α := KSSemigroupBase.toSemigroup
  exact (show Commute x y from hxy).mul_right (show Commute x z from hxz)

/-- If `y` commutes with `x` and `z`, then `y ⊕ z` commutes with `x`. -/
theorem op_left {x y z : α} (hyx : Commutes (α := α) y x) (hzx : Commutes (α := α) z x) :
    Commutes (α := α) (op y z) x := by
  exact (op_right (α := α) (x := x) (y := y) (z := z) hyx.symm hzx.symm).symm

end Commutes

/-- The set of elements commuting with a fixed `x`. -/
def centralizer (x : α) : Set α :=
  {y : α | Commutes (α := α) x y}

namespace centralizer

theorem mem_iff {x y : α} : y ∈ centralizer (α := α) x ↔ Commutes (α := α) x y := by
  rfl

theorem closed_op {x y z : α} (hy : y ∈ centralizer (α := α) x) (hz : z ∈ centralizer (α := α) x) :
    op y z ∈ centralizer (α := α) x :=
  Commutes.op_right (α := α) (x := x) (y := y) (z := z) hy hz

end centralizer

end KSSemigroupBase

section WithIdentity

open KnuthSkillingMonoidBase

variable {α : Type*} [KnuthSkillingMonoidBase α]

namespace KSSemigroupBase.Commutes

theorem ident_left (x : α) : KSSemigroupBase.Commutes (α := α) ident x := by
  simp [KSSemigroupBase.Commutes, op_ident_left, op_ident_right]

theorem ident_right (x : α) : KSSemigroupBase.Commutes (α := α) x ident := by
  simp [KSSemigroupBase.Commutes, op_ident_left, op_ident_right]

end KSSemigroupBase.Commutes

namespace KSSemigroupBase.centralizer

theorem ident_mem (x : α) : ident ∈ KSSemigroupBase.centralizer (α := α) x :=
  KSSemigroupBase.Commutes.ident_right (α := α) x

end KSSemigroupBase.centralizer

end WithIdentity

end KnuthSkilling
