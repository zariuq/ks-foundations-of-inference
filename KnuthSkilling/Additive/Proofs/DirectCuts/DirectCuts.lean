/-
# Rational cuts for ordered combination

`cutSet` uses natural exponents, including a zero numerator. `cutSet_pnat`
uses positive-natural exponents and needs no identity. Their independent
readouts agree on positive elements: the former cut set adds exactly zero.
Thus one positive-natural argument supplies additivity and strictness, with
ordinary identity cases treated separately.

Power laws reuse the supplied semigroup/monoid iteration. The construction
uses sandwich separation; commutativity is derived in the minimum-identity
route and supplied explicitly for positive-only semigroups. The characterization
`Θ_cuts_eq_div_of_representation` compares any supplied faithful additive map
with the independent cuts after calibrating at the same positive anchor.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.Basic
import KnuthSkilling.Core.Algebra
import KnuthSkilling.Additive.Representation
import KnuthSkilling.Additive.Axioms.SandwichSeparation
import KnuthSkilling.Additive.Proofs.GridInduction.Core.SeparationImpliesCommutative

namespace KnuthSkilling.Additive.Proofs.DirectCuts

open Classical
-- Bring the K&S operation/identity projections into scope (`op`, `ident`, etc.).
-- Without this, `op` resolves to unrelated Mathlib identifiers (e.g. Opposite), and the file breaks.
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open scoped Pointwise

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α]

/-!
## §1: Commutativity from Separation (imported)

We use the already-proven fact that KSSeparation implies commutativity.
-/

/-- Commutativity follows from KSSeparation. -/
theorem op_comm' : ∀ x y : α, op x y = op y x :=
  fun x y =>
    KnuthSkilling.Additive.Proofs.GridInduction.Core.op_comm_of_KSSeparation
      (α := α) x y

/-!
## §2: Iteration and Power Notation

We define convenient notation for iterating the operation.
-/

/-- n-fold iteration: x^n = x ⊕ x ⊕ ... ⊕ x (n times), with x^0 = ident -/
def pow' (x : α) : ℕ → α
  | 0 => ident
  | n + 1 => op x (pow' x n)

omit [KSSeparation α] in
theorem iterate_op_eq_pow' (x : α) (n : ℕ) : KnuthSkillingAlgebra.iterate_op x n = pow' x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [KnuthSkillingAlgebra.iterate_op, pow', ih]

omit [KSSeparation α] in
@[simp]
theorem pow'_zero (x : α) : pow' x 0 = ident := rfl

omit [KSSeparation α] in
@[simp]
theorem pow'_one (x : α) : pow' x 1 = x := op_ident_right x

omit [KSSeparation α] in
@[simp]
theorem pow'_succ (x : α) (n : ℕ) : pow' x (n + 1) = op x (pow' x n) := rfl

omit [KSSeparation α] in
/-- Power is additive: x^(m+n) = x^m ⊕ x^n -/
theorem pow'_add (x : α) (m n : ℕ) : pow' x (m + n) = op (pow' x m) (pow' x n) := by
  simpa only [← iterate_op_eq_pow'] using (KnuthSkillingAlgebra.iterate_op_add x m n).symm

omit [KSSeparation α] in
/-- Power is strictly monotone in the exponent when x > ident -/
theorem pow'_strictMono_exp {x : α} (hx : ident < x) : StrictMono (pow' x) := by
  intro m n h
  simpa only [← iterate_op_eq_pow'] using KnuthSkillingAlgebra.iterate_op_strictMono x hx h

omit [KSSeparation α] in
/-- Power is strictly monotone in the base for positive exponents -/
theorem pow'_strictMono_base {x y : α} (hxy : x < y) (n : ℕ) (hn : 0 < n) :
    pow' x n < pow' y n := by
  simpa only [← iterate_op_eq_pow'] using KnuthSkillingAlgebra.iterate_op_strictMono_base n hn x y hxy

omit [KSSeparation α] in
/-- Power is monotone in the base -/
theorem pow'_mono_base {x y : α} (hxy : x ≤ y) (n : ℕ) (_hn : 0 < n) :
    pow' x n ≤ pow' y n := by
  simpa only [← iterate_op_eq_pow'] using KnuthSkillingAlgebra.iterate_op_mono_base n x y hxy

omit [KSSeparation α] in
/-- Power of ident is always ident -/
theorem pow'_ident (n : ℕ) : pow' (ident : α) n = ident := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow'_succ, op_ident_left, ih]

/-!
## §3: The Cut Set Definition

For a fixed base `a > ident` and element `x`, define the "cut set" of rationals
that represent lower bounds for Θ(x)/Θ(a).
-/

/-- The cut set: rationals m/n such that pow' a m ≤ pow' x n (when n > 0) -/
def cutSet (a : α) (x : α) : Set ℚ :=
  { q : ℚ | 0 ≤ q ∧ ∃ (m n : ℕ), n > 0 ∧ q = m / n ∧ pow' a m ≤ pow' x n }

omit [KSSeparation α] in
/-- The cut set is nonempty (contains 0) when x ≥ ident -/
theorem cutSet_nonempty (a : α) (x : α) (hx : ident ≤ x) :
    (cutSet a x).Nonempty := by
  use 0
  simp only [cutSet, Set.mem_ofPred_eq]
  refine ⟨le_refl 0, 0, 1, Nat.one_pos, ?_, ?_⟩
  · simp
  · simp only [pow'_zero, pow'_one]; exact hx

omit [KSSeparation α] in
/-- Power multiplication follows from associativity, without commutativity. -/
theorem pow'_mul (x : α) (m n : ℕ) : pow' (pow' x m) n = pow' x (m * n) := by
  simpa only [← iterate_op_eq_pow'] using KnuthSkillingAlgebra.iterate_op_mul x m n

omit [KSSeparation α] in
/-- Power is monotone in exponent (non-strict) when x ≥ ident -/
theorem pow'_mono_exp {x : α} (hx : ident ≤ x) : Monotone (pow' x) := by
  intro m n hmn
  rcases hx.lt_or_eq with hx_lt | hx_eq
  · -- x > ident: use strict monotonicity
    rcases hmn.lt_or_eq with hmn_lt | hmn_eq
    · exact le_of_lt (pow'_strictMono_exp hx_lt hmn_lt)
    · rw [hmn_eq]
  · -- x = ident: pow' ident n = ident for all n
    rw [← hx_eq]
    simp only [pow'_ident, le_refl]

omit [KSSeparation α] in
/-- Relationship between Function.iterate and pow': f^[n] x = pow' x (n + 1) when f = op x -/
theorem iterate_eq_pow'_succ (x : α) (n : ℕ) :
    (op x)^[n] x = pow' x (n + 1) := by
  simpa only [← iterate_op_eq_pow'] using KnuthSkillingAlgebra.nat_iterate_eq_iterate_op_succ x n

/-- Key lemma: pow' x n < pow' a (k * n) when x < pow' a k -/
theorem pow'_lt_pow'_mul {a x : α} {k : ℕ} (_ha : ident < a) (hx : x < pow' a k) (n : ℕ) (hn : 0 < n) :
    pow' x n < pow' a (k * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [pow'_succ, Nat.mul_succ]
    rw [pow'_add]
    by_cases hn' : n = 0
    · simp only [hn', Nat.mul_zero, pow'_zero, op_ident_left, op_ident_right]
      exact hx
    · have hn'' : 0 < n := Nat.pos_of_ne_zero hn'
      calc op x (pow' x n) < op x (pow' a (k * n)) := op_strictMono_right x (ih hn'')
        _ < op (pow' a k) (pow' a (k * n)) := op_strictMono_left (pow' a (k * n)) hx
        _ = op (pow' a (k * n)) (pow' a k) := op_comm' _ _

/-- The cut set is bounded above (uses Archimedean property, derived from KSSeparation) -/
theorem cutSet_bddAbove (a : α) (ha : ident < a) (x : α) : BddAbove (cutSet a x) := by
  -- By Archimedean (derived from KSSeparation), ∃ N such that x < (op a)^[N] a = pow' a (N + 1)
  obtain ⟨N, hN⟩ := SandwichSeparation.SeparationToArchimedean.op_archimedean_of_separation a x ha
  rw [iterate_eq_pow'_succ] at hN
  -- Use N + 1 as upper bound
  use (N + 1 : ℕ)
  intro q hq
  simp only [cutSet, Set.mem_ofPred_eq] at hq
  obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
  -- Need to show: m/n ≤ N + 1
  rw [hq_eq]
  by_cases hm : m = 0
  · simp only [hm, Nat.cast_zero, zero_div]
    exact Nat.cast_nonneg _
  · -- m > 0, prove by contradiction
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    by_contra h_gt
    push Not at h_gt
    -- h_gt : (N + 1 : ℚ) < m / n
    -- So m > (N+1) * n, i.e., (N + 1) * n < m
    have h1 : (N + 1) * n < m := by
      have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
      have hcast : ((N + 1) * n : ℚ) < m := by
        calc ((N + 1) * n : ℚ) = (N + 1 : ℕ) * n := by norm_cast
          _ < (m / n) * n := by
              apply mul_lt_mul_of_pos_right h_gt
              exact Nat.cast_pos.mpr hn
          _ = m := div_mul_cancel₀ (m : ℚ) hn_ne
      exact_mod_cast hcast
    -- pow' a m > pow' a ((N+1)*n) since a > ident
    have h2 : pow' a ((N + 1) * n) < pow' a m := pow'_strictMono_exp ha h1
    -- pow' x n < pow' a ((N+1) * n) by the key lemma
    have h3 : pow' x n < pow' a ((N + 1) * n) := pow'_lt_pow'_mul ha hN n hn
    -- Contradiction: pow' a m ≤ pow' x n < pow' a ((N+1)*n) < pow' a m
    have h4 : pow' x n < pow' a m := lt_trans h3 h2
    exact not_lt.mpr ham_le h4

/-!
## §4: Definition of Θ via Supremum

Define Θ(x) as the supremum of the cut set.
-/

/-- The representation map Θ defined via cut supremum -/
noncomputable def Θ_cuts (a : α) (_ha : ident < a) (x : α) : ℝ :=
  if _hx : ident ≤ x then
    sSup ((↑) '' cutSet a x : Set ℝ)
  else
    0

omit [KSSeparation α] in
/-- Θ(ident) = 0 -/
theorem Θ_cuts_ident (a : α) (ha : ident < a) : Θ_cuts a ha ident = 0 := by
  simp only [Θ_cuts, le_refl, dite_true]
  -- cutSet of ident is {0} because pow' a m ≤ pow' ident n = ident forces m = 0
  have h_cutSet : cutSet a ident = {0} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · -- 0 ∈ cutSet a ident
      simp only [cutSet, Set.mem_ofPred_eq]
      refine ⟨le_refl 0, 0, 1, Nat.one_pos, by norm_num, ?_⟩
      -- pow' a 0 = ident and pow' ident 1 = ident, so we need ident ≤ ident
      rw [pow'_zero, pow'_one]
    · -- uniqueness: q ∈ cutSet a ident → q = 0
      intro q hq
      simp only [cutSet, Set.mem_ofPred_eq] at hq
      obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
      by_cases hm : m = 0
      · simp only [hq_eq, hm, Nat.cast_zero, zero_div]
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h1 : ident < pow' a m := pow'_strictMono_exp ha hm_pos
        have h2 : pow' (ident : α) n = ident := pow'_ident n
        rw [h2] at ham_le
        exact absurd (lt_of_lt_of_le h1 ham_le) (lt_irrefl ident)
  rw [h_cutSet]
  simp only [Set.image_singleton]
  norm_cast
  exact csSup_singleton 0

omit [KSSeparation α] in
/-- For the base element, cutSet characterization: q ∈ cutSet a a ↔ 0 ≤ q ≤ 1 -/
theorem cutSet_base_subset_unit_interval (a : α) (ha : ident < a) :
    cutSet a a ⊆ {q : ℚ | 0 ≤ q ∧ q ≤ 1} := by
  intro q hq
  simp only [cutSet, Set.mem_ofPred_eq] at hq
  obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
  simp only [Set.mem_ofPred_eq]
  constructor
  · exact hq_nonneg
  · -- Need: m/n ≤ 1, i.e., m ≤ n
    rw [hq_eq]
    rw [div_le_one (by exact_mod_cast hn : (0 : ℚ) < n)]
    -- pow' a m ≤ pow' a n implies m ≤ n by strict monotonicity
    by_contra h_gt
    push Not at h_gt
    have h_gt' : n < m := by exact_mod_cast h_gt
    have h : pow' a n < pow' a m := pow'_strictMono_exp ha h_gt'
    exact not_lt.mpr ham_le h

omit [KSSeparation α] in
/-- For the base element, unit interval subset of cutSet -/
theorem unit_interval_subset_cutSet_base (a : α) (ha : ident < a) :
    {q : ℚ | 0 ≤ q ∧ q ≤ 1} ⊆ cutSet a a := by
  intro q hq
  simp only [Set.mem_ofPred_eq] at hq
  obtain ⟨hq_nonneg, hq_le_one⟩ := hq
  simp only [cutSet, Set.mem_ofPred_eq]
  constructor
  · exact hq_nonneg
  · -- Use the numerator and denominator of q
    use q.num.toNat, q.den
    constructor
    · exact q.den_pos
    · constructor
      · -- q = q.num.toNat / q.den when q ≥ 0
        have h_num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
        have h_eq : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg h_num_nonneg
        -- Show q = q.num.toNat / q.den
        have hkey : (q.num.toNat : ℚ) = q.num := by exact_mod_cast h_eq
        rw [hkey]
        exact (Rat.num_div_den q).symm
      · -- pow' a q.num.toNat ≤ pow' a q.den because q.num.toNat ≤ q.den
        apply pow'_mono_exp (le_of_lt ha)
        -- Need: q.num.toNat ≤ q.den, which follows from q ≤ 1
        have h_num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
        have h_eq : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg h_num_nonneg
        -- q.num ≤ q.den from q ≤ 1
        have h_le : q.num ≤ q.den := by
          have h1 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
          have h2 : q * q.den ≤ 1 * q.den := by
            apply mul_le_mul_of_nonneg_right hq_le_one
            exact_mod_cast q.den_pos.le
          simp only [one_mul] at h2
          have h3 : (q.num : ℚ) ≤ q.den := by linarith
          exact_mod_cast h3
        -- q.num.toNat ≤ q.den follows from q.num ≤ q.den (since q.num ≥ 0)
        have h_nat : q.num.toNat ≤ q.den := by
          have hcast : (q.num.toNat : ℤ) ≤ q.den := by
            rw [h_eq]
            exact h_le
          omega
        exact h_nat

omit [KSSeparation α] in
/-- cutSet of base element equals unit interval -/
theorem cutSet_base_eq (a : α) (ha : ident < a) :
    cutSet a a = {q : ℚ | 0 ≤ q ∧ q ≤ 1} :=
  Set.eq_of_subset_of_subset (cutSet_base_subset_unit_interval a ha) (unit_interval_subset_cutSet_base a ha)

/-- Supremum of [0,1] ∩ ℚ (cast to ℝ) equals 1 -/
theorem sSup_rat_unit_interval :
    sSup ((↑) '' {q : ℚ | 0 ≤ q ∧ q ≤ 1} : Set ℝ) = 1 := by
  apply le_antisymm
  · -- sSup ≤ 1: all elements are ≤ 1
    apply csSup_le
    · use (0 : ℝ)
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      exact ⟨0, ⟨le_refl 0, zero_le_one⟩, Rat.cast_zero⟩
    · intro r hr
      simp only [Set.mem_image, Set.mem_ofPred_eq] at hr
      obtain ⟨q, ⟨_, hq_le⟩, rfl⟩ := hr
      exact_mod_cast hq_le
  · -- 1 ≤ sSup: 1 is in the set
    apply le_csSup
    · -- Bounded above by 1
      use 1
      intro r hr
      simp only [Set.mem_image, Set.mem_ofPred_eq] at hr
      obtain ⟨q, ⟨_, hq_le⟩, rfl⟩ := hr
      exact_mod_cast hq_le
    · -- 1 is in the image (1 = (1 : ℚ) cast to ℝ)
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      exact ⟨1, ⟨zero_le_one, le_refl 1⟩, Rat.cast_one⟩

omit [KSSeparation α] in
/-- Θ(a) = 1 (the base element maps to 1) -/
theorem Θ_cuts_base (a : α) (ha : ident < a) : Θ_cuts a ha a = 1 := by
  simp only [Θ_cuts, le_of_lt ha, dite_true]
  rw [cutSet_base_eq a ha]
  exact sSup_rat_unit_interval

/-!
## §5: Order Preservation

The key property: x ≤ y ↔ Θ(x) ≤ Θ(y)
-/

/-- Forward direction: x ≤ y → Θ(x) ≤ Θ(y) -/
theorem Θ_cuts_mono (a : α) (ha : ident < a) {x y : α} (hxy : x ≤ y) :
    Θ_cuts a ha x ≤ Θ_cuts a ha y := by
  simp only [Θ_cuts]
  have hx : ident ≤ x := ident_le x
  have hy : ident ≤ y := ident_le y
  simp only [hx, hy, dite_true]
  -- cutSet x ⊆ cutSet y
  apply csSup_le_csSup
  · -- cutSet y is bounded above (image version)
    have hbdd : BddAbove (cutSet a y) := cutSet_bddAbove a ha y
    obtain ⟨B, hB⟩ := hbdd
    use B
    intro r hr
    simp only [Set.mem_image] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact Rat.cast_le.mpr (hB hq)
  · exact Set.image_nonempty.mpr (cutSet_nonempty a x hx)
  · intro r hr
    simp only [Set.mem_image] at hr ⊢
    obtain ⟨q, hq, rfl⟩ := hr
    use q
    simp only [cutSet, Set.mem_ofPred_eq] at hq ⊢
    obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
    constructor
    · exact ⟨hq_nonneg, m, n, hn, hq_eq, le_trans ham_le (pow'_mono_base hxy n hn)⟩
    · trivial

/-! The remaining rational-cut bounds use the same supplied iteration. Strict
separation is needed only for strict order reflection, not for additivity. -/

section Standalone

omit [KSSeparation α] in
theorem pow'_eq_iterate_op (x : α) (n : ℕ) : pow' x n = KnuthSkillingAlgebra.iterate_op x n :=
  (iterate_op_eq_pow' (x := x) (n := n)).symm

/-!
### Helper: positivity of powers
-/

omit [KSSeparation α] in
theorem pow'_pos {x : α} (hx : ident < x) {n : ℕ} (hn : 0 < n) : ident < pow' x n := by
  -- `pow' x 0 = ident` and `pow' x` is strictly increasing in the exponent.
  have hmono := pow'_strictMono_exp (x := x) hx
  have : pow' x 0 < pow' x n := hmono hn
  simpa [pow'_zero] using this

/-!
### Helper: strict upper bounds from a single strict inequality

If `x^m0 < a^n0`, then every rational in `cutSet(a,x)` is strictly below `n0/m0`.
-/

omit [KSSeparation α] in
theorem cutSet_lt_of_pow'_lt (a : α) (ha : ident < a) {x : α} {m0 n0 : ℕ} (hm0 : 0 < m0)
    (h_lt : pow' x m0 < pow' a n0) :
    ∀ q ∈ cutSet a x, (q : ℝ) < (n0 : ℝ) / (m0 : ℝ) := by
  intro q hq
  rcases hq with ⟨_hq_nonneg, m, n, hn_pos, hq_eq, ham_le⟩
  -- Rewrite `q` as `m/n`.
  subst hq_eq

  have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hm0_pos' : 0 < (m0 : ℝ) := by exact_mod_cast hm0

  -- Scale `a^m ≤ x^n` by `m0`: `a^(m*m0) ≤ x^(n*m0)`.
  have ham_le' : pow' a (m * m0) ≤ pow' x (n * m0) := by
    -- raise both sides to the (positive) power `m0`
    have := pow'_mono_base (x := pow' a m) (y := pow' x n) ham_le m0 hm0
    -- rewrite (a^m)^m0 and (x^n)^m0
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  -- Scale `x^m0 < a^n0` by `n`: `x^(m0*n) < a^(n0*n)`.
  have hx_lt' : pow' x (m0 * n) < pow' a (n0 * n) := by
    have := pow'_strictMono_base (x := pow' x m0) (y := pow' a n0) h_lt n hn_pos
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  -- Combine: `a^(m*m0) ≤ x^(n*m0) = x^(m0*n) < a^(n0*n)`.
  have h_between : pow' a (m * m0) < pow' a (n0 * n) := by
    -- rewrite `n*m0 = m0*n`
    have : n * m0 = m0 * n := Nat.mul_comm n m0
    have ham_le'' : pow' a (m * m0) ≤ pow' x (m0 * n) := by
      simpa [this] using ham_le'
    exact lt_of_le_of_lt ham_le'' hx_lt'

  -- Since `a > ident`, strict monotonicity of `pow' a` gives `m*m0 < n0*n`.
  have h_nat : m * m0 < n0 * n := by
    exact (pow'_strictMono_exp (x := a) ha).lt_iff_lt.mp h_between

  -- Convert the nat inequality to a real inequality of fractions.
  have h' : (m : ℝ) * (m0 : ℝ) < (n0 : ℝ) * (n : ℝ) := by exact_mod_cast h_nat
  have : (m : ℝ) / (n : ℝ) < (n0 : ℝ) / (m0 : ℝ) := by
    exact (div_lt_div_iff₀ hn_pos' hm0_pos').2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h')
  -- Replace the RHS by `(n0 : ℝ) / (m0 : ℝ)` and rewrite the LHS as `(q : ℝ)`.
  simpa [Rat.cast_div, Rat.cast_natCast] using this

/-! Rational cut addition uses a common denominator and commutative powers.
The positive-natural proof below supplies the common supremum argument. -/

-- A small helper: the real image of a cut-set.
omit [KSSeparation α] in
abbrev cutSetReal (a : α) (x : α) : Set ℝ := (fun q : ℚ => (q : ℝ)) '' cutSet a x

omit [KSSeparation α] in
theorem cutSetReal_nonempty (a : α) (x : α) : (cutSetReal a x).Nonempty :=
  Set.image_nonempty.mpr (cutSet_nonempty a x (ident_le x))

theorem cutSetReal_bddAbove (a : α) (ha : ident < a) (x : α) : BddAbove (cutSetReal a x) := by
  rcases cutSet_bddAbove a ha x with ⟨B, hB⟩
  refine ⟨(B : ℝ), ?_⟩
  intro r hr
  rcases hr with ⟨q, hq, rfl⟩
  exact Rat.cast_le.mpr (hB hq)

omit [KSSeparation α] in
theorem Θ_cuts_eq_csSup (a : α) (ha : ident < a) (x : α) :
    Θ_cuts a ha x = sSup (cutSetReal a x) := by
  simp [Θ_cuts, cutSetReal, ident_le x]

-- Closure of `cutSet` under rational addition.
theorem cutSet_add_closed (a : α) (x y : α) :
    ∀ {q₁ q₂ : ℚ}, q₁ ∈ cutSet a x → q₂ ∈ cutSet a y → q₁ + q₂ ∈ cutSet a (op x y) := by
  intro q₁ q₂ hq₁ hq₂
  rcases hq₁ with ⟨hq₁_nonneg, m₁, n₁, hn₁_pos, hq₁_eq, ham₁_le⟩
  rcases hq₂ with ⟨hq₂_nonneg, m₂, n₂, hn₂_pos, hq₂_eq, ham₂_le⟩
  subst hq₁_eq; subst hq₂_eq

  -- Use the common denominator `n₁ * n₂`.
  refine ⟨add_nonneg hq₁_nonneg hq₂_nonneg, m₁ * n₂ + m₂ * n₁, n₁ * n₂, Nat.mul_pos hn₁_pos hn₂_pos, ?_, ?_⟩
  · -- arithmetic: (m1/n1) + (m2/n2) = (m1*n2 + m2*n1)/(n1*n2)
    have hn₁_ne : (n₁ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn₁_pos)
    have hn₂_ne : (n₂ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn₂_pos)
    field_simp [hn₁_ne, hn₂_ne]
    simp [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, add_comm]

  -- Scale inequalities to the common denominator.
  have ham₁_le' : pow' a (m₁ * n₂) ≤ pow' x (n₁ * n₂) := by
    have := pow'_mono_base (x := pow' a m₁) (y := pow' x n₁) ham₁_le n₂ hn₂_pos
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
  have ham₂_le' : pow' a (m₂ * n₁) ≤ pow' y (n₂ * n₁) := by
    have := pow'_mono_base (x := pow' a m₂) (y := pow' y n₂) ham₂_le n₁ hn₁_pos
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  -- Combine: a^(m₁*n₂ + m₂*n₁) ≤ x^(n₁*n₂) ⊕ y^(n₁*n₂) = (x⊕y)^(n₁*n₂).
  -- Distribute power over `op` (this is linear in the additive setting).
  have h_distrib :
      pow' (op x y) (n₁ * n₂) = op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) := by
    -- Reuse the existing iterate-op lemma, then rewrite back to `pow'`.
    simpa [pow'_eq_iterate_op] using
      (KnuthSkillingAlgebra.iterate_op_op_distrib_of_comm (α := α) (x := x) (y := y) (m := n₁ * n₂) op_comm')

  have ham₂_le'' : pow' a (m₂ * n₁) ≤ pow' y (n₁ * n₂) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ham₂_le'

  -- Monotonicity in both arguments.
  have h_mono_right :
      op (pow' a (m₁ * n₂)) (pow' a (m₂ * n₁)) ≤ op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) :=
    KnuthSkillingAlgebra.op_mono_right (x := pow' a (m₁ * n₂)) ham₂_le''

  have h_mono_left :
      op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) ≤ op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) :=
    KnuthSkillingAlgebra.op_mono_left (y := pow' y (n₁ * n₂)) ham₁_le'

  -- Put it together.
  calc
    pow' a (m₁ * n₂ + m₂ * n₁)
        = op (pow' a (m₁ * n₂)) (pow' a (m₂ * n₁)) := by
            simp [pow'_add]
    _ ≤ op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) := h_mono_right
    _ ≤ op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) := h_mono_left
    _ = pow' (op x y) (n₁ * n₂) := by
          simpa using h_distrib.symm


end Standalone

/-!
## §8: Identity-Free Cuts (Using ℕ+ Iteration)

This section provides a **genuinely identity-free** cuts construction using:
- `iterate_op_pnat : ℕ+ → α` instead of `pow' : ℕ → α` (no n=0 base case)
- `IsPositive a` instead of `ident < a` (Eric Luap's identity-free positivity)

This is the proper foundational approach for ordered semigroups without identity.
-/

section IdentityFreeCuts
variable {α : Type*} [KSSemigroupBase α] [KSSeparationSemigroup α]

open KSSemigroupBase

/-- Identity-free cut set: rationals m/n such that a^m ≤ x^n (using ℕ+ iteration). -/
def cutSet_pnat (a : α) (x : α) : Set ℚ :=
  { q : ℚ | 0 ≤ q ∧ ∃ (m n : ℕ+), q = (m : ℚ) / n ∧ iterate_op_pnat a m ≤ iterate_op_pnat x n }

/-- **Archimedean property for identity-free semigroups**: For positive elements a and x,
there exists N such that a ≤ x^N.

This is derivable from `KSSeparationSemigroup` via the following argument:
1. If a ≤ x, then N = 1 works.
2. If x < a, apply separation with base x on interval (x, a) to get bounds.
   The lower bound x^m < x^n forces m < n (strict mono in exponent).
   Combined with density of rationals, this shows x^n grows unboundedly.

Full proof uses techniques from SandwichSeparation.lean. -/
theorem archimedean_pnat_of_separation (a x : α) (ha : IsPositive a) (hx : IsPositive x) :
    ∃ N : ℕ+, a ≤ iterate_op_pnat x N := by
  -- Case 1: a ≤ x
  by_cases hax : a ≤ x
  · exact ⟨1, by simpa only [iterate_op_pnat_one] using hax⟩
  -- Case 2: x < a
  push Not at hax
  -- Apply separation with base x on interval (a, op a a)
  -- First establish: a < op a a (from IsPositive a)
  have ha2_lt : a < op a a := ha a
  -- Establish: IsPositive (op a a)
  -- For any y: y < op a y < op a (op a y) = op (op a a) y (by associativity)
  have ha2_pos : IsPositive (op a a) := fun y =>
    lt_trans (ha y) (by rw [op_assoc]; exact ha (op a y))
  -- Apply separation: base = x, lower = a, upper = op a a
  obtain ⟨n, m, h_lower, h_upper⟩ := KSSeparationSemigroup.sep hx ha ha2_pos ha2_lt
  -- h_lower: a^m < x^n
  -- h_upper: x^n ≤ (op a a)^m
  -- From a^m < x^n with m ≥ 1: a = a^1 ≤ a^m < x^n
  use n
  -- Show a ≤ a^m using monotonicity (1 ≤ m)
  have ha_le_am : a ≤ iterate_op_pnat a m := by
    rw [← iterate_op_pnat_one a]
    exact iterate_op_pnat_mono a ha (show 1 ≤ m from one_le)
  -- Conclude: a ≤ a^m < x^n
  exact le_of_lt (lt_of_le_of_lt ha_le_am h_lower)

/-- **Reverse Archimedean**: For positive a and x, there exists K with x < a^K.
This bounds x from above by powers of a. -/
theorem reverse_archimedean_pnat (a x : α) (ha : IsPositive a) (_hx : IsPositive x) :
    ∃ K : ℕ+, x < iterate_op_pnat a K := by
  -- Case 1: x < a already
  by_cases hxa : x < a
  · exact ⟨1, by simpa only [iterate_op_pnat_one] using hxa⟩
  -- Case 2: a ≤ x
  push Not at hxa
  -- Need to show x < a^K for some K
  -- Use Archimedean: x ≤ a^N for some N, then x < a^{N+1}
  obtain ⟨N, hN⟩ := archimedean_pnat_of_separation x a _hx ha
  -- hN : x ≤ a^N
  use N + 1
  have h_mono : N < N + 1 := PNat.lt_add_one_iff.mpr (le_refl N)
  calc x ≤ iterate_op_pnat a N := hN
    _ < iterate_op_pnat a (N + 1) := iterate_op_pnat_strictMono a ha h_mono

omit [KSSeparationSemigroup α] in
/-- The cut set is nonempty when x has positive element a in its cut (contains 1/1 = 1 when a ≤ x). -/
theorem cutSet_pnat_nonempty_of_ge (a x : α) (hax : a ≤ x) :
    (cutSet_pnat a x).Nonempty := by
  use 1
  simp only [cutSet_pnat, Set.mem_ofPred_eq]
  refine ⟨by norm_num, 1, 1, ?_, ?_⟩
  · norm_num
  · simp only [iterate_op_pnat_one, hax]

/-- More general nonemptiness: cut set always contains rational approximations. -/
theorem cutSet_pnat_nonempty (a x : α) (ha : IsPositive a) (hx : IsPositive x) :
    (cutSet_pnat a x).Nonempty := by
  -- By Archimedean: ∃ N, a ≤ x^N
  -- Then 1/N ∈ cutSet_pnat a x since a^1 = a ≤ x^N
  obtain ⟨N, hN⟩ := archimedean_pnat_of_separation a x ha hx
  -- hN : a ≤ iterate_op_pnat x N
  use (1 : ℚ) / N
  simp only [cutSet_pnat, Set.mem_ofPred_eq]
  refine ⟨?_, 1, N, ?_, ?_⟩
  · -- 0 ≤ 1/N
    exact div_nonneg (by norm_num) (by exact_mod_cast N.pos.le)
  · -- 1/N = 1/N
    norm_num
  · -- a^1 ≤ x^N
    simp only [iterate_op_pnat_one]
    exact hN

omit [KSSeparationSemigroup α] in
/-- Key lemma: iterate_op_pnat is strictly monotone in base for fixed exponent. -/
theorem iterate_op_pnat_strictMono_base {a b : α} (hab : a < b) (n : ℕ+) :
    iterate_op_pnat a n < iterate_op_pnat b n := by
  exact KnuthSkilling.iterate_op_pnat_strictMono_base hab n

omit [KSSeparationSemigroup α] in
/-- Non-strict monotonicity. -/
theorem iterate_op_pnat_mono_base {a b : α} (hab : a ≤ b) (n : ℕ+) :
    iterate_op_pnat a n ≤ iterate_op_pnat b n := by
  exact KnuthSkilling.iterate_op_pnat_mono_base hab n

omit [KSSeparationSemigroup α] in
/-- Multiplicativity: (x^m)^n = x^(m*n). This follows from pure associativity.
    Key for bounding the cut set. -/
theorem iterate_op_pnat_mul (x : α) (m n : ℕ+) :
    iterate_op_pnat (iterate_op_pnat x m) n = iterate_op_pnat x (m * n) := by
  induction n using PNat.recOn with
  | one => simp [iterate_op_pnat_one]
  | succ n ih =>
    rw [iterate_op_pnat_succ, ih, ← iterate_op_pnat_add]
    congr 1
    apply Subtype.ext
    change (m : ℕ) + (m : ℕ) * (n : ℕ) = (m : ℕ) * ((n : ℕ) + 1)
    ring

omit [KSSeparationSemigroup α] in
/-- Distribution: (x ⊕ y)^n = x^n ⊕ y^n when operation commutes. -/
theorem iterate_op_pnat_distrib (x y : α) (hcomm : ∀ a b : α, op a b = op b a) (n : ℕ+) :
    iterate_op_pnat (op x y) n = op (iterate_op_pnat x n) (iterate_op_pnat y n) := by
  induction n using PNat.recOn with
  | one => simp [iterate_op_pnat_one]
  | succ n ih =>
    rw [iterate_op_pnat_succ, iterate_op_pnat_succ, iterate_op_pnat_succ, ih]
    rw [op_assoc, ← op_assoc y, hcomm y (iterate_op_pnat x n), op_assoc, ← op_assoc x]

/-- The cut set is bounded above (uses Archimedean property from separation). -/
theorem cutSet_pnat_bddAbove (a x : α) (ha : IsPositive a) (hx : IsPositive x) :
    BddAbove (cutSet_pnat a x) := by
  -- By reverse Archimedean: ∃ K, x < a^K
  -- If q = m/n ∈ cutSet_pnat, then a^m ≤ x^n < (a^K)^n = a^{K*n}
  -- Thus a^m < a^{K*n}, so m < K*n (by strict mono in exponent), hence m/n < K
  obtain ⟨K, hK⟩ := reverse_archimedean_pnat a x ha hx
  -- hK : x < iterate_op_pnat a K
  use (K : ℚ)
  intro q hq
  simp only [cutSet_pnat, Set.mem_ofPred_eq] at hq
  obtain ⟨_hq_nonneg, m, n, hq_eq, ham_le⟩ := hq
  subst hq_eq
  -- Goal: m/n ≤ K
  -- Step 1: x^n < (a^K)^n (strict mono in base)
  have hxn_lt : iterate_op_pnat x n < iterate_op_pnat (iterate_op_pnat a K) n :=
    iterate_op_pnat_strictMono_base hK n
  -- Step 2: (a^K)^n = a^{K*n} (multiplicativity)
  rw [iterate_op_pnat_mul] at hxn_lt
  -- hxn_lt : iterate_op_pnat x n < iterate_op_pnat a (K * n)
  -- Step 3: a^m ≤ x^n < a^{K*n}
  have ham_lt : iterate_op_pnat a m < iterate_op_pnat a (K * n) :=
    lt_of_le_of_lt ham_le hxn_lt
  -- Step 4: m < K*n (by strict mono in exponent for positive a)
  have hmKn : m < K * n := by
    by_contra h_not
    push Not at h_not  -- K * n ≤ m
    have h_mono : iterate_op_pnat a (K * n) ≤ iterate_op_pnat a m :=
      iterate_op_pnat_mono a ha h_not
    exact not_lt.mpr h_mono ham_lt
  -- Step 5: m/n ≤ K (since m < K*n implies m/n < K for positive n)
  have hn_pos : (0 : ℚ) < n := by exact_mod_cast n.pos
  have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_pos
  rw [div_le_iff₀ hn_pos]
  -- Goal: (m : ℚ) ≤ K * n
  have h_le : m ≤ K * n := le_of_lt hmKn
  exact_mod_cast h_le

omit [KSSeparationSemigroup α] in
/-- Closure of cutSet_pnat under addition (for additivity proof). -/
theorem cutSet_pnat_add_closed (a x y : α) (_hcomm : ∀ u v : α, op u v = op v u) :
    ∀ {q₁ q₂ : ℚ}, q₁ ∈ cutSet_pnat a x → q₂ ∈ cutSet_pnat a y →
    q₁ + q₂ ∈ cutSet_pnat a (op x y) := by
  rintro q₁ q₂ ⟨hq₁, m₁, n₁, rfl, h₁⟩ ⟨hq₂, m₂, n₂, rfl, h₂⟩
  refine ⟨add_nonneg hq₁ hq₂, m₁ * n₂ + m₂ * n₁, n₁ * n₂, ?_, ?_⟩
  · push_cast
    field_simp
  · have h₁' := iterate_op_pnat_mono_base h₁ n₂
    have h₂' := iterate_op_pnat_mono_base h₂ n₁
    rw [iterate_op_pnat_mul, iterate_op_pnat_mul] at h₁' h₂'
    rw [mul_comm n₂ n₁] at h₂'
    rw [iterate_op_pnat_add, iterate_op_pnat_distrib x y _hcomm]
    exact le_trans ((op_strictMono_left _).monotone h₁')
      ((op_strictMono_right _).monotone h₂')

private theorem rat_image_bddAbove {S : Set ℚ} (h : BddAbove S) :
    BddAbove ((↑) '' S : Set ℝ) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by rintro _ ⟨q, hq, rfl⟩; exact_mod_cast hb hq⟩

/-- Definition of Θ via supremum of cut set (identity-free).
    The `IsPositive` hypotheses ensure the cut set is nonempty and bounded above. -/
noncomputable def Θ_cuts_pnat (a : α) (_ha : IsPositive a) (x : α) (_hx : IsPositive x) : ℝ :=
  sSup ((↑) '' cutSet_pnat a x : Set ℝ)

omit [KSSeparationSemigroup α] in
/-- Every positive-natural cut witness is a strictly positive rational. -/
theorem cutSet_pnat_pos (a x : α) {q : ℚ} (hq : q ∈ cutSet_pnat a x) : 0 < q := by
  obtain ⟨_, m, n, rfl, _⟩ := hq
  exact div_pos (by positivity) (by positivity)

/-- Positive elements have strictly positive cut readouts. -/
theorem Θ_cuts_pnat_pos (a x : α) (ha : IsPositive a) (hx : IsPositive x) :
    0 < Θ_cuts_pnat a ha x hx := by
  obtain ⟨q, hq⟩ := cutSet_pnat_nonempty a x ha hx
  exact lt_of_lt_of_le (by exact_mod_cast cutSet_pnat_pos a x hq)
    (le_csSup (rat_image_bddAbove (cutSet_pnat_bddAbove a x ha hx)) ⟨q, hq, rfl⟩)

/-- Θ_cuts_pnat is monotone: x ≤ y → Θ(x) ≤ Θ(y). -/
theorem Θ_cuts_pnat_mono (a : α) (ha : IsPositive a)
    {x y : α} (hx : IsPositive x) (hy : IsPositive y) (hxy : x ≤ y) :
    Θ_cuts_pnat a ha x hx ≤ Θ_cuts_pnat a ha y hy := by
  simp only [Θ_cuts_pnat]
  -- cutSet_pnat a x ⊆ cutSet_pnat a y
  apply csSup_le_csSup
  · -- cutSet_pnat a y is bounded
    have hbdd := cutSet_pnat_bddAbove a y ha hy
    obtain ⟨B, hB⟩ := hbdd
    use B
    intro r hr
    simp only [Set.mem_image] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact Rat.cast_le.mpr (hB hq)
  · -- cutSet_pnat a x is nonempty
    have hne := cutSet_pnat_nonempty a x ha hx
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, Set.mem_image_of_mem _ hq⟩
  · -- Inclusion
    intro r hr
    simp only [Set.mem_image] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    simp only [Set.mem_image]
    refine ⟨q, ?_, rfl⟩
    simp only [cutSet_pnat, Set.mem_ofPred_eq] at hq ⊢
    obtain ⟨hq_nonneg, m, n, hq_eq, ham_le⟩ := hq
    exact ⟨hq_nonneg, m, n, hq_eq, le_trans ham_le (iterate_op_pnat_mono_base hxy n)⟩

/-!
### Identity-Free Cuts: Full Representation

The complete identity-free cuts path producing `RepresentationResult`.
All proofs use only `IsPositive`, `iterate_op_pnat`, and `KSSeparationSemigroup`.
-/

omit [KSSeparationSemigroup α] in
/-- Key lemma: if `iterate_op_pnat x m₀ < iterate_op_pnat a n₀`, then all rationals
    in `cutSet_pnat a x` are strictly less than `n₀/m₀`.

This is the identity-free version of `cutSet_lt_of_pow'_lt`. -/
theorem cutSet_pnat_lt_of_iterate_lt (a : α) (ha : IsPositive a) {x : α} {m₀ n₀ : ℕ+}
    (h_lt : iterate_op_pnat x m₀ < iterate_op_pnat a n₀) :
    ∀ q ∈ cutSet_pnat a x, (q : ℝ) < (n₀ : ℝ) / (m₀ : ℝ) := by
  intro q hq
  simp only [cutSet_pnat, Set.mem_ofPred_eq] at hq
  obtain ⟨_hq_nonneg, m, n, hq_eq, ham_le⟩ := hq
  subst hq_eq
  -- We have: a^m ≤ x^n and x^m₀ < a^n₀
  -- Need to show: m/n < n₀/m₀, i.e., m * m₀ < n₀ * n

  have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hm₀_pos' : 0 < (m₀ : ℝ) := by exact_mod_cast m₀.pos

  -- Scale `a^m ≤ x^n` by m₀: `a^(m*m₀) ≤ x^(n*m₀)`
  have ham_le' : iterate_op_pnat a (m * m₀) ≤ iterate_op_pnat x (n * m₀) := by
    have := iterate_op_pnat_mono_base ham_le m₀
    rwa [iterate_op_pnat_mul, iterate_op_pnat_mul] at this

  -- Scale `x^m₀ < a^n₀` by n: `x^(m₀*n) < a^(n₀*n)`
  have hx_lt' : iterate_op_pnat x (m₀ * n) < iterate_op_pnat a (n₀ * n) := by
    have := iterate_op_pnat_strictMono_base h_lt n
    rwa [iterate_op_pnat_mul, iterate_op_pnat_mul] at this

  -- Combine: `a^(m*m₀) ≤ x^(n*m₀) = x^(m₀*n) < a^(n₀*n)`
  have h_between : iterate_op_pnat a (m * m₀) < iterate_op_pnat a (n₀ * n) := by
    have heq : n * m₀ = m₀ * n := mul_comm n m₀
    calc iterate_op_pnat a (m * m₀)
        ≤ iterate_op_pnat x (n * m₀) := ham_le'
      _ = iterate_op_pnat x (m₀ * n) := by rw [heq]
      _ < iterate_op_pnat a (n₀ * n) := hx_lt'

  -- From `a^(m*m₀) < a^(n₀*n)`, strict monotonicity gives `m*m₀ < n₀*n`
  have h_exp_lt : m * m₀ < n₀ * n := (iterate_op_pnat_strictMono a ha).lt_iff_lt.mp h_between

  -- Convert to real inequality: m/n < n₀/m₀
  have h_exp_lt' : (m : ℝ) * (m₀ : ℝ) < (n₀ : ℝ) * (n : ℝ) := by
    have : ((m * m₀ : ℕ+) : ℝ) < ((n₀ * n : ℕ+) : ℝ) := by exact_mod_cast h_exp_lt
    simp only [PNat.mul_coe, Nat.cast_mul] at this
    exact this

  -- m/n < n₀/m₀ iff m * m₀ < n₀ * n (when denominators positive)
  -- Goal: ↑(↑↑m / ↑↑n : ℚ) < (n₀ : ℝ) / (m₀ : ℝ)
  -- Rat.cast_div: ↑(p/q) = (↑p)/(↑q) for ℚ→ℝ
  -- Rat.cast_natCast: ↑(n : ℚ) = (n : ℝ) for ℕ→ℝ via ℚ
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [div_lt_div_iff₀ hn_pos' hm₀_pos']
  exact h_exp_lt'

/-- **Strict monotonicity** of identity-free Θ: x < y → Θ(x) < Θ(y).

This is the key property needed for order-preservation.
Requires `KSSeparationSemigroupStrict` for the strict upper bound. -/
theorem Θ_cuts_pnat_strictMono {α : Type*} [KSSemigroupBase α]
    [KSSeparationSemigroupStrict α] (a : α) (ha : IsPositive a)
    {x y : α} (hx : IsPositive x) (hy : IsPositive y) (hxy : x < y) :
    Θ_cuts_pnat a ha x hx < Θ_cuts_pnat a ha y hy := by
  classical
  -- Apply STRICT separation with base a on (x, y)
  obtain ⟨n₀, m₀, hlt_iter, hgt_iter⟩ := KSSeparationSemigroupStrict.sep_strict ha hx hy hxy
  -- hlt_iter: iterate_op_pnat x m₀ < iterate_op_pnat a n₀
  -- hgt_iter: iterate_op_pnat a n₀ < iterate_op_pnat y m₀ (STRICT!)

  -- The witness rational q₀ = n₀/m₀ lies in cutSet_pnat a y (with non-strict bound)
  have hq₀_mem : ((n₀ : ℚ) / m₀) ∈ cutSet_pnat a y := by
    simp only [cutSet_pnat, Set.mem_ofPred_eq]
    refine ⟨?_, n₀, m₀, ?_, ?_⟩
    · exact div_nonneg (by exact_mod_cast n₀.pos.le) (by exact_mod_cast m₀.pos.le)
    · rfl
    · exact le_of_lt hgt_iter  -- a^n₀ < y^m₀ implies a^n₀ ≤ y^m₀

  -- q₀ ≤ Θ(y)
  have hq₀_le : ((n₀ : ℚ) / m₀ : ℝ) ≤ Θ_cuts_pnat a ha y hy := by
    simp only [Θ_cuts_pnat]
    have hbdd := cutSet_pnat_bddAbove a y ha hy
    obtain ⟨B, hB⟩ := hbdd
    have hbdd' : BddAbove ((↑) '' cutSet_pnat a y : Set ℝ) := by
      refine ⟨(B : ℝ), ?_⟩
      intro r hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact Rat.cast_le.mpr (hB hq)
    have hmem : (((n₀ : ℚ) / m₀) : ℝ) ∈ ((↑) '' cutSet_pnat a y : Set ℝ) := by
      refine ⟨(n₀ : ℚ) / m₀, hq₀_mem, ?_⟩
      simp only [Rat.cast_div, Rat.cast_natCast]
    exact le_csSup hbdd' hmem

  -- Apply STRICT separation again to (x^m₀, a^n₀) with base a
  have hx_m₀_pos : IsPositive (iterate_op_pnat x m₀) := iterate_op_pnat_pos x hx m₀
  have ha_n₀_pos : IsPositive (iterate_op_pnat a n₀) := iterate_op_pnat_pos a ha n₀

  obtain ⟨n₁, k, hlt₁_iter, hgt₁_iter⟩ :=
    KSSeparationSemigroupStrict.sep_strict ha hx_m₀_pos ha_n₀_pos hlt_iter
  -- hlt₁_iter: (x^m₀)^k < a^n₁
  -- hgt₁_iter: a^n₁ < (a^n₀)^k (STRICT!)

  have hlt₁ : iterate_op_pnat x (m₀ * k) < iterate_op_pnat a n₁ := by
    have : iterate_op_pnat (iterate_op_pnat x m₀) k < iterate_op_pnat a n₁ := hlt₁_iter
    rwa [iterate_op_pnat_mul] at this

  -- From a^n₁ < (a^n₀)^k = a^(n₀*k), we get n₁ < n₀*k by strict mono
  have h_n₁_lt : n₁ < n₀ * k := by
    have hgt₁' : iterate_op_pnat a n₁ < iterate_op_pnat a (n₀ * k) := by
      have : iterate_op_pnat a n₁ < iterate_op_pnat (iterate_op_pnat a n₀) k := hgt₁_iter
      rwa [iterate_op_pnat_mul] at this
    exact (iterate_op_pnat_strictMono a ha).lt_iff_lt.mp hgt₁'

  -- Θ(x) is bounded above by n₁/(m₀*k)
  have hΘx_le : Θ_cuts_pnat a ha x hx ≤ (n₁ : ℝ) / ((m₀ * k : ℕ+) : ℝ) := by
    simp only [Θ_cuts_pnat]
    have hne := cutSet_pnat_nonempty a x ha hx
    have hne' : ((↑) '' cutSet_pnat a x : Set ℝ).Nonempty := Set.image_nonempty.mpr hne
    refine csSup_le hne' ?_
    intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    have h_lt := cutSet_pnat_lt_of_iterate_lt a ha hlt₁ q hq
    exact le_of_lt h_lt

  -- n₁/(m₀*k) < n₀/m₀ because n₁ < n₀*k
  have hlt_rat : (n₁ : ℝ) / ((m₀ * k : ℕ+) : ℝ) < (n₀ : ℝ) / (m₀ : ℝ) := by
    have h_n₁_lt' : (n₁ : ℝ) < (n₀ : ℝ) * (k : ℝ) := by
      have : ((n₁ : ℕ+) : ℝ) < ((n₀ * k : ℕ+) : ℝ) := by exact_mod_cast h_n₁_lt
      simp only [PNat.mul_coe, Nat.cast_mul] at this
      exact this
    have hm₀k_pos : 0 < ((m₀ * k : ℕ+) : ℝ) := by exact_mod_cast (m₀ * k).pos
    have hm₀_pos : 0 < (m₀ : ℝ) := by exact_mod_cast m₀.pos
    rw [div_lt_div_iff₀ hm₀k_pos hm₀_pos]
    have hk' : ((m₀ * k : ℕ+) : ℝ) = (m₀ : ℝ) * (k : ℝ) := by simp only [PNat.mul_coe, Nat.cast_mul]
    calc (n₁ : ℝ) * (m₀ : ℝ)
        < ((n₀ : ℝ) * (k : ℝ)) * (m₀ : ℝ) := by nlinarith [h_n₁_lt']
      _ = (n₀ : ℝ) * ((m₀ : ℝ) * (k : ℝ)) := by ring
      _ = (n₀ : ℝ) * ((m₀ * k : ℕ+) : ℝ) := by rw [← hk']

  -- Combine: Θ(x) ≤ n₁/(m₀*k) < n₀/m₀ ≤ Θ(y)
  have hq₀_eq : ((n₀ : ℚ) / m₀ : ℝ) = (n₀ : ℝ) / (m₀ : ℝ) := by
    simp only [Rat.cast_natCast]
  calc Θ_cuts_pnat a ha x hx
      ≤ (n₁ : ℝ) / ((m₀ * k : ℕ+) : ℝ) := hΘx_le
    _ < (n₀ : ℝ) / (m₀ : ℝ) := hlt_rat
    _ = ((n₀ : ℚ) / m₀ : ℝ) := hq₀_eq.symm
    _ ≤ Θ_cuts_pnat a ha y hy := hq₀_le

omit [KSSeparationSemigroup α] in
/-- Positivity is preserved under `op` for positive elements. -/
theorem isPositive_op' {x y : α} (hx : IsPositive x) (hy : IsPositive y) : IsPositive (op x y) := by
  intro z
  simpa only [op_assoc] using lt_trans (hy z) (hx (op y z))

/-- **Additivity** of identity-free Θ: Θ(x⊕y) = Θ(x) + Θ(y).

This follows the same proof structure as the identity-based `Θ_cuts_add`:
1. First inequality (≥): Uses `cutSet_pnat_add_closed` and `csSup_add`
2. Second inequality (≤): By contradiction using rational splitting

Requires commutativity for `cutSet_pnat_add_closed`. -/
theorem Θ_cuts_pnat_add (a : α) (ha : IsPositive a)
    (hcomm : ∀ u v : α, op u v = op v u)
    (x y : α) (hx : IsPositive x) (hy : IsPositive y) :
    Θ_cuts_pnat a ha (op x y) (isPositive_op' hx hy) =
      Θ_cuts_pnat a ha x hx + Θ_cuts_pnat a ha y hy := by
  classical
  let S : Set ℝ := (↑) '' cutSet_pnat a x
  let T : Set ℝ := (↑) '' cutSet_pnat a y
  let U : Set ℝ := (↑) '' cutSet_pnat a (op x y)
  have hs : S.Nonempty := (cutSet_pnat_nonempty a x ha hx).image _
  have ht : T.Nonempty := (cutSet_pnat_nonempty a y ha hy).image _
  have hu : U.Nonempty := (cutSet_pnat_nonempty a (op x y) ha (isPositive_op' hx hy)).image _
  have bs := rat_image_bddAbove (cutSet_pnat_bddAbove a x ha hx)
  have bt := rat_image_bddAbove (cutSet_pnat_bddAbove a y ha hy)
  have bu := rat_image_bddAbove (cutSet_pnat_bddAbove a (op x y) ha (isPositive_op' hx hy))
  have hsum : S + T ⊆ U := by
    rintro _ ⟨s, ⟨q₁, hq₁, rfl⟩, t, ⟨q₂, hq₂, rfl⟩, rfl⟩
    exact ⟨q₁ + q₂, cutSet_pnat_add_closed a x y hcomm hq₁ hq₂, Rat.cast_add ..⟩
  change sSup U = sSup S + sSup T
  apply le_antisymm
  · apply csSup_le hu
    rintro _ ⟨q, hq, rfl⟩
    by_contra h
    obtain ⟨q₁, h₁, h₁'⟩ := exists_rat_btwn (show sSup S < (q : ℝ) - sSup T by linarith)
    let q₂ : ℚ := q - q₁
    have h₂ : sSup T < (q₂ : ℝ) := by dsimp [q₂]; push_cast; linarith
    have hq₁ : 0 < q₁ := by exact_mod_cast lt_trans (Θ_cuts_pnat_pos a x ha hx) h₁
    have hq₂ : 0 < q₂ := by exact_mod_cast lt_trans (Θ_cuts_pnat_pos a y ha hy) h₂
    obtain ⟨m₁, n₁, e₁⟩ := positive_rat_fraction q₁ hq₁
    obtain ⟨m₂, n₂, e₂⟩ := positive_rat_fraction q₂ hq₂
    have hx' : iterate_op_pnat x n₁ < iterate_op_pnat a m₁ := by
      apply lt_of_not_ge
      intro hh
      exact (not_le_of_gt h₁) (le_csSup bs ⟨q₁, ⟨hq₁.le, m₁, n₁, e₁, hh⟩, rfl⟩)
    have hy' : iterate_op_pnat y n₂ < iterate_op_pnat a m₂ := by
      apply lt_of_not_ge
      intro hh
      exact (not_le_of_gt h₂) (le_csSup bt ⟨q₂, ⟨hq₂.le, m₂, n₂, e₂, hh⟩, rfl⟩)
    have h₁s := iterate_op_pnat_strictMono_base hx' n₂
    have h₂s := iterate_op_pnat_strictMono_base hy' n₁
    rw [iterate_op_pnat_mul, iterate_op_pnat_mul] at h₁s h₂s
    rw [mul_comm n₂ n₁] at h₂s
    have hpow : iterate_op_pnat (op x y) (n₁ * n₂) <
        iterate_op_pnat a (m₁ * n₂ + m₂ * n₁) := by
      rw [iterate_op_pnat_distrib x y hcomm, iterate_op_pnat_add]
      exact lt_trans (op_strictMono_left _ h₁s) (op_strictMono_right _ h₂s)
    have hbound := cutSet_pnat_lt_of_iterate_lt a ha hpow q hq
    have heq : ((m₁ * n₂ + m₂ * n₁ : ℕ+) : ℝ) / ((n₁ * n₂ : ℕ+) : ℝ) = q := by
      have ee : q = q₁ + q₂ := by simp [q₂]
      rw [ee, e₁, e₂]
      push_cast
      field_simp
    rw [heq] at hbound
    exact (lt_irrefl _) hbound
  · exact (csSup_add hs bs ht bt).symm.trans_le (csSup_le_csSup bu (hs.add ht) hsum)

/-!
### Identity-Free Representation Summary

The following theorems provide a **genuinely identity-free** cuts representation:

- `Θ_cuts_pnat` : Defined via Dedekind cuts using ℕ+ iteration (no n=0 case)
- `Θ_cuts_pnat_strictMono` : Strict monotonicity (x < y ↔ Θ(x) < Θ(y))
- `Θ_cuts_pnat_add` : Additivity (Θ(x⊕y) = Θ(x) + Θ(y))

**Usage**: For a positive ordered semigroup where all elements satisfy `IsPositive`,
these theorems provide a complete representation without needing identity.

**Relation to RepresentationResult**: The identity-free proofs here can be wrapped
into a `RepresentationResult` when restricted to positive elements. For general
ordered semigroups with identity, use `cuts_representation` below.
-/

end IdentityFreeCuts

section CompareNaturalCuts

omit [KSSeparation α] in
/-- Natural cuts add exactly the zero witness to positive-natural cuts. -/
theorem cutSet_eq_insert_pnat (a x : α) : cutSet a x = insert 0 (cutSet_pnat a x) := by
  ext q
  constructor
  · rintro ⟨hq, m, n, hn, eq, hpow⟩
    by_cases hm : m = 0
    · left; simp [eq, hm]
    · right
      let m' : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
      let n' : ℕ+ := ⟨n, hn⟩
      refine ⟨hq, m', n', eq, ?_⟩
      rw [KnuthSkillingAlgebra.iterate_op_pnat_eq, KnuthSkillingAlgebra.iterate_op_pnat_eq]
      change KnuthSkillingAlgebra.iterate_op a m ≤ KnuthSkillingAlgebra.iterate_op x n
      simpa only [iterate_op_eq_pow'] using hpow
  · rintro (rfl | ⟨hq, m, n, eq, hpow⟩)
    · exact ⟨le_rfl, 0, 1, by decide, by simp, by simpa [pow', op_ident_right] using ident_le x⟩
    · refine ⟨hq, m, n, n.pos, eq, ?_⟩
      simpa only [KnuthSkillingAlgebra.iterate_op_pnat_eq, iterate_op_eq_pow'] using hpow

/-- On positive elements the independently defined readouts agree exactly. -/
theorem Θ_cuts_eq_pnat (a x : α) (ha : ident < a) (hx : ident < x) :
    Θ_cuts a ha x = Θ_cuts_pnat a ((isPositive_iff_ident_lt a).mpr ha)
      x ((isPositive_iff_ident_lt x).mpr hx) := by
  have hap := (isPositive_iff_ident_lt a).mpr ha
  have hxp := (isPositive_iff_ident_lt x).mpr hx
  rw [Θ_cuts_eq_csSup]
  change sSup ((↑) '' cutSet a x : Set ℝ) = _
  rw [cutSet_eq_insert_pnat, Set.image_insert_eq]
  simp only [Rat.cast_zero]
  have hb := rat_image_bddAbove (cutSet_pnat_bddAbove a x hap hxp)
  have hn := (cutSet_pnat_nonempty a x hap hxp).image (fun q : ℚ => (q : ℝ))
  rw [csSup_insert hb hn]
  exact max_eq_right (Θ_cuts_pnat_pos a x hap hxp).le

omit [KSSeparation α] in
/-- Strictness for ordinary cuts includes the identity boundary explicitly. -/
theorem Θ_cuts_strictMono {α : Type*} [KnuthSkillingAlgebraBase α]
    [KSSeparationStrict α] (a : α) (ha : ident < a) : StrictMono (Θ_cuts a ha) := by
  intro x y hxy
  by_cases hx : x = ident
  · subst x
    rw [Θ_cuts_ident, Θ_cuts_eq_pnat a y ha hxy]
    exact Θ_cuts_pnat_pos a y ((isPositive_iff_ident_lt a).mpr ha)
      ((isPositive_iff_ident_lt y).mpr hxy)
  · have hxp : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx)
    have hyp := lt_trans hxp hxy
    rw [Θ_cuts_eq_pnat a x ha hxp, Θ_cuts_eq_pnat a y ha hyp]
    exact Θ_cuts_pnat_strictMono a ((isPositive_iff_ident_lt a).mpr ha)
      ((isPositive_iff_ident_lt x).mpr hxp) ((isPositive_iff_ident_lt y).mpr hyp) hxy

/-- Ordinary cuts extend positive-natural cuts by the identity case. -/
theorem Θ_cuts_add (a : α) (ha : ident < a) (x y : α) :
    Θ_cuts a ha (op x y) = Θ_cuts a ha x + Θ_cuts a ha y := by
  by_cases hx : x = ident
  · subst x; simp [op_ident_left, Θ_cuts_ident]
  by_cases hy : y = ident
  · subst y; simp [op_ident_right, Θ_cuts_ident]
  have hxp : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx)
  have hyp : ident < y := lt_of_le_of_ne (ident_le y) (Ne.symm hy)
  have hop : ident < op x y := lt_trans hxp (by simpa [op_ident_right] using op_strictMono_right x hyp)
  rw [Θ_cuts_eq_pnat a (op x y) ha hop, Θ_cuts_eq_pnat a x ha hxp, Θ_cuts_eq_pnat a y ha hyp]
  exact Θ_cuts_pnat_add a ((isPositive_iff_ident_lt a).mpr ha) op_comm' x y
    ((isPositive_iff_ident_lt x).mpr hxp) ((isPositive_iff_ident_lt y).mpr hyp)

end CompareNaturalCuts

/-! ## Bundled ordinary cuts

The readout is the independently defined supremum. Its normalization follows
from the common additive representation laws. -/

section UnifiedInterface
variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparationStrict α]

/-- The cuts path produces a `RepresentationResult` (order + additivity).
    Uses identity internally but the output doesn't require `Θ ident = 0` to be useful. -/
noncomputable def cuts_representation (a : α) (ha : ident < a) : RepresentationResult α :=
  { Θ := Θ_cuts a ha
    order_preserving := fun x y =>
      ⟨fun hxy => Θ_cuts_mono a ha hxy,
       fun hΘ => by
        -- Use strict monotonicity for reverse direction
        by_contra h
        push Not at h
        have hlt := Θ_cuts_strictMono a ha h
        exact not_le_of_gt hlt hΘ⟩
    additive := Θ_cuts_add a ha }

/-- The cuts path produces a `NormalizedRepresentationResult` (with `Θ ident = 0`). -/
noncomputable def cuts_normalized_representation (a : α) (ha : ident < a) :
    NormalizedRepresentationResult α :=
  (cuts_representation a ha).toNormalized

end UnifiedInterface

omit [KSSeparation α] in
/-- Dedekind-cuts characterization: `Θ_cuts` recovers any additive order embedding, normalized at `a`. -/
theorem Θ_cuts_eq_div_of_representation
    (a : α) (ha : ident < a) (Θ : α → ℝ)
    (hΘ_order : ∀ u v : α, u ≤ v ↔ Θ u ≤ Θ v)
    (hΘ_ident : Θ ident = 0)
    (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y)
    (x : α) :
    Θ_cuts a ha x = Θ x / Θ a := by
  let r : NormalizedRepresentationResult α := ⟨⟨Θ, hΘ_order, hΘ_add⟩, hΘ_ident⟩
  let : KSSeparationSemigroupStrict α := r.toRepresentationResult.separationSemigroupStrict
  let : KSSeparationStrict α := KSSeparationStrict_of_KSSeparationSemigroupStrict
  have hh := r.toRepresentationResult.calibrate_agree (cuts_representation a ha) a
    ((isPositive_iff_ident_lt a).mpr ha) x
  simp only [RepresentationResult.calibrate_apply] at hh
  change Θ x / Θ a = Θ_cuts a ha x / Θ_cuts a ha a at hh
  rw [Θ_cuts_base, div_one] at hh
  exact hh.symm


/-!
## §9b: Identity-Free Unified Interface

This section provides `cuts_pnat_representation` using the identity-free proofs
from §8 (`Θ_cuts_pnat`, `Θ_cuts_pnat_strictMono`, `Θ_cuts_pnat_add`).

**Key difference from §9a**: No identity required. Works with `KSSemigroupBase` +
`KSSeparationSemigroupStrict` instead of `KnuthSkillingAlgebra` + `KSSeparationStrict`.

**Requirement**: All elements must be positive (`∀ x, IsPositive x`). This is the
natural case for ordered semigroups without identity element.
-/

section IdentityFreeUnifiedInterface
variable {α : Type*} [KSSemigroupBase α] [KSSeparationSemigroupStrict α]

/-- **Identity-Free Cuts Representation**: Produces a `RepresentationResult` using
    only identity-free constructs (`Θ_cuts_pnat`, `IsPositive`, `iterate_op_pnat`).

    **Hypotheses**:
    - `a : α` - anchor element (used for normalization)
    - `ha : IsPositive a` - anchor is positive
    - `h_all_pos : ∀ x : α, IsPositive x` - all elements are positive
    - `hcomm : ∀ u v : α, op u v = op v u` - commutativity (for additivity)

    **Use case**: Ordered semigroups without identity element, where all elements
    are "positive" (i.e., `∀ z, z < op x z` for all `x`).

    For ordered monoids with identity, prefer `cuts_representation` from §9a. -/
noncomputable def cuts_pnat_representation
    (a : α) (ha : IsPositive a)
    (h_all_pos : ∀ x : α, IsPositive x)
    (hcomm : ∀ u v : α, op u v = op v u) : RepresentationResult α :=
  { Θ := fun x => Θ_cuts_pnat a ha x (h_all_pos x)
    order_preserving := fun x y => by
      constructor
      · -- x ≤ y → Θ(x) ≤ Θ(y)
        intro hxy
        exact Θ_cuts_pnat_mono a ha (h_all_pos x) (h_all_pos y) hxy
      · -- Θ(x) ≤ Θ(y) → x ≤ y (contrapositive via strict mono)
        intro hΘ
        by_contra h
        push Not at h
        have hlt := Θ_cuts_pnat_strictMono a ha (h_all_pos y) (h_all_pos x) h
        exact not_le_of_gt hlt hΘ
    additive := fun x y => by
      -- h_add uses isPositive_op' for the positivity proof, but our Θ uses h_all_pos (op x y)
      -- These are equal by proof irrelevance, so convert handles the mismatch
      have h_add := Θ_cuts_pnat_add a ha hcomm x y (h_all_pos x) (h_all_pos y)
      convert h_add using 2 }

/-- Strict monotonicity for identity-free cuts representation. -/
theorem cuts_pnat_representation_strictMono
    (a : α) (ha : IsPositive a) (h_all_pos : ∀ x : α, IsPositive x)
    (hcomm : ∀ u v : α, op u v = op v u)
    {x y : α} (hxy : x < y) :
    (cuts_pnat_representation a ha h_all_pos hcomm).Θ x <
    (cuts_pnat_representation a ha h_all_pos hcomm).Θ y :=
  Θ_cuts_pnat_strictMono a ha (h_all_pos x) (h_all_pos y) hxy

end IdentityFreeUnifiedInterface

end KnuthSkilling.Additive.Proofs.DirectCuts
