/-
# Sandwich separation and its consequences

Positive sandwich separation supplies unbounded iteration and commutativity on
the positive cone. A minimum identity then extends commutativity to the whole
carrier. None of these conclusions is a field of the base algebra.

The commutativity proof compares ordered repetitions of `x ⊕ y` and `y ⊕ x`.
Its word inequalities use associativity and strict monotonicity, without assuming
that arbitrary rearrangements already have equal values. Separation contradicts
the inequality that would follow from unequal orders of the two products.
-/

import KnuthSkilling.Core.Algebra

namespace KnuthSkilling

open Classical
open KnuthSkillingMonoidBase KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
## Part 1: `KSSeparation` → Archimedean

The Archimedean property states: for any a > ident and any x, there exists n such that x < a^n.

If `KSSeparation` holds, then for x with ident < x < x⊕x (which is always true for x > ident),
we can find n, m with x^m < a^n. Since m ≥ 1, this gives us bounds.

`KSSeparation` derives Archimedean — it is NOT assumed as an axiom. This file provides the
theorem `op_archimedean_of_separation` which derives the Archimedean property from `KSSeparation`.
The base `KnuthSkillingAlgebra` is now an alias for `KnuthSkillingAlgebraBase` (no Archimedean axiom).

`KSSeparation` also implies commutativity (via `op_comm_of_KSSeparation` below).
-/

namespace SandwichSeparation

/-!
### Base Structure

This development splits assumptions by sub-result:
- Archimedean-style consequences use only `KnuthSkillingMonoidBase` + `KSSeparation`.
- Commutativity on the positive cone uses only `KnuthSkillingMonoidBase` + `KSSeparation`.
- Global commutativity additionally uses `KnuthSkillingAlgebraBase` (the `ident_le` reduction).

Both are defined in the main K&S modules:
- `KnuthSkilling.Basic` (`KnuthSkillingAlgebraBase`)
- `KnuthSkilling.Algebra` (`iterate_op` and `KSSeparation`)
-/

/-!
### Theorem 1: `KSSeparation` → Archimedean

If separation holds, then for any a > ident and any x, we can find n with x < a^n.
-/

namespace SeparationToArchimedean

variable {α : Type*} [KnuthSkillingMonoidBase α]

/-- Archimedean-style bound for *positive* `x` (no `ident_le` needed).

If `x > ident`, apply separation to `x < x ⊕ x`, producing `x^m < a^n`. Since `m ≥ 1`,
monotonicity of iterates gives `x = x^1 ≤ x^m < a^n`. -/
theorem archimedean_of_separation_pos [KSSeparation α] (a : α) (ha : ident < a) (x : α)
    (hx : ident < x) : ∃ n : ℕ, x ≤ iterate_op a n := by
  -- x < x ⊕ x
  have hx_lt_xx : x < op x x := by
    calc x = op ident x := (op_ident_left x).symm
      _ < op x x := op_strictMono_left x hx
  have hx_xx_pos : ident < op x x := lt_trans hx hx_lt_xx
  -- Separate between x and x⊕x using base a
  rcases KSSeparation.separation (a := a) (x := x) (y := op x x) ha hx hx_xx_pos hx_lt_xx with
    ⟨n, m, hm_pos, hxm_lt_an, _⟩
  -- x ≤ x^m for m ≥ 1
  have hmono : Monotone (iterate_op x) := (iterate_op_strictMono x hx).monotone
  have hm1 : 1 ≤ m := Nat.succ_le_iff.mp hm_pos
  have hx_le_xm : x ≤ iterate_op x m := by
    -- iterate_op x 1 = x
    simpa [iterate_op_one] using (hmono hm1)
  exact ⟨n, le_of_lt (lt_of_le_of_lt hx_le_xm hxm_lt_an)⟩

/-- Any element is bounded by some power of any base element above identity.

For `x ≤ ident`, take `n = 0`. For `x > ident`, reduce to `archimedean_of_separation_pos`. -/
theorem archimedean_of_separation [KSSeparation α] (a : α) (ha : ident < a) (x : α) :
    ∃ n : ℕ, x ≤ iterate_op a n := by
  by_cases hx : x ≤ ident
  · exact ⟨0, by simpa [iterate_op_zero] using hx⟩
  · have hx' : ident < x := lt_of_not_ge hx
    exact archimedean_of_separation_pos (α := α) a ha x hx'

/-- Nat.iterate (op a) n a equals iterate_op a (n + 1) -/
theorem nat_iterate_eq_iterate_op_succ (a : α) (n : ℕ) :
    Nat.iterate (op a) n a = iterate_op a (n + 1) := by
  exact KnuthSkillingAlgebra.nat_iterate_eq_iterate_op_succ a n

/-- The Archimedean property follows from `KSSeparation`. -/
theorem op_archimedean_of_separation [KSSeparation α] (a : α) (x : α) (ha : ident < a) :
    ∃ n : ℕ, x < Nat.iterate (op a) n a := by
  obtain ⟨k, hk⟩ := archimedean_of_separation a ha x
  refine ⟨k, ?_⟩
  rw [nat_iterate_eq_iterate_op_succ]
  exact lt_of_le_of_lt hk ((iterate_op_strictMono a ha) (Nat.lt_succ_self k))

/-- The Archimedean property in `iterate_op` form: for any positive `a` and any `x`,
there exists `n` such that `x < iterate_op a n`. This is the form used throughout the
K&S formalization. -/
theorem bounded_by_iterate [KSSeparation α] (a : α) (ha : ident < a) (x : α) :
    ∃ n : ℕ, x < iterate_op a n := by
  -- Get the Nat.iterate form from op_archimedean_of_separation
  obtain ⟨k, hk⟩ := op_archimedean_of_separation a x ha
  -- Convert: (op a)^[k] a = iterate_op a (k + 1)
  use k + 1
  rw [← nat_iterate_eq_iterate_op_succ]
  exact hk

end SeparationToArchimedean

/-!
### Part 2: `KSSeparation` → Commutativity (mass counting)

This is proved below using a “mass counting” argument: for `x,y > ident` and exponents
`n > m ≥ 1`, we can show `(x ⊕ y)^n > (y ⊕ x)^m` purely by associativity and strict
monotonicity (no commutativity needed).

If `x ⊕ y ≠ y ⊕ x`, then by trichotomy we may assume `x ⊕ y < y ⊕ x`. Applying
`KSSeparation` with base `a := x ⊕ y` produces exponents `n,m` with
`(x ⊕ y)^m < (x ⊕ y)^n ≤ (y ⊕ x)^m`, forcing `m < n`. The mass-counting inequality then
contradicts the upper bound.
-/

namespace CommutativityProof

variable {α : Type*} [KnuthSkillingMonoidBase α]

/-- Helper: iterate_op is strictly monotone in exponent for positive base -/
theorem iterate_op_strictMono_exp (a : α) (ha : ident < a) : StrictMono (iterate_op a) := by
  exact KnuthSkillingAlgebra.iterate_op_strictMono a ha

end CommutativityProof

/-!
## `KSSeparation` → Commutativity

This file proves that `KSSeparation` implies commutativity via a "mass counting"
argument: both (x⊕y)^n and (y⊕x)^n contain the same multiset of atoms (n copies of x
and n copies of y), so having more iterations always beats having fewer.

The key lemma is `y_op_xy_pow_gt_yx_pow`: y ⊕ (x⊕y)^k > (y⊕x)^k for all k ≥ 1.
This enables `xy_succ_gt_yx`: (x⊕y)^{k+1} > (y⊕x)^k, which combined with
`KSSeparation`'s sandwich constraint yields `ksSeparation_implies_comm`.
-/

namespace ThetaAdditivity

variable {α : Type*} [KnuthSkillingMonoidBase α]

/-!
### The Mass Counting Argument

The conceptual idea is that both (x⊕y)^m and (y⊕x)^m contain exactly m copies of x
and m copies of y, so they should have the same "growth rate" θ. This intuition guides
our formal proof, but we bypass defining θ explicitly: instead, we directly prove that
(x⊕y)^n > (y⊕x)^m when n > m, using associativity to reorganize atoms.
-/

/-!
### The Core "More Atoms = Larger" Lemma

This is the key structural result: (x⊕y)^n > (y⊕x)^m when n > m.

The proof uses associativity to show that (x⊕y)^n contains "more positive stuff"
than (y⊕x)^m, regardless of how the elements are arranged.
-/

/-- Base case: (x⊕y)^2 > (y⊕x)^1

Proof:
  iterate_op (op x y) 2 = (x⊕y) ⊕ (x⊕y) [by iterate_op def]
  Using associativity and monotonicity, show this exceeds y⊕x.
-/
theorem xy_sq_gt_yx (x y : α) (hx : ident < x) (hy : ident < y) :
    iterate_op (op x y) 2 > iterate_op (op y x) 1 := by
  -- iterate_op (op x y) 2 = (x⊕y) ⊕ iterate_op (op x y) 1 = (x⊕y) ⊕ (x⊕y)
  have h_expand : iterate_op (op x y) 2 = op (op x y) (iterate_op (op x y) 1) := rfl
  rw [iterate_op_one] at h_expand
  -- So iterate_op (op x y) 2 = (x⊕y) ⊕ (x⊕y)
  -- By assoc: (x⊕y) ⊕ (x⊕y) = x ⊕ (y ⊕ (x ⊕ y))
  have h2 : op (op x y) (op x y) = op x (op y (op x y)) := by rw [op_assoc x y (op x y)]
  -- y ⊕ (x ⊕ y) = (y ⊕ x) ⊕ y by associativity
  have h3 : op y (op x y) = op (op y x) y := by rw [op_assoc y x y]
  -- (y ⊕ x) ⊕ y > y ⊕ x by right monotonicity (since y > ident)
  have h4 : op (op y x) y > op y x := by
    calc op (op y x) y > op (op y x) ident := op_strictMono_right (op y x) hy
      _ = op y x := op_ident_right (op y x)
  -- x ⊕ ((y ⊕ x) ⊕ y) > x ⊕ (y ⊕ x) by right mono
  have h5 : op x (op (op y x) y) > op x (op y x) := op_strictMono_right x h4
  -- x ⊕ (y ⊕ x) > y ⊕ x by left mono (since x > ident)
  have h6 : op x (op y x) > op y x := by
    calc op x (op y x) > op ident (op y x) := op_strictMono_left (op y x) hx
      _ = op y x := op_ident_left (op y x)
  -- Chain
  rw [h_expand]
  calc op (op x y) (op x y)
      = op x (op y (op x y)) := h2
    _ = op x (op (op y x) y) := by rw [h3]
    _ > op x (op y x) := h5
    _ > op y x := h6
    _ = iterate_op (op y x) 1 := (iterate_op_one (op y x)).symm

/-- Key intermediate lemma: y ⊕ (x⊕y)^k > (y⊕x)^k for all k ≥ 1

This is proved by induction using associativity:
- Base k=1: y ⊕ (x⊕y) = (y⊕x) ⊕ y > y⊕x
- Inductive step uses restructuring via associativity
-/
theorem y_op_xy_pow_gt_yx_pow (x y : α) (_hx : ident < x) (hy : ident < y)
    (k : ℕ) (hk : k ≥ 1) :
    op y (iterate_op (op x y) k) > iterate_op (op y x) k := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- Base case k = 1: y ⊕ (x⊕y)^1 = y ⊕ (x⊕y) > y⊕x
      rw [iterate_op_one, iterate_op_one]
      -- y ⊕ (x⊕y) = (y⊕x) ⊕ y by associativity
      have h1 : op y (op x y) = op (op y x) y := by rw [op_assoc y x y]
      rw [h1]
      -- (y⊕x) ⊕ y > (y⊕x) ⊕ ident = y⊕x
      calc op (op y x) y > op (op y x) ident := op_strictMono_right (op y x) hy
        _ = op y x := op_ident_right (op y x)
    | succ m =>
      -- Induction step: k = m + 2
      -- IH: op y (iterate_op (op x y) (m + 1)) > iterate_op (op y x) (m + 1)
      have ih_applied : op y (iterate_op (op x y) (m + 1)) > iterate_op (op y x) (m + 1) :=
        ih (Nat.le_add_left 1 m)

      -- Key: Use associativity to restructure y ⊕ (x⊕y)^{m+2}
      -- y ⊕ ((x⊕y) ⊕ (x⊕y)^{m+1}) = (y ⊕ (x⊕y)) ⊕ (x⊕y)^{m+1}  [by assoc]
      -- = ((y⊕x) ⊕ y) ⊕ (x⊕y)^{m+1}  [by assoc on y ⊕ (x⊕y)]
      -- = (y⊕x) ⊕ (y ⊕ (x⊕y)^{m+1})  [by assoc in reverse]

      have assoc1 : op y (op (op x y) (iterate_op (op x y) (m + 1))) =
          op (op y (op x y)) (iterate_op (op x y) (m + 1)) := by
        rw [op_assoc y (op x y) (iterate_op (op x y) (m + 1))]

      have assoc2 : op y (op x y) = op (op y x) y := by rw [op_assoc y x y]

      have assoc3 : op (op (op y x) y) (iterate_op (op x y) (m + 1)) =
          op (op y x) (op y (iterate_op (op x y) (m + 1))) := by
        rw [op_assoc (op y x) y (iterate_op (op x y) (m + 1))]

      calc op y (iterate_op (op x y) (m + 2))
          = op y (op (op x y) (iterate_op (op x y) (m + 1))) := rfl
        _ = op (op y (op x y)) (iterate_op (op x y) (m + 1)) := assoc1
        _ = op (op (op y x) y) (iterate_op (op x y) (m + 1)) := by rw [assoc2]
        _ = op (op y x) (op y (iterate_op (op x y) (m + 1))) := assoc3
        _ > op (op y x) (iterate_op (op y x) (m + 1)) := op_strictMono_right (op y x) ih_applied
        _ = iterate_op (op y x) (m + 2) := rfl

/-- Generalization: (x⊕y)^{k+1} > (y⊕x)^k for all k ≥ 1

Uses y_op_xy_pow_gt_yx_pow and transitivity.
-/
theorem xy_succ_gt_yx (x y : α) (hx : ident < x) (hy : ident < y) (k : ℕ) (hk : k ≥ 1) :
    iterate_op (op x y) (k + 1) > iterate_op (op y x) k := by
  -- (x⊕y)^{k+1} = (x⊕y) ⊕ (x⊕y)^k = x ⊕ (y ⊕ (x⊕y)^k) by associativity
  have assoc : op (op x y) (iterate_op (op x y) k) =
      op x (op y (iterate_op (op x y) k)) := by
    rw [op_assoc x y (iterate_op (op x y) k)]

  -- y ⊕ (x⊕y)^k > (y⊕x)^k by the intermediate lemma
  have h1 : op y (iterate_op (op x y) k) > iterate_op (op y x) k :=
    y_op_xy_pow_gt_yx_pow x y hx hy k hk

  -- x ⊕ (y ⊕ (x⊕y)^k) > x ⊕ (y⊕x)^k by right monotonicity
  have h2 : op x (op y (iterate_op (op x y) k)) > op x (iterate_op (op y x) k) :=
    op_strictMono_right x h1

  -- x ⊕ (y⊕x)^k > (y⊕x)^k by left monotonicity
  have h3 : op x (iterate_op (op y x) k) > iterate_op (op y x) k := by
    calc op x (iterate_op (op y x) k)
        > op ident (iterate_op (op y x) k) := op_strictMono_left _ hx
      _ = iterate_op (op y x) k := op_ident_left _

  calc iterate_op (op x y) (k + 1)
      = op (op x y) (iterate_op (op x y) k) := rfl
    _ = op x (op y (iterate_op (op x y) k)) := assoc
    _ > op x (iterate_op (op y x) k) := h2
    _ > iterate_op (op y x) k := h3

/-- The main comparison lemma: for n > m ≥ 1, (x⊕y)^n > (y⊕x)^m

This is the "mass counting" result formalized: more copies of positive atoms
always yield a strictly larger result, regardless of arrangement.
-/
theorem xy_pow_gt_yx_pow (x y : α) (hx : ident < x) (hy : ident < y)
    (n m : ℕ) (hm : m ≥ 1) (hnm : n > m) :
    iterate_op (op x y) n > iterate_op (op y x) m := by
  -- The proof uses:
  -- 1. (x⊕y)^{k+1} > (y⊕x)^k for all k ≥ 1 (from xy_succ_gt_yx)
  -- 2. iterate_op is strictly increasing in exponent
  -- 3. Chain: (x⊕y)^n > (x⊕y)^{m+1} > (y⊕x)^m when n > m

  have hxy_pos : ident < op x y := by
    calc ident < x := hx
      _ = op x ident := (op_ident_right x).symm
      _ < op x y := op_strictMono_right x hy

  cases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hnm) with
  | inl h_n_gt_m_plus_1 =>
    -- n > m + 1, so n ≥ m + 2
    -- (x⊕y)^n > (x⊕y)^{m+1} > (y⊕x)^m
    have h1 : iterate_op (op x y) n > iterate_op (op x y) (m + 1) :=
      CommutativityProof.iterate_op_strictMono_exp (op x y) hxy_pos h_n_gt_m_plus_1
    have h2 : iterate_op (op x y) (m + 1) > iterate_op (op y x) m :=
      xy_succ_gt_yx x y hx hy m hm
    exact lt_trans h2 h1
  | inr h_n_eq_m_plus_1 =>
    -- n = m + 1 (note: h_n_eq_m_plus_1 : m.succ = n, i.e., m + 1 = n)
    rw [← h_n_eq_m_plus_1]
    exact xy_succ_gt_yx x y hx hy m hm

/-!
### Step 4: The Main Theorem
-/

/-- **Main Theorem**: `KSSeparation` implies commutativity.

Paper cross-reference:
- `paper/ks-formalization.tex`, Section “Commutativity from Separation” (label `sec:commutativity`).
- Theorem “Separation Implies Commutativity” (label `thm:sep-comm`).

Proof Structure:
1. Assume x⊕y < y⊕x (for contradiction)
2. Apply `KSSeparation` to get n, m with (x⊕y)^m < (x⊕y)^n ≤ (y⊕x)^m and n > m
3. By mass counting: (x⊕y)^n > (y⊕x)^m (because n > m and both have same "atoms per unit")
4. This contradicts step 2's upper bound (x⊕y)^n ≤ (y⊕x)^m

  The mass counting argument (step 3) is implemented directly as `xy_pow_gt_yx_pow`:
  for `n > m ≥ 1`, we prove `(x⊕y)^n > (y⊕x)^m` by associativity + strict monotonicity,
  without introducing an explicit “growth rate” function `θ`.
  -/
theorem ksSeparation_implies_comm [KSSeparation α] (x y : α) (hx : ident < x) (hy : ident < y) :
    op x y = op y x := by
  have no_lt : ∀ u v : α, ident < u → ident < v → ¬ op u v < op v u := by
    intro u v hu hv huv
    have hp : ident < op u v := lt_trans hu (by simpa [op_ident_right] using op_strictMono_right u hv)
    obtain ⟨n, m, hm, hlo, hhi⟩ :=
      KSSeparation.separation (a := op u v) hp hp (lt_trans hp huv) huv
    have hmn : m < n := (CommutativityProof.iterate_op_strictMono_exp _ hp).lt_iff_lt.mp hlo
    exact (not_le_of_gt (xy_pow_gt_yx_pow u v hu hv n m hm hmn)) hhi
  exact le_antisymm (le_of_not_gt (no_lt y x hy hx)) (le_of_not_gt (no_lt x y hx hy))

end ThetaAdditivity

/-! A convenience corollary: the commutativity theorem is global (handles identity cases). -/
/-- Global (identity-safe) commutativity corollary for the mass-counting proof.

Paper cross-reference:
- `paper/ks-formalization.tex`, Theorem “Separation Implies Commutativity” (label `thm:sep-comm`). -/
theorem ksSeparation_implies_commutative
    {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α] :
    ∀ x y : α, op x y = op y x := by
  intro x y
  by_cases hx : x = ident (α := α)
  · subst hx
    simp [op_ident_left, op_ident_right]
  by_cases hy : y = ident (α := α)
  · subst hy
    simp [op_ident_left, op_ident_right]
  have hx_pos :
      ident (α := α) < x :=
    lt_of_le_of_ne (ident_le x) (Ne.symm hx)
  have hy_pos :
      ident (α := α) < y :=
    lt_of_le_of_ne (ident_le y) (Ne.symm hy)
  simpa using
    ThetaAdditivity.ksSeparation_implies_comm (α := α) (x := x) (y := y) hx_pos hy_pos

/-! ## Separating models

The semidirect counterexample is Archimedean and noncommutative; the lexicographic
product is commutative and non-Archimedean. Both fail separation. Their rank
arguments require a monotone, positive rank that scales under iteration. The
shared obstruction is a strictly ordered triple of positive elements with one
rank value. This does not assert injectivity of every additive observation.

The central word inequalities remain `y_op_xy_pow_gt_yx_pow`, `xy_succ_gt_yx`
and `xy_pow_gt_yx_pow`. They provide the bounds used by the positive-cone theorem;
identity cases are discharged separately in the global corollary. -/

end SandwichSeparation

end KnuthSkilling
