/-
# Hölder Embedding via OrderedSemigroups

This file provides an alternative path to the K&S representation theorem:

  `NoAnomalousPairs α` → Eric's `¬has_anomalous_pair α` → `holder_not_anom` → ℝ embedding

By using Eric Luap's complete Hölder embedding theorem from OrderedSemigroups,
we can derive the representation theorem directly from the no-anomalous-pairs condition,
without needing the custom infrastructure in `AlimovEmbedding.lean`.

## Main Results

- `holder_embedding_of_noAnomalousPairs`: Main embedding theorem
- `representation_from_noAnomalousPairs`: K&S representation from NoAnomalousPairs

## References

- Luap, E. (2024). "OrderedSemigroups: Formalization in Lean 4." github.com/ericluap/OrderedSemigroups
- Alimov, N. G. (1950). "On ordered semigroups." Izv. Akad. Nauk SSSR Ser. Mat. 14, 569–576.

-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs
-- Import Eric's OrderedSemigroups
import OrderedSemigroups.Holder
-- Import for Multiplicative type tag lemmas
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Subsemigroup.Defs

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs
open Multiplicative (toAdd ofAdd)
open Subsemigroup

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-! ## Section 1: K&S Algebra provides Semigroup structure

We show that a `KnuthSkillingAlgebraBase` naturally gives rise to a `Semigroup`
with `mul := op`. The identity `ident` becomes the monoid identity `1`.
-/

/-- The K&S `op` operation viewed as multiplication. -/
instance KSAlgebra_to_Semigroup : Semigroup α where
  mul := op
  mul_assoc := op_assoc

/-- The K&S `ident` as the monoid identity. -/
instance KSAlgebra_to_One : One α where
  one := ident

/-- K&S algebra has a monoid structure (with identity). -/
instance KSAlgebra_to_Monoid : Monoid α where
  mul := op
  mul_assoc := op_assoc
  one := ident
  one_mul := op_ident_left
  mul_one := op_ident_right
  npow n x := iterate_op x n
  npow_zero x := iterate_op_zero x
  npow_succ n x := by
    -- Need: iterate_op x (n + 1) = op (iterate_op x n) x
    -- From iterate_op_add with m=n, n'=1:
    --   op (iterate_op x n) (iterate_op x 1) = iterate_op x (n + 1)
    -- Since iterate_op x 1 = x, we get:
    --   op (iterate_op x n) x = iterate_op x (n + 1)
    have h := iterate_op_add x n 1
    simp only [iterate_op_one] at h
    exact h.symm

/-! ## Section 2: K&S Algebra is an Ordered Cancel Semigroup -/

/-- K&S algebra is a left ordered semigroup (left multiplication preserves order). -/
instance KSAlgebra_to_IsLeftOrderedSemigroup : IsLeftOrderedSemigroup α where
  mul_le_mul_left' a b hab c := by
    -- Need: a ≤ b → c * a ≤ c * b, i.e., op c a ≤ op c b
    rcases hab.lt_or_eq with hlt | heq
    · exact le_of_lt (op_strictMono_right c hlt)
    · rw [heq]

/-- K&S algebra is a right ordered semigroup (right multiplication preserves order). -/
instance KSAlgebra_to_IsRightOrderedSemigroup : IsRightOrderedSemigroup α where
  mul_le_mul_right' a b hab c := by
    -- Need: a ≤ b → a * c ≤ b * c, i.e., op a c ≤ op b c
    rcases hab.lt_or_eq with hlt | heq
    · exact le_of_lt (op_strictMono_left c hlt)
    · rw [heq]

/-- K&S algebra is a left ordered cancel semigroup. -/
instance KSAlgebra_to_IsLeftOrderedCancelSemigroup : IsLeftOrderedCancelSemigroup α where
  mul_le_mul_left' := IsLeftOrderedSemigroup.mul_le_mul_left'
  le_of_mul_le_mul_right' a b c hab := by
    -- Need: a * b ≤ a * c → b ≤ c, i.e., op a b ≤ op a c → b ≤ c
    by_contra h_not
    push_neg at h_not
    have hlt : c < b := h_not
    have hlt' : op a c < op a b := op_strictMono_right a hlt
    exact absurd hab (not_le_of_gt hlt')

/-- K&S algebra is a right ordered cancel semigroup. -/
instance KSAlgebra_to_IsRightOrderedCancelSemigroup : IsRightOrderedCancelSemigroup α where
  mul_le_mul_right' := IsRightOrderedSemigroup.mul_le_mul_right'
  le_of_mul_le_mul_left' a b c hab := by
    -- Signature: ∀ a b c : α, b * a ≤ c * a → b ≤ c
    -- hab : b * a ≤ c * a (i.e., op b a ≤ op c a)
    -- Goal: b ≤ c
    by_contra h_not
    push_neg at h_not
    have hlt : c < b := h_not
    have hlt' : op c a < op b a := op_strictMono_left a hlt
    -- hlt' : op c a < op b a, but hab : op b a ≤ op c a - contradiction
    exact absurd hab (not_le_of_gt hlt')

/-- K&S algebra is an ordered cancel semigroup. -/
instance KSAlgebra_to_IsOrderedCancelSemigroup : IsOrderedCancelSemigroup α where
  mul_le_mul_left' := IsLeftOrderedSemigroup.mul_le_mul_left'
  le_of_mul_le_mul_right' := IsLeftOrderedCancelSemigroup.le_of_mul_le_mul_right'
  mul_le_mul_right' := IsRightOrderedSemigroup.mul_le_mul_right'
  le_of_mul_le_mul_left' := IsRightOrderedCancelSemigroup.le_of_mul_le_mul_left'

/-! ## Section 4: Definition equivalence

Our `AnomalousPair a b` is equivalent to Eric's `anomalous_pair a b`.
-/

/-- Our anomalous pair definition matches Eric's structurally.

Eric uses: `∀n : ℕ+, (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))`
We use:   `∀n : ℕ, 0 < n → (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))`

These are equivalent since ℕ+ ≃ {n : ℕ | 0 < n}.
-/
theorem anomalousPair_iff_eric (a b : α) :
    AnomalousPair a b ↔ anomalous_pair a b := by
  constructor
  · -- Our definition → Eric's
    intro hAnom n
    have hn_pos : 0 < (n : ℕ) := n.pos
    specialize hAnom n hn_pos
    -- Need to convert between iterate_op and ^
    simp only [HPow.hPow, Pow.pow] at hAnom ⊢
    convert hAnom using 2
  · -- Eric's → Our definition
    intro hEric n hn_pos
    specialize hEric ⟨n, hn_pos⟩
    simp only [HPow.hPow, Pow.pow, PNat.mk_coe, PNat.add_coe, PNat.val_ofNat] at hEric ⊢
    exact hEric

/-- No anomalous pairs in our sense ↔ no anomalous pairs in Eric's sense. -/
theorem noAnomalousPairs_iff_eric [NoAnomalousPairs α] :
    ¬has_anomalous_pair (α := α) := by
  intro ⟨a, b, hAnom⟩
  have hOurs : AnomalousPair a b := (anomalousPair_iff_eric a b).mpr hAnom
  exact NoAnomalousPairs.not_anomalous a b hOurs

theorem eric_noAnomalousPairs_to_ours (h : ¬has_anomalous_pair (α := α)) :
    NoAnomalousPairs α := by
  constructor
  intro a b hAnom
  have hEric : anomalous_pair a b := (anomalousPair_iff_eric a b).mp hAnom
  exact h ⟨a, b, hEric⟩

/-! ## Section 6: Main Embedding Theorem

Using Eric's `holder_not_anom`, we get an embedding into ℝ.
-/

/-- **Main Theorem**: If a K&S algebra has no anomalous pairs, it embeds into ℝ.

This is Eric's Hölder theorem specialized to our setting. The embedding is into
`Multiplicative ℝ`, where multiplication corresponds to addition of reals.
Thus, for any `a, b : α`:
- `Θ(op a b) = Θ a + Θ b` (in ℝ)
- `a ≤ b ↔ Θ a ≤ Θ b`
-/
theorem holder_embedding_of_noAnomalousPairs [NoAnomalousPairs α] :
    ∃ G : Subsemigroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  have h : ¬has_anomalous_pair (α := α) := noAnomalousPairs_iff_eric
  exact holder_not_anom h

/-! ## Section 7: Extracting the Representation Function Θ

From the Hölder embedding, we construct the representation function Θ : α → ℝ
satisfying the K&S representation theorem requirements.
-/

/-- From the multiplicative order isomorphism, extract the additive representation.

In `Multiplicative ℝ`, the group operation is `*` which corresponds to `+` in ℝ.
An element `x : Multiplicative ℝ` with `Multiplicative.toAdd x = r` represents
the real number `r`. The group multiplication is `Multiplicative.ofAdd (r + s)`.
-/
noncomputable def theta_from_embedding [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) : α → ℝ :=
  fun a => Multiplicative.toAdd (iso a : Multiplicative ℝ)

theorem theta_preserves_order [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    ∀ a b : α, a ≤ b ↔ theta_from_embedding G iso a ≤ theta_from_embedding G iso b := by
  intro a b
  simp only [theta_from_embedding]
  constructor
  · intro hab
    have h1 : iso a ≤ iso b := iso.map_le_map_iff'.mpr hab
    exact h1
  · intro hθ
    have h1 : iso a ≤ iso b := hθ
    exact iso.map_le_map_iff'.mp h1

theorem theta_ident [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    theta_from_embedding G iso ident = 0 := by
  unfold theta_from_embedding
  -- We need to show: Multiplicative.toAdd (iso ident : Multiplicative ℝ) = 0
  -- This is equivalent to: (iso ident : Multiplicative ℝ) = 1

  -- Use the fact that for all x, ident * x = x, so iso(ident * x) = iso(x)
  -- But iso(ident * x) = iso(ident) * iso(x), so iso(ident) * iso(x) = iso(x)
  have h_left_id : ∀ x : α, op ident x = x := op_ident_left
  -- iso preserves multiplication, so iso(ident * x) = iso(ident) * iso(x)
  have h_map : ∀ x : α, iso (op ident x) = iso ident * iso x := fun x => map_mul iso ident x

  -- Since iso(ident * ident) = iso(ident) and iso(ident * ident) = iso(ident) * iso(ident),
  -- we have iso(ident) * iso(ident) = iso(ident)
  have h1 : (iso ident : G) * iso ident = iso ident := by
    rw [← h_map ident, h_left_id ident]

  -- Coerce to Multiplicative ℝ
  -- In a subsemigroup, multiplication is inherited: (x * y : G).val = x.val * y.val
  have h2 : (↑(iso ident) : Multiplicative ℝ) * ↑(iso ident) = ↑(iso ident) := by
    have h1' := congrArg (·.val) h1
    convert h1' using 1

  -- Convert to additive form: (x * y).toAdd = x.toAdd + y.toAdd
  have h3 : (↑(iso ident) : Multiplicative ℝ).toAdd +
            (↑(iso ident) : Multiplicative ℝ).toAdd =
            (↑(iso ident) : Multiplicative ℝ).toAdd := by
    have := congrArg Multiplicative.toAdd h2
    convert this using 1

  -- From x + x = x, we get x = 0
  linarith

theorem theta_additive [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    ∀ x y : α, theta_from_embedding G iso (op x y) =
               theta_from_embedding G iso x + theta_from_embedding G iso y := by
  intro x y
  unfold theta_from_embedding
  -- iso (x * y) = iso x * iso y, where * is op
  have h : iso (op x y) = iso x * iso y := map_mul iso x y
  simp only [h]
  -- In Multiplicative ℝ: toAdd (a * b) = toAdd a + toAdd b
  rfl

/-! ## Section 8: The Full Representation Theorem from NoAnomalousPairs -/

/-- **K&S Appendix A via Hölder**: `NoAnomalousPairs α` implies the representation theorem.

This is an alternative to the `KSSeparation`-based proof, using Eric's complete
Hölder embedding theorem.
-/
theorem representation_from_noAnomalousPairs [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  obtain ⟨G, ⟨iso⟩⟩ := holder_embedding_of_noAnomalousPairs (α := α)
  use theta_from_embedding G iso
  exact ⟨theta_preserves_order G iso, theta_ident G iso, theta_additive G iso⟩

end Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding
