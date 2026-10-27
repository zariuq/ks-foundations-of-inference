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

import KnuthSkilling.Additive.Axioms.AnomalousPairs
import KnuthSkilling.Additive.Representation
import KnuthSkilling.Additive.Proofs.GridInduction.GlobalizationInterface
-- Import Eric's OrderedSemigroups
import OrderedSemigroups.Holder
-- Import for Multiplicative type tag lemmas
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Subsemigroup.Defs

namespace KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

open Classical
open KSSemigroupBase
open KnuthSkilling.Additive.Axioms.AnomalousPairs
open KnuthSkilling.Additive
open Multiplicative (toAdd ofAdd)
open Subsemigroup

variable {α : Type*}

section Semigroup

variable [KSSemigroupBase α]

/-! ## Section 1: K&S Semigroup provides Semigroup structure

We show that a `KSSemigroupBase` naturally gives rise to a `Semigroup`
with `mul := op`.
-/

/-- The K&S `op` operation viewed as multiplication. -/
instance KSSemigroupBase_to_Semigroup : Semigroup α := KSSemigroupBase.toSemigroup

/-! ## Section 2: K&S Semigroup is an Ordered Cancel Semigroup -/

/-- K&S semigroup is a left ordered semigroup (left multiplication preserves order). -/
instance KSSemigroupBase_to_IsLeftOrderedSemigroup : IsLeftOrderedSemigroup α where
  mul_le_mul_left' a b hab c := by
    -- Need: a ≤ b → c * a ≤ c * b, i.e., op c a ≤ op c b
    exact KSSemigroupBase.op_mono_right c hab

/-- K&S semigroup is a right ordered semigroup (right multiplication preserves order). -/
instance KSSemigroupBase_to_IsRightOrderedSemigroup : IsRightOrderedSemigroup α where
  mul_le_mul_right' a b hab c := by
    -- Need: a ≤ b → a * c ≤ b * c, i.e., op a c ≤ op b c
    exact KSSemigroupBase.op_mono_left c hab

/-! K&S semigroup is a left ordered cancel semigroup. -/
instance KSSemigroupBase_to_IsLeftOrderedCancelSemigroup : IsLeftOrderedCancelSemigroup α where
  mul_le_mul_left' := IsLeftOrderedSemigroup.mul_le_mul_left'
  le_of_mul_le_mul_right' a _b _c hab := (op_strictMono_right a).le_iff_le.mp hab

/-! K&S semigroup is a right ordered cancel semigroup. -/
instance KSSemigroupBase_to_IsRightOrderedCancelSemigroup : IsRightOrderedCancelSemigroup α where
  mul_le_mul_right' := IsRightOrderedSemigroup.mul_le_mul_right'
  le_of_mul_le_mul_left' a _b _c hab := (op_strictMono_left a).le_iff_le.mp hab

/-- K&S semigroup is an ordered cancel semigroup. -/
instance KSSemigroupBase_to_IsOrderedCancelSemigroup : IsOrderedCancelSemigroup α where
  mul_le_mul_left' := IsLeftOrderedSemigroup.mul_le_mul_left'
  le_of_mul_le_mul_right' := IsLeftOrderedCancelSemigroup.le_of_mul_le_mul_right'
  mul_le_mul_right' := IsRightOrderedSemigroup.mul_le_mul_right'
  le_of_mul_le_mul_left' := IsRightOrderedCancelSemigroup.le_of_mul_le_mul_left'

/-! ## Section 3: ℕ+ Powers for OrderedSemigroups -/

/-- `ℕ+`-powering via K&S iteration. -/
instance KSSemigroupBase_to_PowPNat : Pow α ℕ+ where
  pow x n := iterate_op_pnat x n

/-- Power associativity for `ℕ+` iteration. -/
instance KSSemigroupBase_to_PNatPowAssoc : PNatPowAssoc α where
  ppow_add k n x := by
    -- x^(k+n) = x^k * x^n
    change iterate_op_pnat x (k + n) = op (iterate_op_pnat x k) (iterate_op_pnat x n)
    exact iterate_op_pnat_add x k n
  ppow_one x := by
    change iterate_op_pnat x 1 = x
    exact iterate_op_pnat_one x

/-! ## Section 4: Definition equivalence

Our `AnomalousPair a b` is equivalent to Eric's `anomalous_pair a b`.
-/

/-- Our anomalous pair definition matches Eric's structurally. -/
theorem anomalousPair_iff_eric (a b : α) :
    AnomalousPair a b ↔ anomalous_pair a b := Iff.rfl

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
  exact iso.map_le_map_iff'.symm

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

end Semigroup

section WithIdentity

variable [KnuthSkillingMonoidBase α]
open KnuthSkillingMonoidBase KnuthSkillingAlgebra

theorem theta_ident [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    theta_from_embedding G iso ident = 0 := by
  let r : RepresentationResult α :=
    ⟨theta_from_embedding G iso, theta_preserves_order G iso, theta_additive G iso⟩
  exact r.ident_zero_of_ident

end WithIdentity

section Semigroup

variable [KSSemigroupBase α]


/-! ## Section 8: Identity-Free Representation (Semigroup Version)

The Hölder/Alimov embedding does NOT require identity. This section makes that explicit.

**What identity provides:**
- An identity necessarily maps to zero by additivity.
- A positive anchor fixes the remaining multiplicative scale by mapping to one.
- A nonzero additive shift does not preserve additivity, even without identity.

**K&S reference:** Lines 320, 340-342 of "Foundations of Inference" (2012) state
that the bottom element (identity) is "optional" in the lattice framework. -/

/-- **Semigroup Representation Theorem**: NoAnomalousPairs implies additive embedding into ℝ.
    This version requires no identity and retains the supplied additive operation. -/
theorem representation_semigroup [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) := by
  obtain ⟨G, ⟨iso⟩⟩ := holder_embedding_of_noAnomalousPairs (α := α)
  use theta_from_embedding G iso
  exact ⟨theta_preserves_order G iso, theta_additive G iso⟩

/-! ## Section 9: Normalized Representation (with identity) -/

/-- Hölder path produces a RepresentationResult (identity-free). -/
noncomputable def holder_representation [NoAnomalousPairs α] : RepresentationResult α :=
  let h := representation_semigroup (α := α)
  { Θ := Classical.choose h
    order_preserving := (Classical.choose_spec h).1
    additive := (Classical.choose_spec h).2 }

end Semigroup

section WithIdentity

variable [KnuthSkillingMonoidBase α]
open KnuthSkillingMonoidBase KnuthSkillingAlgebra

/-- **K&S Appendix A via Hölder**: `NoAnomalousPairs α` implies the representation theorem.

This is an alternative to the `KSSeparation`-based proof, using Eric's complete
Hölder embedding theorem. -/
theorem representation_from_noAnomalousPairs [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  obtain ⟨G, ⟨iso⟩⟩ := holder_embedding_of_noAnomalousPairs (α := α)
  use theta_from_embedding G iso
  exact ⟨theta_preserves_order G iso, theta_ident G iso, theta_additive G iso⟩

/-- Archimedean-style bound from `NoAnomalousPairs`.

Under the Hölder/Alimov embedding into `ℝ`, the real Archimedean property implies that for any
base `a > ident` and any `x`, some iterate `a^n` bounds `x` from above. -/
theorem archimedean_of_noAnomalousPairs [NoAnomalousPairs α] (a x : α) (ha : ident < a) :
    ∃ n : ℕ, x ≤ iterate_op a n := by
  let r := (holder_representation (α := α)).toNormalized
  have hpos : 0 < r.Θ a := by
    simpa [r.ident_zero] using (r.strict_order_preserving ident a).mp ha
  obtain ⟨n, hn⟩ := exists_nat_ge (r.Θ x / r.Θ a)
  refine ⟨n, (r.order_preserving _ _).mpr ?_⟩
  rw [r.toRepresentationResult.map_iterate]
  exact (div_le_iff₀ hpos).mp hn

/-- An identity maps to zero because the representation preserves addition. -/
theorem identity_gives_canonical_normalization [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    theta_from_embedding G iso ident = 0 :=
  theta_ident G iso

/-- Minimal uniqueness theorem (identity-only):

If two real-valued representations are:
- order-preserving
- additive for `op`
- normalized at the identity (`Θ(ident)=0`)

then, once we choose a single reference element `a > ident`, the two representations differ
by a positive multiplicative scale factor.

This version does **not** assume `ident_le` (i.e. it only needs `KnuthSkillingMonoidBase`),
so it is reusable outside the probability-theory setting. -/
theorem representation_uniqueness_structure_of_ref
    (Θ₁ Θ₂ : α → ℝ)
    (h1_ord : ∀ a b : α, a ≤ b ↔ Θ₁ a ≤ Θ₁ b)
    (h2_ord : ∀ a b : α, a ≤ b ↔ Θ₂ a ≤ Θ₂ b)
    (h1_add : ∀ x y : α, Θ₁ (op x y) = Θ₁ x + Θ₁ y)
    (h2_add : ∀ x y : α, Θ₂ (op x y) = Θ₂ x + Θ₂ y)
    (h1_ident : Θ₁ ident = 0)
    (h2_ident : Θ₂ ident = 0)
    (a : α) (ha_pos : ident < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, Θ₂ x = c * Θ₁ x := by
  let r : NormalizedRepresentationResult α := ⟨⟨Θ₁, h1_ord, h1_add⟩, h1_ident⟩
  let t : NormalizedRepresentationResult α := ⟨⟨Θ₂, h2_ord, h2_add⟩, h2_ident⟩
  exact r.toRepresentationResult.unique_up_to_posScale t.toRepresentationResult a
    ((isPositive_iff_ident_lt a).mpr ha_pos)

end WithIdentity

section IdentIsMin

variable [KnuthSkillingAlgebraBase α]
open KnuthSkillingAlgebraBase KnuthSkillingAlgebra

/-- The representation is unique up to positive scaling.
    Additivity forces Θ(ident) = 0; a positive reference fixes the scale.

    Proof strategy: Both embeddings respect the same order structure on iterates, so
    a^m ≤ x^n ↔ m·Θ₁(a) ≤ n·Θ₁(x) ↔ m·Θ₂(a) ≤ n·Θ₂(x).
    This forces Θ₁(x)/Θ₁(a) = Θ₂(x)/Θ₂(a) for positive elements. -/
theorem representation_uniqueness_structure [NoAnomalousPairs α]
    (Θ₁ Θ₂ : α → ℝ)
    (h1_ord : ∀ a b : α, a ≤ b ↔ Θ₁ a ≤ Θ₁ b)
    (h2_ord : ∀ a b : α, a ≤ b ↔ Θ₂ a ≤ Θ₂ b)
    (h1_add : ∀ x y : α, Θ₁ (op x y) = Θ₁ x + Θ₁ y)
    (h2_add : ∀ x y : α, Θ₂ (op x y) = Θ₂ x + Θ₂ y)
    (h1_ident : Θ₁ ident = 0)
    (h2_ident : Θ₂ ident = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, Θ₂ x = c * Θ₁ x := by
  classical
  by_cases htriv : ∀ x : α, x = ident
  · refine ⟨1, one_pos, fun x => ?_⟩
    simp only [htriv x, h1_ident, h2_ident, mul_zero]
  push Not at htriv
  obtain ⟨a, ha_ne⟩ := htriv
  have ha_pos : ident < a := lt_of_le_of_ne (ident_le a) (Ne.symm ha_ne)
  exact
    representation_uniqueness_structure_of_ref (α := α)
      Θ₁ Θ₂ h1_ord h2_ord h1_add h2_add h1_ident h2_ident a ha_pos

/-! ## Normalized Hölder Representation -/

/-- Hölder path produces a NormalizedRepresentationResult (with identity). -/
noncomputable def holder_normalized_representation [NoAnomalousPairs α] :
    NormalizedRepresentationResult α :=
  (holder_representation (α := α)).toNormalized

/-! ## Unified Representation Interface

The common interfaces `RepresentationResult` and `NormalizedRepresentationResult` live in
`KnuthSkilling.Additive.Representation`. -/

/-! ## Grid Path Representation

The grid path uses `KSSeparation` + globalization to produce representations.
Grid iteration uses `iterate_op x 0 = ident`, so identity is required for the construction.

**Identity-free separation (`KSSeparationSemigroup`)**:
- Uses `IsPositive` (Eric Luap's approach) instead of `ident < a`
- Uses `iterate_op_pnat` (ℕ+ iteration) instead of `iterate_op` (ℕ iteration)
- When identity exists: `KSSeparation ↔ KSSeparationSemigroup` (see `Algebra.lean`)

The parametric grid constructions (`mu_param`, `kGrid_param`) allow shifting
the base element, but the grid path itself produces `NormalizedRepresentationResult`
with the canonical `Θ(ident) = 0` normalization. -/

section GridPath
open KnuthSkilling.Additive in
variable {α : Type*} [KnuthSkillingMonoidBase α] [RepresentationGlobalization α]

open KnuthSkilling.Additive in
/-- Grid path produces a NormalizedRepresentationResult (with identity).
    This wraps the `RepresentationGlobalization` class into our unified interface. -/
noncomputable def grid_normalized_representation {α : Type*}
    [KnuthSkillingMonoidBase α] [RepresentationGlobalization α] :
    NormalizedRepresentationResult α :=
  let h := RepresentationGlobalization.exists_Theta (α := α)
  { Θ := Classical.choose h
    order_preserving := (Classical.choose_spec h).1
    additive := (Classical.choose_spec h).2.2
    ident_zero := (Classical.choose_spec h).2.1 }

open KnuthSkilling.Additive in
/-- Grid path from `KSSeparationSemigroup` (when identity exists).

    When identity exists, `KSSeparationSemigroup` implies `KSSeparation` via
    the equivalence in `Algebra.lean`. This function shows the integration. -/
noncomputable def grid_normalized_representation_from_semigroup_sep {α : Type*}
    [KnuthSkillingMonoidBase α] [RepresentationGlobalization α] :
    NormalizedRepresentationResult α :=
  grid_normalized_representation (α := α)

open KnuthSkilling.Additive in
/-- Grid path produces a RepresentationResult (identity-free interface).

    This extracts just the order + additivity properties from the normalized result.
    Since `NormalizedRepresentationResult` extends `RepresentationResult`, this is
    a simple extraction. The grid construction internally uses identity, but the
    resulting `Θ : α → ℝ` doesn't depend on `Θ(ident) = 0` for its properties.

    **Use case**: When you want to work with the unified `RepresentationResult`
    interface across all paths (Hölder, Grid, Cuts) without committing to identity. -/
noncomputable def grid_representation {α : Type*}
    [KnuthSkillingMonoidBase α] [RepresentationGlobalization α] :
    RepresentationResult α :=
  (grid_normalized_representation (α := α)).toRepresentationResult

end GridPath

/-! ## Comparing supplied routes

Hölder consumes an identity-free no-anomalous-pairs profile. Grid consumes a
normalized globalization witness. Ordinary cuts consume minimum identity and
strict separation; positive-only cuts retain explicit commutativity.
On a common carrier their resulting additive order embeddings agree after
calibration. Ordered event histories remain separate data: equal calibrated endpoints can
come from different authored orders and different intermediate observations.
-/

section PathEquivalence

open KnuthSkilling.Additive
open KnuthSkillingAlgebraBase KSSemigroupBase

/-- **Path Equivalence Theorem**: The Hölder and Grid paths produce equivalent representations.

Both `holder_normalized_representation` and `grid_normalized_representation` satisfy order + additivity + ident=0.
By `representation_uniqueness_structure`, they're related by positive scaling.

This is a foundational result: K&S representation is unique up to scale,
regardless of which construction path is used. -/
theorem holder_grid_paths_equivalent {α : Type*}
    [KnuthSkillingAlgebraBase α] [NoAnomalousPairs α] [KSSeparation α] [RepresentationGlobalization α] :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, (grid_normalized_representation (α := α)).Θ x =
      c * (holder_normalized_representation (α := α)).Θ x := by
  exact representation_uniqueness_structure
    (holder_normalized_representation (α := α)).Θ
    (grid_normalized_representation (α := α)).Θ
    (holder_normalized_representation (α := α)).order_preserving
    (grid_normalized_representation (α := α)).order_preserving
    (holder_normalized_representation (α := α)).additive
    (grid_normalized_representation (α := α)).additive
    (holder_normalized_representation (α := α)).ident_zero
    (grid_normalized_representation (α := α)).ident_zero

/-- The Hölder path is the canonical identity-free representation.
    When identity exists, other paths are equivalent to it. -/
theorem holder_is_canonical {α : Type*} [KnuthSkillingAlgebraBase α] [NoAnomalousPairs α] :
    ∀ R : NormalizedRepresentationResult α,
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, R.Θ x = c * (holder_normalized_representation (α := α)).Θ x :=
  fun R => representation_uniqueness_structure
    (holder_normalized_representation (α := α)).Θ
    R.Θ
    (holder_normalized_representation (α := α)).order_preserving
    R.order_preserving
    (holder_normalized_representation (α := α)).additive
    R.additive
    (holder_normalized_representation (α := α)).ident_zero
    R.ident_zero

end PathEquivalence

end IdentIsMin

end KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding
