/-
# Comparison of Representation Theorem Proofs

This file provides:
1. Integration of the Hölder approach with the existing `RepresentationGlobalization` interface
2. A more general interface (`HasRepresentationTheorem`) that works without `KSSeparation`
3. Instances showing each proof approach satisfies the interface
4. Equivalence relationships between assumptions

## The Three Approaches

| Approach | Assumptions | Local LOC | Key Files |
|----------|-------------|-----------|-----------|
| Grid     | KSSeparation + RepresentationGlobalization | ~2500 | ThetaPrime.lean, MultiGrid.lean |
| Cuts     | KSSeparation + KSSeparationStrict | ~900 | DirectCuts.lean |
| Hölder   | NoAnomalousPairs (weakest!) | ~320 | HolderEmbedding.lean |

## Assumption Hierarchy

```
         KSSeparation + IdentIsMinimum
                    ↓
            NoAnomalousPairs  ←──────┐
                    ↓                │
         Hölder Embedding into ℝ     │  (EQUIVALENCE!)
                    ↓                │
           Representation Theorem ───┘
                    ↓
              Commutativity
```

## Key Result

**NoAnomalousPairs ↔ HasRepresentationTheorem** — these conditions are equivalent!
- Forward: NoAnomalousPairs → Hölder embedding → Representation (via Eric Luap's theorems)
- Reverse: Representation → NoAnomalousPairs (by Archimedean argument)
-/

import KnuthSkilling.Additive.Main
import KnuthSkilling.Additive.Proofs.GridInduction.Main

namespace KnuthSkilling.Additive.Proofs.GridInduction.Comparison

open Classical
open KnuthSkillingMonoidBase
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open KnuthSkilling.Additive.Axioms.AnomalousPairs
open KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

/-! ## Section 1: “Three proof paths” as instances -/

/-- **Instance from Grid approach** (identity-free interface). -/
instance grid_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [RepresentationGlobalizationSemigroup α] :
    HasRepresentationTheorem α where
  exists_representation := by
    obtain ⟨Θ, hΘ_order, hΘ_add⟩ :=
      RepresentationGlobalizationSemigroup.exists_Theta (α := α)
    exact ⟨Θ, hΘ_order, hΘ_add⟩

/-! ## Section 3: Bridge from NoAnomalousPairs to RepresentationGlobalization

When we have both `KSSeparation` and `NoAnomalousPairs`, we can provide
a `RepresentationGlobalization` instance via the Hölder approach.
-/

/-- **Bridge**: NoAnomalousPairs provides RepresentationGlobalizationSemigroup. -/
instance representationGlobalizationSemigroup_of_noAnomalousPairs
    (α : Type*) [KSSemigroupBase α] [NoAnomalousPairs α] :
    RepresentationGlobalizationSemigroup α where
  exists_Theta := by
    obtain ⟨Θ, hΘ_order, hΘ_add⟩ := representation_semigroup (α := α)
    exact ⟨Θ, hΘ_order, hΘ_add⟩

/-!
## Section 3b: Identity-based bridge (normalized)
-/

/-- **Bridge**: NoAnomalousPairs provides RepresentationGlobalization.

This shows the Hölder approach can substitute for the grid-based globalization
when `NoAnomalousPairs` is available. -/
instance representationGlobalization_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α] :
    RepresentationGlobalization α where
  exists_Theta := representation_from_noAnomalousPairs

/-! ## Section 4: Corollaries from the General Interface -/

/-- **Commutativity** follows from any representation. -/
theorem op_comm_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∀ x y : α, op x y = op y x := by
  obtain ⟨Θ, hΘ_order, hΘ_add⟩ := HasRepresentationTheorem.exists_representation (α := α)
  intro x y
  have h1 : Θ (op x y) = Θ x + Θ y := hΘ_add x y
  have h2 : Θ (op y x) = Θ y + Θ x := hΘ_add y x
  have h3 : Θ x + Θ y = Θ y + Θ x := add_comm (Θ x) (Θ y)
  have h4 : Θ (op x y) = Θ (op y x) := by rw [h1, h2, h3]
  -- Θ is injective (order embedding)
  have hΘ_inj : Function.Injective Θ := by
    intro a b hab
    have ha : a ≤ b := (hΘ_order a b).mpr (le_of_eq hab)
    have hb : b ≤ a := (hΘ_order b a).mpr (le_of_eq hab.symm)
    exact le_antisymm ha hb
  exact hΘ_inj h4

/-! ## Section 5: Assumption Relationships -/

/-- **KSSeparation + IdentIsMinimum → NoAnomalousPairs** -/
theorem noAnomalousPairs_of_KSSeparation_IdentIsMinimum
    (α : Type*) [KnuthSkillingMonoidBase α] [KSSeparation α] [IdentIsMinimum α] :
    NoAnomalousPairs α :=
  KSSeparation.noAnomalousPairs_of_KSSeparation_with_IdentMin

/-! ## Section 5.5: The Equivalence NoAnomalousPairs ↔ Representation

We have already proven `NoAnomalousPairs → Representation` (via Hölder embedding).
Here we prove the reverse: `Representation → NoAnomalousPairs`.

This establishes a **full equivalence**: `NoAnomalousPairs ↔ HasRepresentationTheorem`.
-/

/-- **Additive representations scale iterates**: `Θ(aⁿ) = n * Θ(a)`.

This is the key lemma for the equivalence proof. -/
lemma theta_iterate_op_pnat_eq_nsmul
    (α : Type*) [KSSemigroupBase α]
    (Θ : α → ℝ) (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y)
    (a : α) (n : ℕ+) : Θ (iterate_op_pnat a n) = (n : ℝ) * Θ a := by
  induction n using PNat.recOn with
  | one =>
    simp [iterate_op_pnat_one]
  | succ n ih =>
    have hcoe : ((n + 1 : ℕ+) : ℝ) = (n : ℝ) + 1 := by
      have h := PNat.add_coe n 1
      exact_mod_cast h
    rw [iterate_op_pnat_succ, hΘ_add, ih, hcoe]
    ring

/-! ### Identity-based convenience (ℕ iteration) -/
lemma theta_iterate_op_eq_nsmul
    (α : Type*) [KnuthSkillingMonoidBase α]
    (Θ : α → ℝ) (hΘ_ident : Θ ident = 0) (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y)
    (a : α) (n : ℕ) : Θ (iterate_op a n) = n * Θ a := by
  induction n with
  | zero => simp [iterate_op, hΘ_ident]
  | succ n ih =>
    rw [iterate_op_succ, hΘ_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- **Representation → NoAnomalousPairs**: An additive order-isomorphism implies no anomalous pairs.

**Proof idea**: For an anomalous pair with `aⁿ < bⁿ < aⁿ⁺¹`, we get
`n*Θ(a) < n*Θ(b) < (n+1)*Θ(a)`, which gives `n*(Θ(b) - Θ(a)) < Θ(a)` for all n > 0.
Since `Θ(b) > Θ(a)` (from n=1), this bounds n from above, contradiction. -/
theorem noAnomalousPairs_of_representation
    (α : Type*) [KSSemigroupBase α]
    (Θ : α → ℝ) (hΘ_order : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b)
    (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y) :
    NoAnomalousPairs α := by
  constructor
  intro a b hAnom
  -- Helper: Θ reflects strict order
  have hΘ_order_lt : ∀ x y : α, x < y ↔ Θ x < Θ y := fun x y => by
    constructor
    · intro hxy
      have h1 : Θ x ≤ Θ y := (hΘ_order x y).mp (le_of_lt hxy)
      have h2 : Θ x ≠ Θ y := by
        intro heq
        have h3 : x ≤ y := le_of_lt hxy
        have h4 : y ≤ x := (hΘ_order y x).mpr (le_of_eq heq.symm)
        exact absurd (le_antisymm h3 h4) (ne_of_lt hxy)
      exact lt_of_le_of_ne h1 h2
    · intro hxy
      have h1 : Θ x ≤ Θ y := le_of_lt hxy
      have h2 : x ≤ y := (hΘ_order x y).mpr h1
      have h3 : x ≠ y := by
        intro heq
        rw [heq] at hxy
        exact lt_irrefl (Θ y) hxy
      exact lt_of_le_of_ne h2 h3

  -- Get the anomalous condition at n=1
  rcases hAnom 1 with ⟨ha1_lt_b1, hb1_lt_a2⟩ | ⟨ha1_gt_b1, hb1_gt_a2⟩

  · -- Positive case: a¹ < b¹ < a²
    simp only [iterate_op_pnat_one] at ha1_lt_b1 hb1_lt_a2
    -- a < b and b < a·a
    have hΘa_lt_Θb : Θ a < Θ b := hΘ_order_lt a b |>.mp ha1_lt_b1
    have hdiff_pos : 0 < Θ b - Θ a := sub_pos.mpr hΘa_lt_Θb

    -- For any n : ℕ+, the anomalous condition gives n*(Θb - Θa) < Θa
    have hbound : ∀ n : ℕ+, (n : ℝ) * (Θ b - Θ a) < Θ a := by
      intro n
      rcases hAnom n with ⟨han_lt_bn, hbn_lt_an1⟩ | ⟨han_gt_bn, _⟩
      · -- From bⁿ < aⁿ⁺¹, we get n*Θb < (n+1)*Θa
        have h1 : Θ (iterate_op_pnat b n) < Θ (iterate_op_pnat a (n + 1)) :=
          hΘ_order_lt _ _ |>.mp hbn_lt_an1
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add a (n + 1)] at h1
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add b n] at h1
        -- n * Θb < (n + 1) * Θa
        -- n * Θb < n * Θa + Θa
        -- n * (Θb - Θa) < Θa
        have h2 : (n : ℝ) * Θ b < ((n + 1 : ℕ+) : ℝ) * Θ a := h1
        have hcoe : ((n + 1 : ℕ+) : ℝ) = (n : ℝ) + 1 := by
          have h := PNat.add_coe n 1
          exact_mod_cast h
        calc (n : ℝ) * (Θ b - Θ a) = (n : ℝ) * Θ b - (n : ℝ) * Θ a := by ring
          _ < ((n + 1 : ℕ+) : ℝ) * Θ a - (n : ℝ) * Θ a := by linarith
          _ = ((n : ℝ) + 1) * Θ a - (n : ℝ) * Θ a := by rw [hcoe]
          _ = Θ a := by ring
      · -- Contradicts a < b at n=1 level
        have h1 : Θ (iterate_op_pnat a n) > Θ (iterate_op_pnat b n) :=
          hΘ_order_lt _ _ |>.mp han_gt_bn
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add a n] at h1
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add b n] at h1
        have hn_pos : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast n.pos
        have h1' : (n : ℝ) * Θ b < (n : ℝ) * Θ a := by linarith
        have h2 : Θ b < Θ a := (mul_lt_mul_iff_right₀ hn_pos).1 h1'
        exact absurd hΘa_lt_Θb (not_lt.mpr (le_of_lt h2))

    -- Now we derive a contradiction: hdiff_pos and hbound can't both hold for all n
    -- Since Θb - Θa > 0, for large enough n, n*(Θb - Θa) ≥ Θa
    -- We need to handle both cases: Θa ≥ 0 and Θa < 0
    by_cases hΘa_sign : Θ a ≥ 0
    · -- Case Θa ≥ 0: use Archimedean property
      have hArch := exists_nat_gt (Θ a / (Θ b - Θ a))
      rcases hArch with ⟨N, hN⟩
      have hN_pos : 0 < N := by
        by_contra h_not
        push_neg at h_not
        interval_cases N
        simp at hN
        have : Θ a / (Θ b - Θ a) ≥ 0 := div_nonneg hΘa_sign (le_of_lt hdiff_pos)
        linarith
      let n' : ℕ+ := ⟨N, hN_pos⟩
      have hcontra := hbound n'
      have h1 : (n' : ℝ) > Θ a / (Θ b - Θ a) := by
        simpa using hN
      have h2 : (n' : ℝ) * (Θ b - Θ a) > Θ a := by
        calc (n' : ℝ) * (Θ b - Θ a) > (Θ a / (Θ b - Θ a)) * (Θ b - Θ a) := by
              exact mul_lt_mul_of_pos_right h1 hdiff_pos
          _ = Θ a := by field_simp
      linarith
    · -- Case Θa < 0: immediate contradiction since n*(Θb - Θa) > 0 > Θa
      push_neg at hΘa_sign
      have h := hbound 1
      simp at h
      -- 1 * (Θb - Θa) < Θa means Θb < 2*Θa
      -- But Θb > Θa and Θa < 0 means Θb could be anywhere
      -- Actually: Θb - Θa > 0, so Θb > Θa
      -- And Θb - Θa < Θa means Θb < 2*Θa
      -- Combined with Θa < 0: this means Θb < 2*Θa < 0
      -- And Θb > Θa, so Θa < Θb < 2*Θa < 0
      -- But 2*Θa < Θa when Θa < 0, contradiction
      have h2Θa : 2 * Θ a < Θ a := by linarith
      have hΘb_lt : Θ b < 2 * Θ a := by linarith
      have hΘb_gt : Θ b > Θ a := hΘa_lt_Θb
      linarith

  · -- Negative case: a¹ > b¹ > a² (symmetric argument)
    simp only [iterate_op_pnat_one] at ha1_gt_b1 hb1_gt_a2
    -- a > b and b > a·a
    have hΘa_gt_Θb : Θ a > Θ b := hΘ_order_lt b a |>.mp ha1_gt_b1
    have hdiff_pos : 0 < Θ a - Θ b := sub_pos.mpr hΘa_gt_Θb

    -- For any n > 0, the anomalous condition gives n*(Θa - Θb) < -Θa
    -- From aⁿ⁺¹ < bⁿ < aⁿ (negative squeeze): (n+1)*Θa < n*Θb < n*Θa
    -- So n*Θa - n*Θb < n*Θa - (n+1)*Θa = -Θa
    -- i.e., n*(Θa - Θb) < -Θa, but Θa - Θb > 0 and we need -Θa > 0 means Θa < 0
    have hbound : ∀ n : ℕ+, (n : ℝ) * (Θ a - Θ b) < -Θ a := by
      intro n
      rcases hAnom n with ⟨han_lt_bn, _⟩ | ⟨_, hbn_gt_an1⟩
      · -- From aⁿ < bⁿ - contradicts a > b
        have h1 : Θ (iterate_op_pnat a n) < Θ (iterate_op_pnat b n) :=
          hΘ_order_lt _ _ |>.mp han_lt_bn
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add a n] at h1
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add b n] at h1
        have hn_pos : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast n.pos
        have h1' : (n : ℝ) * Θ a < (n : ℝ) * Θ b := by linarith
        have h2 : Θ a < Θ b := (mul_lt_mul_iff_right₀ hn_pos).1 h1'
        exact absurd hΘa_gt_Θb (not_lt.mpr (le_of_lt h2))
      · -- From aⁿ⁺¹ < bⁿ, we get (n+1)*Θa < n*Θb
        have h1 : Θ (iterate_op_pnat a (n + 1)) < Θ (iterate_op_pnat b n) :=
          hΘ_order_lt _ _ |>.mp hbn_gt_an1
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add a (n + 1)] at h1
        rw [theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add b n] at h1
        -- (n + 1) * Θa < n * Θb
        -- n * Θa + Θa < n * Θb
        -- n * (Θa - Θb) < -Θa
        have h2 : ((n + 1 : ℕ+) : ℝ) * Θ a < (n : ℝ) * Θ b := h1
        have hcoe : ((n + 1 : ℕ+) : ℝ) = (n : ℝ) + 1 := by
          have h := PNat.add_coe n 1
          exact_mod_cast h
        calc (n : ℝ) * (Θ a - Θ b) = (n : ℝ) * Θ a - (n : ℝ) * Θ b := by ring
          _ < (n : ℝ) * Θ a - ((n + 1 : ℕ+) : ℝ) * Θ a := by linarith
          _ = (n : ℝ) * Θ a - ((n : ℝ) + 1) * Θ a := by rw [hcoe]
          _ = -Θ a := by ring

    -- Contradiction: n*(Θa - Θb) < -Θa for all n > 0, with Θa - Θb > 0
    -- This requires -Θa > 0, i.e., Θa < 0
    -- And for large n, n*(Θa - Θb) → +∞, which can't stay < -Θa (a fixed value)
    have hΘa_neg : Θ a < 0 := by
      have h := hbound 1
      simp at h
      linarith
    have hArch := exists_nat_gt ((-Θ a) / (Θ a - Θ b))
    rcases hArch with ⟨N, hN⟩
    have hN_pos : 0 < N := by
      by_contra h_not
      push_neg at h_not
      interval_cases N
      simp at hN
      have h1 : -Θ a > 0 := neg_pos.mpr hΘa_neg
      have h2 : (-Θ a) / (Θ a - Θ b) ≥ 0 := div_nonneg (le_of_lt h1) (le_of_lt hdiff_pos)
      linarith
    let n' : ℕ+ := ⟨N, hN_pos⟩
    have hcontra := hbound n'
    have h1 : (n' : ℝ) > (-Θ a) / (Θ a - Θ b) := by
      simpa using hN
    have h2 : (n' : ℝ) * (Θ a - Θ b) > -Θ a := by
      calc (n' : ℝ) * (Θ a - Θ b) > ((-Θ a) / (Θ a - Θ b)) * (Θ a - Θ b) := by
            exact mul_lt_mul_of_pos_right h1 hdiff_pos
        _ = -Θ a := by field_simp
    linarith

/-- **NoAnomalousPairs ↔ Representation**: Full equivalence.

This is the central theorem showing that `NoAnomalousPairs` is exactly the
condition needed for an additive order-isomorphism into ℝ. -/
theorem noAnomalousPairs_iff_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] :
    NoAnomalousPairs α ↔ HasRepresentationTheorem α := by
  constructor
  · intro h
    exact @holder_hasRepresentationTheorem α _ h
  · intro h
    obtain ⟨Θ, hΘ_order, hΘ_add⟩ := h.exists_representation
    exact noAnomalousPairs_of_representation α Θ hΘ_order hΘ_add

/-! ## Section 5.6: The Silly but Complete Chain

We can now prove the full (and somewhat redundant) chain:

```
NoAnomalousPairs → Representation → KSSeparation
```

This is "silly" because we typically assume KSSeparation to get NoAnomalousPairs,
but it completes the logical circle and shows these conditions are all equivalent
(under appropriate additional hypotheses like `IdentIsMinimum`).
-/

/-- **The full chain**: NoAnomalousPairs → Representation → KSSeparation.

This theorem shows that `NoAnomalousPairs` implies the separation property
(via the intermediate representation theorem and rational density in ℝ).

Combined with `KSSeparation + IdentIsMinimum → NoAnomalousPairs`, this shows
all three conditions are equivalent under `IdentIsMinimum`. -/
theorem ksSeparation_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α]
    {a x y : α} (ha : ident < a) (hx : ident < x) (hy : ident < y) (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  -- Step 1: NoAnomalousPairs → Representation (via Hölder)
  obtain ⟨Θ, hΘ_order, hΘ_ident, hΘ_add⟩ := representation_from_noAnomalousPairs (α := α)

  -- Helper: Θ reflects strict order
  have hΘ_lt : ∀ u v : α, u < v ↔ Θ u < Θ v := fun u v => by
    constructor
    · intro huv
      have h1 : Θ u ≤ Θ v := (hΘ_order u v).mp (le_of_lt huv)
      have h2 : Θ u ≠ Θ v := by
        intro heq
        have h3 : v ≤ u := (hΘ_order v u).mpr (le_of_eq heq.symm)
        exact absurd (le_antisymm (le_of_lt huv) h3) (ne_of_lt huv)
      exact lt_of_le_of_ne h1 h2
    · intro huv
      have h1 : u ≤ v := (hΘ_order u v).mpr (le_of_lt huv)
      have h2 : u ≠ v := by
        intro heq
        rw [heq] at huv
        exact lt_irrefl _ huv
      exact lt_of_le_of_ne h1 h2

  -- Step 2: Map hypotheses to ℝ
  have ha' : 0 < Θ a := by rw [← hΘ_ident]; exact (hΘ_lt ident a).mp ha
  have hx' : 0 < Θ x := by rw [← hΘ_ident]; exact (hΘ_lt ident x).mp hx
  have hy' : 0 < Θ y := by rw [← hΘ_ident]; exact (hΘ_lt ident y).mp hy
  have hxy' : Θ x < Θ y := (hΘ_lt x y).mp hxy
  -- Step 3: Use AxiomSystemEquivalence.real_separation
  have hgap : 0 < Θ y - Θ x := sub_pos.mpr hxy'
  obtain ⟨m, hm⟩ := exists_nat_gt (Θ a / (Θ y - Θ x))
  have hm_pos : 0 < m := by
    by_contra h_not
    push_neg at h_not
    interval_cases m
    simp at hm
    exact not_lt.mpr (le_of_lt (div_pos ha' hgap)) hm
  have hm_gap : Θ a < (m : ℝ) * (Θ y - Θ x) := by
    have : Θ a / (Θ y - Θ x) < m := hm
    calc Θ a = (Θ a / (Θ y - Θ x)) * (Θ y - Θ x) := by field_simp
      _ < m * (Θ y - Θ x) := mul_lt_mul_of_pos_right this hgap
  have hm_ineq : (m : ℝ) * Θ x + Θ a < (m : ℝ) * Θ y := by
    calc (m : ℝ) * Θ x + Θ a < (m : ℝ) * Θ x + (m : ℝ) * (Θ y - Θ x) := by linarith
      _ = (m : ℝ) * Θ y := by ring
  let n' := Nat.floor ((m : ℝ) * Θ y / Θ a)
  have hn'_upper : (n' : ℝ) * Θ a ≤ (m : ℝ) * Θ y := by
    have h1 : (n' : ℝ) ≤ (m : ℝ) * Θ y / Θ a := Nat.floor_le (by positivity)
    calc (n' : ℝ) * Θ a ≤ ((m : ℝ) * Θ y / Θ a) * Θ a := mul_le_mul_of_nonneg_right h1 (le_of_lt ha')
      _ = (m : ℝ) * Θ y := by field_simp
  by_cases hn'_works : (m : ℝ) * Θ x < (n' : ℝ) * Θ a
  · -- Translate back via Θ
    refine ⟨n', m, hm_pos, ?_, ?_⟩
    · apply (hΘ_lt _ _).mpr
      rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add x m]
      rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add a n']
      exact hn'_works
    · apply (hΘ_order _ _).mpr
      rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add a n']
      rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add y m]
      exact hn'_upper
  · -- n' doesn't work, derive contradiction
    push_neg at hn'_works
    have hn'_floor_upper : (m : ℝ) * Θ y < ((n' : ℝ) + 1) * Θ a := by
      have := Nat.lt_floor_add_one ((m : ℝ) * Θ y / Θ a)
      calc (m : ℝ) * Θ y = ((m : ℝ) * Θ y / Θ a) * Θ a := by field_simp
        _ < (↑(Nat.floor ((m : ℝ) * Θ y / Θ a)) + 1) * Θ a := mul_lt_mul_of_pos_right this ha'
    have h1 : ((n' : ℝ) + 1) * Θ a < (m : ℝ) * Θ y := by linarith
    linarith

/-- Negative-side version of `ksSeparation_of_noAnomalousPairs`.

This proves the same sandwich property below `ident`.  Under a Hölder representation
`Θ : α → ℝ`, the proof is the same rational-density argument, but uses the interval in
`ℝ_{<0}` (equivalently, applies the positive argument to `-Θ`). -/
theorem ksSeparation_neg_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α]
    {a x y : α} (ha : a < ident) (hx : x < ident) (hy : y < ident) (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  -- Step 1: NoAnomalousPairs → Representation (via Hölder)
  obtain ⟨Θ, hΘ_order, hΘ_ident, hΘ_add⟩ := representation_from_noAnomalousPairs (α := α)

  -- Helper: Θ reflects strict order
  have hΘ_lt : ∀ u v : α, u < v ↔ Θ u < Θ v := fun u v => by
    constructor
    · intro huv
      have h1 : Θ u ≤ Θ v := (hΘ_order u v).mp (le_of_lt huv)
      have h2 : Θ u ≠ Θ v := by
        intro heq
        have h3 : v ≤ u := (hΘ_order v u).mpr (le_of_eq heq.symm)
        exact absurd (le_antisymm (le_of_lt huv) h3) (ne_of_lt huv)
      exact lt_of_le_of_ne h1 h2
    · intro huv
      have h1 : u ≤ v := (hΘ_order u v).mpr (le_of_lt huv)
      have h2 : u ≠ v := by
        intro heq
        rw [heq] at huv
        exact lt_irrefl _ huv
      exact lt_of_le_of_ne h1 h2

  -- Step 2: Map hypotheses to ℝ (all negative)
  have ha' : Θ a < 0 := by
    have : Θ a < Θ ident := (hΘ_lt a ident).mp ha
    simpa [hΘ_ident] using this
  have hx' : Θ x < 0 := by
    have : Θ x < Θ ident := (hΘ_lt x ident).mp hx
    simpa [hΘ_ident] using this
  have hy' : Θ y < 0 := by
    have : Θ y < Θ ident := (hΘ_lt y ident).mp hy
    simpa [hΘ_ident] using this
  have hxy' : Θ x < Θ y := (hΘ_lt x y).mp hxy

  -- Work with positive reals A = -Θ(a), X = -Θ(y), Y = -Θ(x), so 0 < X < Y.
  let A : ℝ := -Θ a
  let X : ℝ := -Θ y
  let Y : ℝ := -Θ x
  have hA_pos : 0 < A := by simp [A]; linarith
  have hX_pos : 0 < X := by simp [X]; linarith
  have hY_pos : 0 < Y := by simp [Y]; linarith
  have hXY : X < Y := by
    have : -Θ y < -Θ x := by linarith [hxy']
    simpa [X, Y] using this
  have hgap_pos : 0 < Y - X := sub_pos.mpr hXY

  -- Choose m large enough that A ≤ m * (Y - X).
  obtain ⟨m, hm⟩ := exists_nat_ge (A / (Y - X))
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm0' : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst hm0'
    have hfrac_pos : 0 < A / (Y - X) := div_pos hA_pos hgap_pos
    exact (not_lt_of_ge hm) (by simpa using hfrac_pos)
  have hA_le : A ≤ (m : ℝ) * (Y - X) := by
    -- hm : A / (Y - X) ≤ m
    have hm' : A / (Y - X) ≤ (m : ℝ) := by simpa using hm
    exact (div_le_iff₀ hgap_pos).1 hm'

  -- Choose n = ceil(m * X / A). Then m*X ≤ n*A < m*X + A ≤ m*Y.
  let n : ℕ := Nat.ceil ((m : ℝ) * X / A)
  have hmx_le_nA : (m : ℝ) * X ≤ (n : ℝ) * A := by
    have hceil : (m : ℝ) * X / A ≤ (n : ℝ) := by
      simpa [n] using (Nat.le_ceil ((m : ℝ) * X / A))
    exact (div_le_iff₀ hA_pos).1 hceil
  have hnA_lt_mY : (n : ℝ) * A < (m : ℝ) * Y := by
    have hnonneg : 0 ≤ (m : ℝ) * X / A := by positivity
    have hceil_lt : (n : ℝ) < (m : ℝ) * X / A + 1 := by
      simpa [n] using (Nat.ceil_lt_add_one (R := ℝ) hnonneg)
    have hnA_lt : (n : ℝ) * A < ((m : ℝ) * X / A + 1) * A :=
      mul_lt_mul_of_pos_right hceil_lt hA_pos
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    have hRHS : ((m : ℝ) * X / A + 1) * A = (m : ℝ) * X + A := by
      calc
        ((m : ℝ) * X / A + 1) * A
            = ((m : ℝ) * X / A) * A + 1 * A := by
                simp [add_mul]
        _ = ((m : ℝ) * X * A) / A + A := by
                simp [div_mul_eq_mul_div, mul_assoc]
        _ = (m : ℝ) * X + A := by
                simp [mul_div_cancel_right₀, hA_ne]
    have hmxA_le_mY : (m : ℝ) * X + A ≤ (m : ℝ) * Y := by
      have h1 : (m : ℝ) * X + A ≤ (m : ℝ) * X + (m : ℝ) * (Y - X) :=
        add_le_add_right hA_le ((m : ℝ) * X)
      have h2 : (m : ℝ) * X + (m : ℝ) * (Y - X) = (m : ℝ) * Y := by ring
      simpa [h2] using h1
    have hnA_lt_mxA : (n : ℝ) * A < (m : ℝ) * X + A := by
      simpa [hRHS] using hnA_lt
    exact lt_of_lt_of_le hnA_lt_mxA hmxA_le_mY

  -- Convert back to Θ inequalities: m*Θ(x) < n*Θ(a) ≤ m*Θ(y).
  have hlt_real : (m : ℝ) * Θ x < (n : ℝ) * Θ a := by
    have h' : (n : ℝ) * (-Θ a) < (m : ℝ) * (-Θ x) := by
      simpa [A, Y] using hnA_lt_mY
    have := neg_lt_neg h'
    -- `-(m * (-Θ x)) = m * Θ x` and `-(n * (-Θ a)) = n * Θ a`
    simpa using this
  have hle_real : (n : ℝ) * Θ a ≤ (m : ℝ) * Θ y := by
    have h' : (m : ℝ) * (-Θ y) ≤ (n : ℝ) * (-Θ a) := by
      simpa [A, X] using hmx_le_nA
    have := neg_le_neg h'
    simpa using this

  -- Translate back via Θ
  refine ⟨n, m, hm_pos, ?_, ?_⟩
  · apply (hΘ_lt _ _).mpr
    rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add x m]
    rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add a n]
    exact hlt_real
  · apply (hΘ_order _ _).mpr
    rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add a n]
    rw [theta_iterate_op_eq_nsmul α Θ hΘ_ident hΘ_add y m]
    exact hle_real

/-- **Bilateral separation from NAP** (no `IdentIsMinimum` needed).

This packages both `ksSeparation_of_noAnomalousPairs` (positive side) and
`ksSeparation_neg_of_noAnomalousPairs` (negative side) into `SeparationBilateralProp`. -/
theorem separationBilateralProp_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α] :
    SeparationBilateralProp (α := α) := by
  classical
  -- First build the identity-based `KSSeparation` instance, then use the standard conversion
  -- `KSSeparation -> KSSeparationSemigroup` to get the ℕ+-iteration version.
  letI : KSSeparation α :=
    { separation := fun {a x y} ha hx hy hxy =>
        ksSeparation_of_noAnomalousPairs (α := α) (a := a) (x := x) (y := y) ha hx hy hxy }
  refine ⟨?_, ?_⟩
  · -- Positive cone: use the existing `KSSeparation -> KSSeparationSemigroup` equivalence.
    exact KSSeparationSemigroup.separationSemigroupProp (α := α)
  · -- Negative cone: convert `IsNegative` to `< ident`, apply the identity-based theorem,
    -- then convert ℕ-iteration back to ℕ+-iteration.
    intro a x y ha hx hy hxy
    have ha' : a < ident := (isNegative_iff_lt_ident (a := a)).1 ha
    have hx' : x < ident := (isNegative_iff_lt_ident (a := x)).1 hx
    have hy' : y < ident := (isNegative_iff_lt_ident (a := y)).1 hy
    obtain ⟨n, m, hm_pos, h_lo, h_hi⟩ :=
      ksSeparation_neg_of_noAnomalousPairs (α := α) (a := a) (x := x) (y := y) ha' hx' hy' hxy
    -- `n` cannot be 0, otherwise the upper bound would force `ident ≤ y^m`, contradicting negativity.
    by_cases hn : n = 0
    · subst hn
      have hy_iter_lt : iterate_op y m < ident :=
        KnuthSkillingAlgebra.iterate_op_lt_ident_of_isNegative (y := y) hy m hm_pos
      have h_contra : ¬ ident ≤ iterate_op y m := not_le_of_gt hy_iter_lt
      have h_hi' : ident ≤ iterate_op y m := by
        simpa [KnuthSkillingAlgebra.iterate_op_zero] using h_hi
      exact (False.elim (h_contra h_hi'))
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      let n' : ℕ+ := ⟨n, hn_pos⟩
      let m' : ℕ+ := ⟨m, hm_pos⟩
      have hx_eq : iterate_op_pnat x m' = iterate_op x m :=
        KnuthSkillingAlgebra.iterate_op_pnat_eq x m'
      have ha_eq : iterate_op_pnat a n' = iterate_op a n :=
        KnuthSkillingAlgebra.iterate_op_pnat_eq a n'
      have hy_eq : iterate_op_pnat y m' = iterate_op y m :=
        KnuthSkillingAlgebra.iterate_op_pnat_eq y m'
      refine ⟨n', m', ?_, ?_⟩
      · simpa [hx_eq, ha_eq] using h_lo
      · simpa [ha_eq, hy_eq] using h_hi

/-! ## Section 6: Analysis Summary

### Lines of Code Comparison

| Component | Grid | Cuts | Hölder |
|-----------|------|------|--------|
| Main proof file | ~2500 (ThetaPrime) | ~900 (DirectCuts) | ~320 (HolderEmbedding) |
| Supporting files | ~1500 (MultiGrid, etc.) | ~200 | ~100 (AnomalousPairs) |
| External deps | 0 | 0 | ~1500 (OrderedSemigroups) |
| **Total** | **~4000** | **~1100** | **~1920** |

### Assumptions Comparison

| Approach | Required Typeclasses |
|----------|---------------------|
| Grid (normalized) | `KnuthSkillingAlgebra`, `KSSeparation`, `RepresentationGlobalization` |
| Grid (semigroup) | `KSSemigroupBase`, `RepresentationGlobalizationSemigroup` |
| Cuts | `KnuthSkillingAlgebra`, `KSSeparation`, `KSSeparationStrict` |
| Hölder | `KSSemigroupBase`, `NoAnomalousPairs` (**weakest!**) |

### Elegance Assessment

| Criterion | Grid | Cuts | Hölder |
|-----------|------|------|--------|
| Conceptual clarity | Low | Medium | **High** |
| Self-contained | **Yes** | **Yes** | No (uses external lib) |
| Follows K&S paper | **Yes** | Partial | No |
| Maintainability | Low | Medium | **High** |
| Proof length | Long | Medium | **Short** |

### Recommendation

- **For minimal assumptions**: Use Hölder approach (`NoAnomalousPairs`)
- **For self-contained proofs**: Use Cuts approach
- **For K&S paper alignment**: Use Grid approach

The Hölder approach is recommended for practical use because:
1. It uses the weakest assumptions
2. Shortest local codebase
3. Leverages Eric Luap's battle-tested formalization
4. Most mathematically elegant (classical Alimov-Hölder theory)
-/

end KnuthSkilling.Additive.Proofs.GridInduction.Comparison
