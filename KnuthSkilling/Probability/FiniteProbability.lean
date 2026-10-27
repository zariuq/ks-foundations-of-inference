import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import KnuthSkilling.Probability.BooleanRepresentation
import KnuthSkilling.Information.InformationEntropy

/-!
# Finite coordinates of Boolean event observations

A normalized Boolean event valuation determines singleton weights. Shared
finite disjoint-additivity laws show that they sum to one and reconstruct
every event probability. The explicit equivalence with `Fin (card Ω)` retains
the original sample-space observations in the finite-distribution representation.
Normalization requires nonzero total weight; zero total weight is not a
probability distribution.
Reference: Knuth and Skilling, “Foundations of Inference” (2012), Appendix A.
-/

namespace KnuthSkilling.Probability.FiniteProbability

open KnuthSkilling.Probability.BooleanRepresentation
open KnuthSkilling.Information.InformationEntropy
open Set Finset BigOperators
open Classical

-- Some theorems (e.g., singleton_disjoint) don't need [Fintype Ω] but share the
-- variable context. These are foundational lemmas that could be more general.

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## §1: Finite Additivity from Modularity

The key lemma: disjoint union has additive probability. This follows from modularity
plus the fact that `P(a ⊓ b) = 0` when `Disjoint a b`.
-/

section FiniteAdditivity

variable (R : KSBooleanRepresentation (Set Ω))

/-- **Disjoint sets have zero intersection probability**.

If `a` and `b` are disjoint sets, then `P(a ∩ b) = P(∅) = 0`. -/
theorem probability_inf_eq_zero_of_disjoint {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : KSBooleanRepresentation (Set Ω)) {a b : Set Ω} (h : Disjoint a b) :
    R.probability (a ⊓ b) = 0 := by
  have hinf : a ⊓ b = ⊥ := h.eq_bot
  simp only [hinf]
  exact R.probability_bot

/-- **Finite additivity on disjoint unions** (core lemma).

For disjoint sets `a` and `b`: `P(a ∪ b) = P(a) + P(b)`.

This follows from:
- Modularity: `P(a ∪ b) + P(a ∩ b) = P(a) + P(b)`
- Disjointness: `P(a ∩ b) = 0`
-/
theorem probability_sup_of_disjoint (h : R.Θ ⊤ ≠ 0) {a b : Set Ω} (hab : Disjoint a b) :
    R.probability (a ⊔ b) = R.probability a + R.probability b := by
  have hmod := R.probability_modular a b h
  have hinf := probability_inf_eq_zero_of_disjoint R hab
  linarith

end FiniteAdditivity

/-! ## §2: Singletons and Set Coverage

Key facts about singletons in a finite type:
- Singletons are pairwise disjoint
- The union of all singletons is the entire space
-/

/-- Singletons are pairwise disjoint. -/
theorem singleton_disjoint {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {ω₁ ω₂ : Ω} (h : ω₁ ≠ ω₂) :
    Disjoint ({ω₁} : Set Ω) {ω₂} := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
  intro hx1 hx2
  rw [hx1] at hx2
  exact h hx2

/-- The union of all singletons is the entire space. -/
theorem iUnion_singleton_eq_univ {Ω : Type*} [Fintype Ω] [DecidableEq Ω] :
    (⋃ ω : Ω, ({ω} : Set Ω)) = Set.univ := by
  ext x
  simp only [mem_iUnion, mem_singleton_iff, mem_univ, iff_true]
  exact ⟨x, rfl⟩

/-- Finite union version using Finset. -/
theorem biUnion_singleton_eq_univ :
    (⋃ ω ∈ (Finset.univ : Finset Ω), ({ω} : Set Ω)) = Set.univ := by
  simp only [Finset.mem_univ, Set.iUnion_true]
  exact iUnion_singleton_eq_univ

/-! ## §3: Sum of Singleton Probabilities

The key step: prove that summing singleton probabilities gives the probability
of the union, using finite induction.
-/

section SingletonSum

variable (R : KSBooleanRepresentation (Set Ω))

/-- **Sum of singleton probabilities equals probability of their union** (via Finset induction).

This is the workhorse lemma for proving `sum_one` in `toProbDist`. -/
theorem probability_sum_singletons (h : R.Θ ⊤ ≠ 0) (s : Finset Ω) :
    ∑ ω ∈ s, R.probability ({ω} : Set Ω) = R.probability (⋃ ω ∈ s, ({ω} : Set Ω)) := by
  have hsup : s.sup (fun ω => ({ω} : Set Ω)) = ⋃ ω ∈ s, ({ω} : Set Ω) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert _ _ hi ih => simp [Finset.sup_insert, ih]
  simpa only [hsup] using
    sum_eq_finset_sup_of_disjoint R.probability R.probability_bot
      (fun _ _ hd => probability_sup_of_disjoint R h hd)
      (fun ω => ({ω} : Set Ω)) (fun _ _ hne => singleton_disjoint hne) s

/-- **Sum over all elements equals probability of entire space**. -/
theorem probability_sum_all_singletons (h : R.Θ ⊤ ≠ 0) :
    ∑ ω : Ω, R.probability ({ω} : Set Ω) = R.probability Set.univ := by
  have h1 : ∑ ω ∈ Finset.univ, R.probability ({ω} : Set Ω) =
      R.probability (⋃ ω ∈ Finset.univ, ({ω} : Set Ω)) :=
    probability_sum_singletons R h Finset.univ
  rw [h1, biUnion_singleton_eq_univ]

/-- **Sum of singleton probabilities equals 1**. -/
theorem probability_sum_singletons_eq_one (h : R.Θ ⊤ ≠ 0) :
    ∑ ω : Ω, R.probability ({ω} : Set Ω) = 1 := by
  rw [probability_sum_all_singletons R h]
  exact R.probability_top h

end SingletonSum

/-! ## §4: The Main Bridge: `toProbDist`

This is the key definition that grounds `ProbDist` on the KS derivation.
-/

section Bridge

variable (R : KSBooleanRepresentation (Set Ω))

/-- **Extract a finite probability distribution from a KS representation**.

Given a `KSBooleanRepresentation (Set Ω)` with non-degenerate total measure,
we extract the probability distribution over `Ω` by taking singleton probabilities.

This is the bridge that grounds `ProbDist` on the KS derivation of probability theory.
-/
noncomputable def toProbDist (h : R.Θ ⊤ ≠ 0) : ProbDist (Fintype.card Ω) where
  p := fun i => R.probability ({(Fintype.equivFin Ω).symm i} : Set Ω)
  nonneg := fun i => R.probability_nonneg _
  sum_one := by
    -- Use the equivalence to rewrite the sum
    have hsum : ∑ i : Fin (Fintype.card Ω), R.probability ({(Fintype.equivFin Ω).symm i} : Set Ω) =
        ∑ ω : Ω, R.probability ({ω} : Set Ω) := by
      rw [← Equiv.sum_comp (Fintype.equivFin Ω).symm]
    rw [hsum]
    exact probability_sum_singletons_eq_one R h

/-- The `i`-th coordinate of `toProbDist` is the probability of the corresponding singleton. -/
theorem toProbDist_apply (h : R.Θ ⊤ ≠ 0) (i : Fin (Fintype.card Ω)) :
    (toProbDist R h).p i = R.probability ({(Fintype.equivFin Ω).symm i} : Set Ω) := rfl

/-- For a specific element `ω : Ω`, its singleton probability matches the corresponding
coordinate of `toProbDist`. -/
theorem toProbDist_singleton (h : R.Θ ⊤ ≠ 0) (ω : Ω) :
    R.probability ({ω} : Set Ω) = (toProbDist R h).p (Fintype.equivFin Ω ω) := by
  rw [toProbDist_apply]
  simp only [Equiv.symm_apply_apply]

end Bridge

/-! ## §5: Event Probability = Sum of Singleton Probabilities

This is the payoff lemma that truly "grounds" `ProbDist`: the probability of any
event equals the sum of singleton probabilities over elements in that event.
-/

section Grounding

variable (R : KSBooleanRepresentation (Set Ω))

/-- **Probability of any set equals sum of its singleton probabilities**.

This is the key grounding lemma: it shows that `ProbDist` coordinates are not
arbitrary but match the KS-derived event probability.

`P(s) = ∑_{ω ∈ s} P({ω})`
-/
theorem probability_eq_sum_singletons (h : R.Θ ⊤ ≠ 0) (s : Set Ω) :
    R.probability s = ∑ ω ∈ s.toFinset, R.probability ({ω} : Set Ω) := by
  -- Key: s = ⋃ ω ∈ s.toFinset, {ω}
  have hs_eq : s = ⋃ ω ∈ s.toFinset, ({ω} : Set Ω) := by
    ext x
    simp only [Set.mem_toFinset, mem_iUnion, mem_singleton_iff, exists_prop]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · intro ⟨y, hy, hxy⟩; subst hxy; exact hy
  conv_lhs => rw [hs_eq]
  exact (probability_sum_singletons R h s.toFinset).symm

/-- The grounding theorem connecting `toProbDist` coordinates to event probability.

For any event `s : Set Ω`:
`P(s) = ∑ i : Fin n, (if (equivFin⁻¹ i) ∈ s then (toProbDist h).p i else 0)`

This shows `ProbDist` is the coordinate representation of KS event probability.
-/
theorem probability_eq_sum_toProbDist (h : R.Θ ⊤ ≠ 0) (s : Set Ω) :
    R.probability s =
      ∑ i : Fin (Fintype.card Ω),
        if (Fintype.equivFin Ω).symm i ∈ s then (toProbDist R h).p i else 0 := by
  rw [probability_eq_sum_singletons R h s]
  -- Rewrite using the equivalence
  have hsum : ∑ ω ∈ s.toFinset, R.probability ({ω} : Set Ω) =
      ∑ i : Fin (Fintype.card Ω),
        if (Fintype.equivFin Ω).symm i ∈ s
        then R.probability ({(Fintype.equivFin Ω).symm i} : Set Ω) else 0 := by
    rw [← Finset.sum_filter]
    have h1 : (Finset.filter (fun i => (Fintype.equivFin Ω).symm i ∈ s) Finset.univ) =
        (s.toFinset.map (Fintype.equivFin Ω).toEmbedding) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                 Set.mem_toFinset, Equiv.toEmbedding_apply]
      constructor
      · intro hi
        exact ⟨(Fintype.equivFin Ω).symm i, hi, Equiv.apply_symm_apply _ _⟩
      · intro ⟨ω, hω, hi⟩
        subst hi
        simp only [Equiv.symm_apply_apply]
        exact hω
    rw [h1]
    rw [Finset.sum_map]
    congr 1
    ext ω
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
  rw [hsum]
  simp only [toProbDist_apply]

end Grounding

/-! ## §6: Summary

We have established the complete bridge:

```
K&S Axioms + Separation
        ↓
Representation Theorem
        ↓
KSBooleanRepresentation (Set Ω)
        ↓ (toProbDist)
ProbDist Ω
```

The key grounding lemmas:
1. `probability_sup_of_disjoint`: P(A ∪ B) = P(A) + P(B) for disjoint A, B
2. `probability_sum_singletons`: ∑_{ω ∈ s} P({ω}) = P(⋃ ω ∈ s, {ω})
3. `probability_sum_singletons_eq_one`: ∑_ω P({ω}) = 1
4. `probability_eq_sum_singletons`: P(s) = ∑_{ω ∈ s} P({ω})
5. `probability_eq_sum_toProbDist`: P(s) matches sum of ProbDist coordinates

This shows that `ProbDist` is NOT a free-floating definition but the
**coordinate incarnation of KS probability on a finite sample space**.
-/

end KnuthSkilling.Probability.FiniteProbability
