/-
# Counterexample: Negative Values Without Identity

K&S claim (p.42): "fidelity ensures that other elements are quantified by positive values."

This file proves that claim is FALSE for unbounded distributive lattices.

## The Gap

K&S's positivity proof (p.45) uses "we may set m(⊥) = 0". But distributive lattices
don't require ⊥. For (ℤ, ≤) — a valid distributive lattice with no bottom — the
Hölder representation theorem applies but produces NEGATIVE values.

## Main Results

1. `Int.instKSSemigroupBase` — ℤ satisfies K&S semigroup axioms
2. `MultiplicativeInt.no_anomalous_pair` — ℤ has no anomalous pairs
3. `holder_embedding_produces_negatives` — THE embedding from `holder_not_anom` has Φ(-1) < 0

The key insight: positivity comes from `ident_le : ∀ x, ident ≤ x`, not from
the representation theorem itself.
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.Basic
import OrderedSemigroups.Holder
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.NNReal.Basic
import KnuthSkilling.Additive.Proofs.GridInduction.Comparison
import KnuthSkilling.Additive.Proofs.DirectCuts.Main

namespace KnuthSkilling.AppendixA.Counterexamples

open KSSemigroupBase

/-! ## Part 1: ℤ as a KSSemigroupBase -/

/-- ℤ is a distributive lattice (every chain is). -/
example : DistribLattice ℤ := inferInstance

/-- ℤ has no bottom element. -/
theorem Int.unbounded_below : ¬∃ bot : ℤ, ∀ n : ℤ, bot ≤ n := by
  intro ⟨bot, hbot⟩; have := hbot (bot - 1); omega

/-- **ℤ is a KSSemigroupBase** with `op = (+)`. -/
instance Int.instKSSemigroupBase : KSSemigroupBase ℤ where
  op := (· + ·)
  op_assoc := add_assoc
  op_strictMono_left := fun y => by intro a b hab; show a + y < b + y; omega
  op_strictMono_right := fun x => by intro a b hab; show x + a < x + b; omega

theorem Int.op_eq_add : ∀ a b : ℤ, op a b = a + b := fun _ _ => rfl

/-- ℤ cannot satisfy `ident_le` (identity-as-minimum). -/
theorem Int.cannot_satisfy_ident_le : ¬(∀ n : ℤ, (0 : ℤ) ≤ n) := by push Not; use -1; omega

/-! ## Part 2: Bounded Lattices DO Give Positivity -/

/-- When we have ⊥ and normalize v(⊥) = 0, fidelity gives positivity. -/
theorem positivity_from_bounded_lattice {α : Type*} [Lattice α] [OrderBot α]
    (v : α → ℝ) (hFidelity : ∀ a b : α, a < b → v a < v b)
    (hNormalized : v ⊥ = 0) (x : α) (hx : ⊥ < x) : 0 < v x :=
  calc 0 = v ⊥ := hNormalized.symm
       _ < v x := hFidelity ⊥ x hx

/-! ## Part 3: ℤ Has No Anomalous Pairs -/

/-- ℤ has no anomalous pairs — the Archimedean property rules them out.

An anomalous pair (a,b) requires ∀n, `n·a < n·b < (n+1)·a` or vice versa.
For ℤ, if a < b, then for large n, n·(b-a) ≥ a, contradicting the bound. -/
theorem Int.no_anomalous_pair_additive :
    ∀ a b : ℤ, ¬(∀ n : ℕ+, (n * a < n * b ∧ n * b < (n + 1) * a) ∨
                          (n * a > n * b ∧ n * b > (n + 1) * a)) := by
  intro a b hanom
  have h1 := hanom 1; simp only [PNat.val_ofNat, one_mul, Nat.cast_one] at h1
  rcases h1 with ⟨ha_lt_b, hb_lt_2a⟩ | ⟨ha_gt_b, hb_gt_2a⟩
  · -- Case: a < b < 2a (requires a > 0)
    have ha_pos : 0 < a := by omega
    have hba_ge_one : 1 ≤ b - a := by omega
    have key : ∀ m : ℕ, 0 < m → m * (b - a) < a → m < a := by intro m _ h; nlinarith
    let m := a.natAbs + 1
    have hm_pos : 0 < m := by omega
    have hanom_m := hanom ⟨m, hm_pos⟩; simp only [PNat.mk_coe] at hanom_m
    rcases hanom_m with ⟨_, hm_b_lt⟩ | ⟨hm_a_gt, _⟩
    · have h_key : (m : ℤ) * (b - a) < a := by nlinarith
      have := key m hm_pos h_key
      have : (m : ℤ) = a.natAbs + 1 := by simp [m]
      have : a = a.natAbs := (Int.natAbs_of_nonneg (by omega : 0 ≤ a)).symm
      omega
    · have : (m : ℤ) * a > (m : ℤ) * b := hm_a_gt; nlinarith
  · -- Case: a > b > 2a (requires a < 0)
    have ha_neg : a < 0 := by omega
    let m := (-a).natAbs + 1
    have hm_pos : 0 < m := by omega
    have hanom_m := hanom ⟨m, hm_pos⟩; simp only [PNat.mk_coe] at hanom_m
    rcases hanom_m with ⟨hm_a_lt, _⟩ | ⟨_, hm_b_gt⟩
    · have : (m : ℤ) * a < (m : ℤ) * b := hm_a_lt; nlinarith
    · have h_key : (m : ℤ) * (b - a) > a := by nlinarith
      have hba_neg : b - a ≤ -1 := by omega
      have : (m : ℤ) = (-a).natAbs + 1 := by simp [m]
      have : -a = (-a).natAbs := (Int.natAbs_of_nonneg (by omega : 0 ≤ -a)).symm
      nlinarith

/-! ## Part 4: Setting Up Multiplicative ℤ for Hölder -/

open Multiplicative in
instance : IsOrderedCancelSemigroup (Multiplicative ℤ) where
  mul_le_mul_left' {a b} hab c := by
    have h : toAdd a ≤ toAdd b := toAdd_le.mpr hab
    rw [← toAdd_le, toAdd_mul, toAdd_mul]; omega
  le_of_mul_le_mul_left' {a b} c hab := by
    rw [← toAdd_le, toAdd_mul, toAdd_mul] at hab; rw [← toAdd_le]; omega
  le_of_mul_le_mul_right' {a b} c hab := by
    rw [← toAdd_le, toAdd_mul, toAdd_mul] at hab; rw [← toAdd_le]; omega
  mul_le_mul_right' {a b} hab c := by
    have h : toAdd a ≤ toAdd b := toAdd_le.mpr hab
    rw [← toAdd_le, toAdd_mul, toAdd_mul]; omega

open Multiplicative in
instance : Pow (Multiplicative ℤ) ℕ+ where
  pow x n := ofAdd (n * toAdd x)

open Multiplicative in
instance : PNatPowAssoc (Multiplicative ℤ) where
  ppow_add m n x := by
    show ofAdd ((m + n : ℕ+) * toAdd x) = ofAdd (m * toAdd x) * ofAdd (n * toAdd x)
    rw [← ofAdd_add]; congr 1; push_cast; ring
  ppow_one x := by
    show ofAdd ((1 : ℕ+) * toAdd x) = x
    have h : (1 : ℕ+).val * toAdd x = toAdd x := one_mul (toAdd x)
    rw [h]; exact ofAdd_toAdd x

open Multiplicative in
/-- `Multiplicative ℤ` has no anomalous pairs. -/
theorem MultiplicativeInt.no_anomalous_pair : ¬has_anomalous_pair (α := Multiplicative ℤ) := by
  intro ⟨a, b, hanom⟩
  let a' := toAdd a; let b' := toAdd b
  have hanom' : ∀ n : ℕ+, (n * a' < n * b' ∧ n * b' < (n + 1) * a') ∨
                         (n * a' > n * b' ∧ n * b' > (n + 1) * a') := by
    intro n; have h := hanom n
    simp only [HPow.hPow, Pow.pow, ofAdd_lt] at h; exact h
  exact Int.no_anomalous_pair_additive a' b' hanom'

/-! ## Part 5: The Main Theorem -/

/-- **Main Theorem**: If ℤ has no anomalous pairs, `holder_not_anom` gives an embedding
with negative values.

The premise `hna : ¬has_anomalous_pair` is what `holder_not_anom` requires.
Inside the proof, we explicitly call `holder_not_anom hna` to get the embedding.

The proof then shows that embedding has Φ(-1) < 0:
1. Φ is additive: Φ(a+b) = Φ(a) + Φ(b)
2. Φ(0) = 0
3. Φ is strictly monotone (from order isomorphism)
4. Φ(1) > 0 (since 0 < 1)
5. Φ(-1) = -Φ(1) < 0 -/
theorem holder_embedding_produces_negatives
    (hna : ¬has_anomalous_pair (α := Multiplicative ℤ)) :
    ∃ (G : Subsemigroup (Multiplicative ℝ)) (Θ : Multiplicative ℤ ≃*o G),
      Multiplicative.toAdd (Θ (Multiplicative.ofAdd (-1)) : Multiplicative ℝ) < 0 := by
  -- Apply Hölder's theorem to get the embedding
  obtain ⟨G, ⟨Θ⟩⟩ := holder_not_anom hna
  refine ⟨G, Θ, ?_⟩
  let Φ : ℤ → ℝ := fun n => Multiplicative.toAdd (Θ (Multiplicative.ofAdd n) : Multiplicative ℝ)
  have hAdditive : ∀ a b : ℤ, Φ (a + b) = Φ a + Φ b := by
    intro a b
    exact congrArg (fun z : G => Multiplicative.toAdd (z : Multiplicative ℝ))
      (map_mul Θ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))
  -- Φ(0) = 0
  have hZero : Φ 0 = 0 := by
    have h : Φ 0 = Φ 0 + Φ 0 := by rw [← hAdditive 0 0]; ring_nf
    linarith
  have hStrictMono : StrictMono Φ := fun _ _ h => Θ.strictMono h
  -- Φ(1) > 0
  have hOne : 0 < Φ 1 := by have := hStrictMono (by omega : (0:ℤ) < 1); rw [hZero] at this; exact this
  -- Φ(-1) < 0
  have hNegOne : Φ (-1) + Φ 1 = 0 := by rw [← hAdditive (-1) 1]; simp only [neg_add_cancel, hZero]
  show Φ (-1) < 0; linarith

/-- **Corollary**: Applying `holder_not_anom` to ℤ produces an embedding with negative values.

This combines:
1. `MultiplicativeInt.no_anomalous_pair` — ℤ has no anomalous pairs
2. `holder_embedding_produces_negatives` — applies `holder_not_anom` and shows Φ(-1) < 0 -/
theorem Int.holder_embedding_has_negatives :
    ∃ (G : Subsemigroup (Multiplicative ℝ)) (Θ : Multiplicative ℤ ≃*o G),
      Multiplicative.toAdd (Θ (Multiplicative.ofAdd (-1)) : Multiplicative ℝ) < 0 :=
  holder_embedding_produces_negatives MultiplicativeInt.no_anomalous_pair

/-! ## Summary

**What we proved:**
1. ℤ is a valid `KSSemigroupBase` — satisfies K&S semigroup axioms
2. ℤ cannot satisfy `ident_le` — no identity-as-minimum
3. ℤ has no anomalous pairs — Hölder/Alimov theorem applies
4. The Hölder embedding has Φ(-1) < 0 — positivity fails

**The key insight:**
K&S's positivity comes from `ident_le : ∀ x, ident ≤ x`, NOT from the representation
theorem. The Hölder path works perfectly for ℤ but produces negative values. -/

end KnuthSkilling.AppendixA.Counterexamples

namespace KnuthSkilling.Additive.Counterexamples.Models

open KSSemigroupBase KnuthSkillingMonoidBase
open Proofs.OrderedSemigroupEmbedding.HolderEmbedding

/-! Concrete profiles are explicit values, never global instances. The arithmetic
readouts establish consistency before any abstract representation route is invoked. -/

@[instance_reducible] noncomputable def realProfile : KnuthSkillingMonoidBase ℝ where
  op := (· + ·)
  op_assoc := add_assoc
  op_strictMono_left := fun y _a _b h => _root_.add_lt_add_left h y
  op_strictMono_right := fun x _a _b h => _root_.add_lt_add_right h x
  ident := 0
  op_ident_left := zero_add
  op_ident_right := add_zero

noncomputable def realReadout : letI := realProfile; RepresentationResult ℝ := by
  let := realProfile
  exact ⟨id, fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem real_premises : letI := realProfile;
    Axioms.AnomalousPairs.NoAnomalousPairs ℝ ∧ KSSeparationStrict ℝ := by
  let := realProfile
  let r := realReadout
  refine ⟨Proofs.GridInduction.Comparison.noAnomalousPairs_of_representation
    ℝ r.Θ r.order_preserving r.additive, ?_⟩
  let := r.separationSemigroupStrict
  exact KSSeparationStrict_of_KSSeparationSemigroupStrict

theorem reals_have_negative_values : letI := realProfile;
    ¬ (∀ x : ℝ, ident ≤ x) := by
  let := realProfile
  intro h
  have hh := h (-1)
  change (0 : ℝ) ≤ -1 at hh
  norm_num at hh

@[instance_reducible] noncomputable def nnrealProfile : KnuthSkillingAlgebraBase NNReal where
  op := (· + ·)
  op_assoc := add_assoc
  op_strictMono_left := fun y _a _b h => _root_.add_lt_add_left h y
  op_strictMono_right := fun x _a _b h => _root_.add_lt_add_right h x
  ident := 0
  op_ident_left := zero_add
  op_ident_right := add_zero
  ident_le := fun _ => bot_le

noncomputable def nnrealReadout : letI := nnrealProfile; RepresentationResult NNReal := by
  let := nnrealProfile
  exact ⟨fun x => (x : ℝ), fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem nnreal_premises : letI := nnrealProfile;
    Axioms.AnomalousPairs.NoAnomalousPairs NNReal ∧ KSSeparationStrict NNReal := by
  let := nnrealProfile
  let r := nnrealReadout
  refine ⟨Proofs.GridInduction.Comparison.noAnomalousPairs_of_representation
    NNReal r.Θ r.order_preserving r.additive, ?_⟩
  let := r.separationSemigroupStrict
  exact KSSeparationStrict_of_KSSeparationSemigroupStrict

abbrev PositiveReal := {x : ℝ // 0 < x}

@[instance_reducible] noncomputable def positiveProfile : KSSemigroupBase PositiveReal where
  op x y := ⟨x.val + y.val, add_pos x.property y.property⟩
  op_assoc x y z := Subtype.ext (add_assoc x.val y.val z.val)
  op_strictMono_left := by
    intro y a b h
    change a.val + y.val < b.val + y.val
    change a.val < b.val at h
    exact _root_.add_lt_add_left h y.val
  op_strictMono_right := by
    intro x a b h
    change x.val + a.val < x.val + b.val
    change a.val < b.val at h
    exact _root_.add_lt_add_right h x.val

noncomputable def positiveReadout : letI := positiveProfile; RepresentationResult PositiveReal := by
  let := positiveProfile
  exact ⟨Subtype.val, fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem positive_premises : letI := positiveProfile;
    KSSeparationSemigroupStrict PositiveReal ∧
      (∀ x : PositiveReal, IsPositive x) ∧ (∀ x y : PositiveReal, op x y = op y x) := by
  let := positiveProfile
  let r := positiveReadout
  exact ⟨r.separationSemigroupStrict, fun x => (r.isPositive_iff x).mpr x.property, r.op_comm⟩

/-- Strictly positive addition needs no identity in its carrier. -/
theorem positive_no_left_identity : letI := positiveProfile;
    ¬ ∃ e : PositiveReal, ∀ x, op e x = x := by
  let := positiveProfile
  rintro ⟨e, h⟩
  exact (ne_of_lt (positive_premises.2.1 e e)) (h e).symm

/-- Positivity can hold without any minimum element of the carrier. -/
theorem positive_no_minimum : ¬ ∃ m : PositiveReal, ∀ x, m ≤ x := by
  rintro ⟨m, h⟩
  have hh := h ⟨m.val / 2, half_pos m.property⟩
  change m.val ≤ m.val / 2 at hh
  linarith [m.property]

noncomputable def nnrealHolder : letI := nnrealProfile; RepresentationResult NNReal := by
  let := nnrealProfile
  let := nnreal_premises.1
  exact holder_representation

noncomputable def nnrealGrid : letI := nnrealProfile; RepresentationResult NNReal := by
  let := nnrealProfile
  let := nnreal_premises.2
  -- Select the actual grid globalization, rather than another provider of its interface.
  letI : RepresentationGlobalization NNReal := representationGlobalization_of_KSSeparationStrict
  exact grid_normalized_representation.toRepresentationResult

noncomputable def nnrealCuts : letI := nnrealProfile; RepresentationResult NNReal := by
  let := nnrealProfile
  let := nnreal_premises.2
  exact Proofs.DirectCuts.cuts_representation 1 (by change (0 : NNReal) < 1; norm_num)

theorem nnreal_one_positive : letI := nnrealProfile; IsPositive (1 : NNReal) := by
  let := nnrealProfile
  exact (nnrealReadout.isPositive_iff 1).mpr (by change (0 : ℝ) < 1; norm_num)

/-- The actual three constructions have identical observations after unit calibration. -/
theorem three_routes_calibrated (x : NNReal) : letI := nnrealProfile;
    (nnrealHolder.calibrate 1 nnreal_one_positive).Θ x = (x : ℝ) ∧
    (nnrealGrid.calibrate 1 nnreal_one_positive).Θ x = (x : ℝ) ∧
    (nnrealCuts.calibrate 1 nnreal_one_positive).Θ x = (x : ℝ) := by
  let := nnrealProfile
  have h (r : RepresentationResult NNReal) :
      (r.calibrate 1 nnreal_one_positive).Θ x = (x : ℝ) := by
    rw [r.calibrate_agree nnrealReadout 1 nnreal_one_positive x]
    simp [RepresentationResult.calibrate_apply, nnrealReadout]
  exact ⟨h nnrealHolder, h nnrealGrid, h nnrealCuts⟩

/-- Positive-natural cuts also execute on a genuinely identity-free positive carrier. -/
theorem positive_cuts_exist : letI := positiveProfile; Nonempty (RepresentationResult PositiveReal) := by
  let := positiveProfile
  let := positive_premises.1
  exact ⟨Proofs.DirectCuts.cuts_pnat_representation ⟨1, by norm_num⟩
    (positive_premises.2.1 _) positive_premises.2.1 positive_premises.2.2⟩

/-- Reordering additive events preserves the endpoint, not the history or first observation. -/
theorem equal_endpoints_distinct_histories :
    ([1, 2] : List ℝ) ≠ [2, 1] ∧
    ([1, 2] : List ℝ).foldl (· + ·) 0 = ([2, 1] : List ℝ).foldl (· + ·) 0 ∧
    ([1, 2] : List ℝ).head? ≠ ([2, 1] : List ℝ).head? := by norm_num

theorem nonzero_shift_fails : letI := realProfile;
    ¬ (∀ x y, realReadout.Θ (op x y) + 1 = (realReadout.Θ x + 1) + (realReadout.Θ y + 1)) := by
  let := realProfile
  rw [realReadout.shift_additive_iff 1 1]
  norm_num

end KnuthSkilling.Additive.Counterexamples.Models
