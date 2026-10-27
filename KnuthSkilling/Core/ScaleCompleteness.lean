/-
# From additive scales to countable event valuations

A representation is an algebraic order embedding into the additive reals;
countable additivity requires separate event and continuity hypotheses.
`KSScaleComplete` provides preimages of bounded increasing real suprema.
`KSScottContinuous` supplies preservation along increasing event sequences.
The normalized scale then sends disjoint countable joins to convergent sums.
These hypotheses do not assert normalization at the top event.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import KnuthSkilling.Core.Basic
import KnuthSkilling.Bridges.Model
import KnuthSkilling.Additive.Representation

namespace KnuthSkilling

open KnuthSkillingMonoidBase KSSemigroupBase
open KnuthSkilling.Additive

/-- **Unbundled predicate**: Scale completeness property.

Θ(S) ⊆ ℝ is closed under suprema of bounded increasing ω-sequences.
This is the predicate form; see `KSScaleComplete` for the class form. -/
def ScaleCompleteProp {S : Type*} [KSSemigroupBase S] (R : RepresentationResult S) : Prop :=
  ∀ (f : ℕ → S), Monotone f → BddAbove (Set.range (R.Θ ∘ f)) →
    ∃ s : S, R.Θ s = ⨆ n, R.Θ (f n)

/-- Sequential completeness of the scale, relative to a K&S representation.

Given a representation Θ from the Hölder/Alimov embedding (via NoAnomalousPairs),
this says: Θ(S) ⊆ ℝ is closed under suprema of bounded increasing ω-sequences.

This is **sequential completeness** (ω-completeness), NOT full Dedekind completeness.
It is a sufficient scale-closure premise in the σ-additivity theorem.

**Key Design**: Θ-preservation is automatic from the closure property - we don't need
to axiomatize that Θ preserves sups separately, it falls out of the definition. -/
class KSScaleComplete (S : Type*) [KSSemigroupBase S] (R : RepresentationResult S) where
  /-- Θ(S) is closed: bounded increasing sequences have preimages of their sups -/
  closed_seqSup : ∀ (f : ℕ → S), Monotone f → BddAbove (Set.range (R.Θ ∘ f)) →
    ∃ s : S, R.Θ s = ⨆ n, R.Θ (f n)

namespace KSScaleComplete

variable {S : Type*} [KSSemigroupBase S] (R : RepresentationResult S) [KSScaleComplete S R]

/-- The supremum element in S (chosen via closure property).

This exists by KSScaleComplete: there's some s ∈ S with Θ(s) = sup Θ(fₙ). -/
noncomputable def seqSup (f : ℕ → S) (hf : Monotone f)
    (hbdd : BddAbove (Set.range (R.Θ ∘ f))) : S :=
  Classical.choose (closed_seqSup (R := R) f hf hbdd)

/-- Θ automatically preserves seqSup by construction.

This is NOT an axiom - it's derived from the closure property.
The closure says "∃ s, Θ s = sup Θ(fₙ)", and seqSup picks that s. -/
theorem Θ_seqSup (f : ℕ → S) (hf : Monotone f) (hbdd : BddAbove (Set.range (R.Θ ∘ f))) :
    R.Θ (seqSup R f hf hbdd) = ⨆ n, R.Θ (f n) :=
  Classical.choose_spec (closed_seqSup (R := R) f hf hbdd)

/-- seqSup is an upper bound: each f n ≤ seqSup f -/
theorem le_seqSup (f : ℕ → S) (hf : Monotone f) (hbdd : BddAbove (Set.range (R.Θ ∘ f))) (n : ℕ) :
    f n ≤ seqSup R f hf hbdd := by
  rw [R.order_preserving]
  rw [Θ_seqSup]
  exact le_ciSup hbdd n

/-- seqSup is the least upper bound -/
theorem seqSup_le (f : ℕ → S) (hf : Monotone f) (hbdd : BddAbove (Set.range (R.Θ ∘ f)))
    (b : S) (hb : ∀ n, f n ≤ b) : seqSup R f hf hbdd ≤ b := by
  rw [R.order_preserving]
  rw [Θ_seqSup]
  apply ciSup_le
  intro n
  exact (R.order_preserving (f n) b).mp (hb n)

end KSScaleComplete

/-- The `KSScaleComplete` instance satisfies the unbundled `ScaleCompleteProp` predicate. -/
theorem KSScaleComplete.scaleCompleteProp {S : Type*} [KSSemigroupBase S]
    (R : RepresentationResult S) [KSScaleComplete S R] : ScaleCompleteProp R :=
  KSScaleComplete.closed_seqSup

/-- **Unbundled predicate**: σ-complete events property.

Events have countable joins. This is the predicate form; see `SigmaCompleteEvents` for the class form. -/
def SigmaCompleteEventsProp (E : Type*) [PlausibilitySpace E] : Prop :=
  ∃ (iSup : (ℕ → E) → E),
    (∀ (f : ℕ → E) (n : ℕ), f n ≤ iSup f) ∧
    (∀ (f : ℕ → E) (b : E), (∀ n, f n ≤ b) → iSup f ≤ b)

/-- σ-complete event structure: events have countable joins.

This extends PlausibilitySpace with countable joins (σ-frame structure).
The key operation is `iSup : (ℕ → E) → E` for countable families. -/
class SigmaCompleteEvents (E : Type*) extends PlausibilitySpace E where
  /-- Countable supremum exists -/
  iSup : (ℕ → E) → E
  /-- iSup is an upper bound -/
  le_iSup : ∀ (f : ℕ → E) (n : ℕ), f n ≤ iSup f
  /-- iSup is the least upper bound -/
  iSup_le : ∀ (f : ℕ → E) (b : E), (∀ n, f n ≤ b) → iSup f ≤ b

namespace SigmaCompleteEvents

variable {E : Type*} [SigmaCompleteEvents E]

/-- Countable union of events -/
def countableUnion (f : ℕ → E) : E := iSup f

/-- The iSup of a monotone sequence -/
theorem iSup_mono {f : ℕ → E} (_hf : Monotone f) : ∀ n, f n ≤ iSup f := le_iSup f

/-- iSup of a constant sequence -/
theorem iSup_eq_of_const {f : ℕ → E} {a : E} (h : ∀ n, f n = a) :
    iSup f = a := by
  apply le_antisymm
  · exact iSup_le f a (fun n => le_of_eq (h n))
  · have : a = f 0 := (h 0).symm
    rw [this]
    exact le_iSup f 0

end SigmaCompleteEvents

/-- The `SigmaCompleteEvents` instance satisfies the unbundled `SigmaCompleteEventsProp` predicate. -/
theorem SigmaCompleteEvents.sigmaCompleteEventsProp {E : Type*} [inst : SigmaCompleteEvents E] :
    SigmaCompleteEventsProp E :=
  ⟨inst.iSup, inst.le_iSup, inst.iSup_le⟩

/-- **Unbundled predicate**: Scott continuity property.

v preserves directed suprema (ω-chains). This is the predicate form;
see `KSScottContinuous` for the class form. -/
def ScottContinuousProp {E S : Type*} [SigmaCompleteEvents E] [KSSemigroupBase S]
    (R : RepresentationResult S) [KSScaleComplete S R] (v : E → S) : Prop :=
  ∀ (f : ℕ → E), Monotone f →
    ∃ _hf_mono : Monotone (R.Θ ∘ v ∘ f),
    ∃ _hf_bdd : BddAbove (Set.range (R.Θ ∘ v ∘ f)),
    R.Θ (v (SigmaCompleteEvents.iSup f)) = ⨆ n, R.Θ (v (f n))

/-- Scott continuity: v preserves directed suprema (ω-chains).

Phrased via the representation Θ since S may not have internal sups.
The key property: when events increase to a limit, their Θ-images converge
to the Θ-image of the limit.

This is an additional hypothesis, not a consequence of finite additivity.

**Identity note**: The unbundled predicate is identity-free; the bundled class
`KSScottContinuous` requires identity only because it extends `KSModel`. -/
class KSScottContinuous (E S : Type*) [SigmaCompleteEvents E] [KnuthSkillingMonoidBase S]
    (R : RepresentationResult S) [KSScaleComplete S R] extends KSModel E S where
  /-- v preserves countable sups of increasing sequences (via Θ) -/
  v_scott : ∀ (f : ℕ → E), Monotone f →
    ∃ _hf_mono : Monotone (R.Θ ∘ v ∘ f),
    ∃ _hf_bdd : BddAbove (Set.range (R.Θ ∘ v ∘ f)),
    R.Θ (v (SigmaCompleteEvents.iSup f)) = ⨆ n, R.Θ (v (f n))

namespace KSScottContinuous

variable {E S : Type*} [SigmaCompleteEvents E] [KnuthSkillingMonoidBase S]
variable (R : RepresentationResult S) [KSScaleComplete S R]
variable (m : KSScottContinuous E S R)

/-- The valuation of a countable increasing union equals the sup of valuations (via Θ) -/
theorem v_countable_union_eq (f : ℕ → E) (hf : Monotone f) :
    R.Θ (m.v (SigmaCompleteEvents.iSup f)) = ⨆ n, R.Θ (m.v (f n)) := by
  obtain ⟨_, _, heq⟩ := m.v_scott f hf
  exact heq

end KSScottContinuous

/-- The `KSScottContinuous` instance satisfies the unbundled `ScottContinuousProp` predicate. -/
theorem KSScottContinuous.scottContinuousProp {E S : Type*} [SigmaCompleteEvents E]
    [KnuthSkillingMonoidBase S] (R : RepresentationResult S) [KSScaleComplete S R]
    (m : KSScottContinuous E S R) : ScottContinuousProp R m.v :=
  m.v_scott

/-- Pairwise disjoint family of events -/
def PairwiseDisjoint' {E : Type*} [SemilatticeInf E] [OrderBot E] (f : ℕ → E) : Prop :=
  ∀ i j, i ≠ j → Disjoint (f i) (f j)

/-- Partial unions: the finite union of the first n events -/
def partialUnion {E : Type*} [PlausibilitySpace E] (f : ℕ → E) (n : ℕ) : E :=
  Finset.sup (Finset.range n) f

/-- Partial unions are monotone -/
theorem partialUnion_mono {E : Type*} [PlausibilitySpace E] (f : ℕ → E) :
    Monotone (partialUnion f) := by
  intro m n hmn
  apply Finset.sup_mono
  exact Finset.range_mono hmn

/-- Partial union at n+1 extends by f n -/
theorem partialUnion_succ {E : Type*} [PlausibilitySpace E] (f : ℕ → E) (n : ℕ) :
    partialUnion f (n + 1) = partialUnion f n ⊔ f n := by
  simp only [partialUnion, Finset.range_add_one, Finset.sup_insert]
  rw [sup_comm]

/-- iSup of f equals iSup of partial unions -/
theorem iSup_eq_iSup_partialUnion {E : Type*} [SigmaCompleteEvents E] (f : ℕ → E) :
    SigmaCompleteEvents.iSup f = SigmaCompleteEvents.iSup (partialUnion f) := by
  apply le_antisymm
  · -- Each f n ≤ partialUnion f (n+1) ≤ iSup (partialUnion f)
    apply SigmaCompleteEvents.iSup_le
    intro n
    have h1 : f n ≤ partialUnion f (n + 1) := by
      simp only [partialUnion]
      exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_add_one n))
    exact le_trans h1 (SigmaCompleteEvents.le_iSup (partialUnion f) (n + 1))
  · -- Each partialUnion f n ≤ iSup f
    apply SigmaCompleteEvents.iSup_le
    intro n
    simp only [partialUnion]
    apply Finset.sup_le
    intro i _
    exact SigmaCompleteEvents.le_iSup f i

/-- For a pairwise disjoint family in range n, partialUnion f n is disjoint from f n -/
theorem disjoint_partialUnion_of_pairwiseDisjoint {E : Type*} [PlausibilitySpace E]
    {f : ℕ → E} (hd : PairwiseDisjoint' f) (n : ℕ) :
    Disjoint (partialUnion f n) (f n) := by
  simp only [partialUnion]
  rw [Finset.disjoint_sup_left]
  intro i hi
  exact hd i n (Finset.mem_range.mp hi).ne

/-- Finite additivity: Θ(v(partialUnion f n)) = ∑ i in range n, Θ(v(f i))

Requires NormalizedRepresentationResult for the base case Θ(ident) = 0. -/
theorem Θ_v_partialUnion_eq_sum {E S : Type*} [PlausibilitySpace E] [KnuthSkillingMonoidBase S]
    (R : NormalizedRepresentationResult S) (m : KSModel E S)
    (f : ℕ → E) (hd : PairwiseDisjoint' f) (n : ℕ) :
    R.Θ (m.v (partialUnion f n)) = ∑ i ∈ Finset.range n, R.Θ (m.v (f i)) := by
  induction n with
  | zero =>
    simp only [partialUnion, Finset.range_zero, Finset.sup_empty, Finset.sum_empty]
    rw [m.v_bot, R.ident_zero]
  | succ n ih =>
    rw [partialUnion_succ, Finset.sum_range_succ]
    have hdisj := disjoint_partialUnion_of_pairwiseDisjoint hd n
    rw [m.v_sup_of_disjoint hdisj, R.additive, ih]

/-- **Key Lemma**: For nonnegative sequences with bounded partial sums, tsum equals the iSup of partial sums.

For f : ℕ → ℝ with f ≥ 0 and bounded partial sums:
- The series is summable (by completeness)
- The tsum equals the limit of partial sums (definition of HasSum)
- For monotone bounded sequences, the limit equals the supremum

**Note**: The boundedness hypothesis is necessary - without it, the equality may not hold
(tsum = 0 for non-summable by Lean convention, but ciSup is undefined for unbounded sets). -/
theorem tsum_eq_iSup_partialSums_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hbdd : BddAbove (Set.range (fun n => ∑ i ∈ Finset.range n, f i))) :
    ∑' n, f n = ⨆ n, ∑ i ∈ Finset.range n, f i := by
  obtain ⟨C, hC⟩ := hbdd
  have hsummable : Summable f := summable_of_sum_range_le (c := C) hf (fun n => hC (Set.mem_range_self n))
  have hmono : Monotone (fun n => ∑ i ∈ Finset.range n, f i) := by
    intro m n hmn
    apply Finset.sum_mono_set_of_nonneg hf
    exact Finset.range_mono hmn
  exact tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat
    (tendsto_atTop_ciSup hmono ⟨C, hC⟩)

/-- **K&S σ-Additivity Theorem**

Given:
- S with a K&S representation R (from Hölder/Alimov via NoAnomalousPairs)
- KSScaleComplete S R (Θ(S) is sequentially closed)
- KSScottContinuous E S R (v preserves directed sups)

Then μ = R.Θ ∘ v is σ-additive on disjoint families.

This is the clean bridge from K&S finite additivity to Kolmogorov σ-additivity,
building on the representation theorem without importing σ-algebra structure.

**Two independent gates**:
- Gate 1 (NAP): For Θ's existence (via Hölder/Alimov, already formalized)
- Gate 2 (Completeness + Scott): For σ-additivity (this theorem)

**Note**: This theorem requires NormalizedRepresentationResult (with Θ(ident) = 0)
for the base case of the finite additivity induction. -/
theorem ks_sigma_additive
    {E S : Type*} [SigmaCompleteEvents E] [KnuthSkillingMonoidBase S]
    (R : NormalizedRepresentationResult S) [KSScaleComplete S R.toRepresentationResult]
    (m : KSScottContinuous E S R.toRepresentationResult)
    (f : ℕ → E) (hd : PairwiseDisjoint' f) :
    let μ := R.Θ ∘ m.v
    μ (SigmaCompleteEvents.iSup f) = ∑' n, μ (f n) := by
  intro μ
  rw [iSup_eq_iSup_partialUnion f]
  show R.Θ (m.v (SigmaCompleteEvents.iSup (partialUnion f))) = ∑' n, R.Θ (m.v (f n))
  have hscott := m.v_countable_union_eq R.toRepresentationResult (partialUnion f) (partialUnion_mono f)
  rw [hscott]
  have hfinite := Θ_v_partialUnion_eq_sum R m.toKSModel f hd
  simp_rw [hfinite]
  have hμ_nonneg : ∀ n, 0 ≤ R.Θ (m.v (f n)) := by
    intro n
    have h := m.v_ident_le (f n)
    rw [← R.ident_zero]
    exact (R.order_preserving ident (m.v (f n))).mp h
  obtain ⟨_, hbdd_pu, _⟩ := m.v_scott (partialUnion f) (partialUnion_mono f)
  have hbdd : BddAbove (Set.range (fun n => ∑ i ∈ Finset.range n, R.Θ (m.v (f i)))) := by
    change BddAbove (Set.range (fun n => R.Θ (m.v (partialUnion f n)))) at hbdd_pu
    simpa only [hfinite] using hbdd_pu
  exact (tsum_eq_iSup_partialSums_nonneg hμ_nonneg hbdd).symm

/-- NNReal with identity and coercion to ℝ forms a valid K&S representation.

This provides the standard model where Θ is just coercion to ℝ. -/
def nnrealRepresentation : RepresentationResult NNReal where
  Θ := fun x => x.val
  order_preserving := fun a b => NNReal.coe_le_coe
  additive := fun x y => by
    show (op x y).val = x.val + y.val
    rfl

/-- NNReal is sequentially complete (inherits from ℝ's conditional completeness).

The image Θ(NNReal) = [0, ∞) ⊆ ℝ is closed under bounded ω-sups. -/
instance instKSScaleCompleteNNReal : KSScaleComplete NNReal nnrealRepresentation where
  closed_seqSup := fun f _hf hbdd => by
    have hsup_nonneg : 0 ≤ ⨆ n, (f n).val := by
      apply Real.iSup_nonneg
      intro n
      exact (f n).coe_nonneg
    use ⟨⨆ n, (f n).val, hsup_nonneg⟩
    rfl

/-- The standard model NNReal satisfies scale completeness. -/
theorem nnreal_scale_complete : KSScaleComplete NNReal nnrealRepresentation := inferInstance

end KnuthSkilling
