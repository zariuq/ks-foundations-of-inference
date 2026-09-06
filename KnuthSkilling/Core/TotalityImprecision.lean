/-
# Totality, Order Reflection, and Interval Models

This file separates three notions that are easy to conflate: one-way scalar
fidelity, order-reflecting scalar embeddings, and interval representations.

## Main Results

* `PartialKnuthSkillingAlgebra`: K&S axioms with PartialOrder instead of LinearOrder
* `PlausibilityInterval`: Interval-valued plausibilities for partial orders
* `totality_of_orderReflectingPointRepresentation`: an order-reflecting scalar
  representation forces the source order to be total
* `incomparable_implies_overlapping`: a faithful interval representation sends
  incomparable elements to non-separated intervals

## Mathematical Background

`PartialKnuthSkillingAlgebra` is a deliberately lightweight partial-order
analogue of the ordered associative combination used by K&S.  It is not, by
itself, a formalization of all the hypotheses of their representation theorem.

**Key distinction**: K&S fidelity is one-way: order in the lattice must imply
order of the scalar values, while the scalar order may extend the lattice order.
The stronger requirement that a scalar map also *reflect* order forces the
source order to be total.  Interval-valued semantics is one principled way to
retain incomparability, but incomparability alone does not forbid ordinary
one-way K&S scalar valuations.

## References

* Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
* Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
-/

import KnuthSkilling.Core.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic

namespace KnuthSkilling.TotalityImprecision

open KnuthSkilling

/-!
## Part 1: Partial Knuth-Skilling Algebra

The key weakening: replace LinearOrder with PartialOrder.
This allows incomparable elements, which represent "uncertain ordering"
in plausibility assignments.
-/

/-- A **Partial Knuth-Skilling Algebra**: the K&S axioms with partial order instead of linear order.

This captures systems where some plausibilities are incomparable.  An interval
model can retain that information, but further coherence assumptions are needed
before identifying such a model with a particular theory of imprecise
probability.

**Difference from `KnuthSkillingAlgebra`**:
- `KnuthSkillingAlgebra` extends `LinearOrder` (total order)
- `PartialKnuthSkillingAlgebra` extends `PartialOrder` (allows incomparability)
-/
class PartialKnuthSkillingAlgebra (α : Type*) extends PartialOrder α where
  /-- The combination operation -/
  op : α → α → α
  /-- Identity element -/
  ident : α
  /-- Associativity -/
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  /-- Right identity -/
  op_ident_right : ∀ x : α, op x ident = x
  /-- Left identity -/
  op_ident_left : ∀ x : α, op ident x = x
  /-- Monotonicity in first argument -/
  op_mono_left : ∀ y : α, Monotone (fun x => op x y)
  /-- Monotonicity in second argument -/
  op_mono_right : ∀ x : α, Monotone (fun y => op x y)
  /-- Identity is bottom -/
  ident_le : ∀ x : α, ident ≤ x

namespace PartialKnuthSkillingAlgebra

variable {α : Type*} [PartialKnuthSkillingAlgebra α]

/-- Two elements are incomparable if neither is ≤ the other. -/
def Incomparable (x y : α) : Prop := ¬(x ≤ y) ∧ ¬(y ≤ x)

/-- Incomparability is symmetric. -/
theorem incomparable_symm {x y : α} (h : Incomparable x y) : Incomparable y x :=
  ⟨h.2, h.1⟩

/-- Incomparable elements are distinct. -/
theorem incomparable_ne {x y : α} (h : Incomparable x y) : x ≠ y := by
  intro heq
  rw [heq] at h
  exact h.1 (le_refl y)

end PartialKnuthSkillingAlgebra

/-!
## Part 2: Interval Representation

This section studies a chosen interval representation [lower, upper] ⊆ ℝ.
The interval width measures imprecision in that representation.  Existence of
such a representation is data below, not a consequence of partial order alone.
-/

/-- An interval in ℝ representing an imprecise plausibility. -/
structure PlausibilityInterval where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  nonneg : 0 ≤ lower

namespace PlausibilityInterval

@[ext]
theorem ext {I J : PlausibilityInterval} (hl : I.lower = J.lower) (hu : I.upper = J.upper) :
    I = J := by
  cases I; cases J; simp only [mk.injEq]; exact ⟨hl, hu⟩

/-- A precise (point) value as a degenerate interval. -/
def point (x : ℝ) (hx : 0 ≤ x) : PlausibilityInterval where
  lower := x
  upper := x
  valid := le_refl x
  nonneg := hx

/-- The width (imprecision) of an interval. -/
def width (I : PlausibilityInterval) : ℝ := I.upper - I.lower

/-- Width is nonnegative. -/
theorem width_nonneg (I : PlausibilityInterval) : 0 ≤ I.width := by
  simp only [width]
  linarith [I.valid]

/-- An interval is precise iff its width is zero. -/
def isPrecise (I : PlausibilityInterval) : Prop := I.width = 0

theorem isPrecise_iff_eq (I : PlausibilityInterval) :
    I.isPrecise ↔ I.lower = I.upper := by
  simp only [isPrecise, width, sub_eq_zero]
  exact eq_comm

theorem point_isPrecise (x : ℝ) (hx : 0 ≤ x) : (point x hx).isPrecise := by
  simp [isPrecise, width, point]

/-- Interval addition (Minkowski sum). -/
def add (I J : PlausibilityInterval) : PlausibilityInterval where
  lower := I.lower + J.lower
  upper := I.upper + J.upper
  valid := add_le_add I.valid J.valid
  nonneg := add_nonneg I.nonneg J.nonneg

theorem add_width (I J : PlausibilityInterval) :
    (add I J).width = I.width + J.width := by
  simp only [add, width]; ring

/-- The identity interval [0, 0]. -/
def zero : PlausibilityInterval := point 0 (le_refl 0)

theorem add_zero (I : PlausibilityInterval) : add I zero = I := by
  apply ext
  · simp [add, zero, point]
  · simp [add, zero, point]

theorem zero_add (I : PlausibilityInterval) : add zero I = I := by
  apply ext
  · simp [add, zero, point]
  · simp [add, zero, point]

/-- Interval order: I ≤ J iff I.upper ≤ J.lower (strict separation).
    This is the "certainly less" relation used for interval comparisons. -/
def separated (I J : PlausibilityInterval) : Prop := I.upper ≤ J.lower

/-- Intervals are incomparable when they overlap but neither dominates. -/
def incomparable (I J : PlausibilityInterval) : Prop :=
  ¬separated I J ∧ ¬separated J I ∧ I ≠ J

/-- Overlapping intervals: ¬separated I J means J.lower < I.upper,
    and ¬separated J I means I.lower < J.upper. -/
theorem incomparable_overlap (I J : PlausibilityInterval) (h : incomparable I J) :
    I.lower < J.upper ∧ J.lower < I.upper := by
  simp only [incomparable, separated, not_le] at h
  -- h.1 : J.lower < I.upper (from ¬(I.upper ≤ J.lower))
  -- h.2.1 : I.lower < J.upper (from ¬(J.upper ≤ I.lower))
  exact ⟨h.2.1, h.1⟩

end PlausibilityInterval

/-!
## Part 3: The Key Theorems

### Theorem 1: Interval representation structure

For any `PartialKnuthSkillingAlgebra`, we can define an interval-valued representation.
-/

/-- An interval representation of a partial K&S algebra. -/
structure IntervalRepresentation (α : Type*) [PartialKnuthSkillingAlgebra α] where
  /-- The interval-valued measure -/
  Θ : α → PlausibilityInterval
  /-- Comparable elements have separated intervals -/
  order_respecting : ∀ x y : α, x < y → (Θ x).separated (Θ y)
  /-- Identity maps to zero interval -/
  ident_zero : Θ PartialKnuthSkillingAlgebra.ident = PlausibilityInterval.zero
  /-- Additivity holds as interval containment (lower bound) -/
  additive_lower : ∀ x y : α, (Θ x).lower + (Θ y).lower ≤ (Θ (PartialKnuthSkillingAlgebra.op x y)).lower
  /-- Additivity holds as interval containment (upper bound) -/
  additive_upper : ∀ x y : α, (Θ (PartialKnuthSkillingAlgebra.op x y)).upper ≤ (Θ x).upper + (Θ y).upper

/-- A representation is **precise** if all intervals are points. -/
def IntervalRepresentation.isPrecise {α : Type*} [PartialKnuthSkillingAlgebra α]
    (R : IntervalRepresentation α) : Prop :=
  ∀ x : α, (R.Θ x).isPrecise

/-- A **faithful** representation: separated intervals imply comparable elements.
This is the converse of order_respecting. -/
def IntervalRepresentation.isFaithful {α : Type*} [PartialKnuthSkillingAlgebra α]
    (R : IntervalRepresentation α) : Prop :=
  ∀ x y : α, (R.Θ x).separated (R.Θ y) → x ≤ y

/-!
### Theorem 2: Incomparable elements → overlapping intervals (for faithful representations)

If two elements are incomparable in the algebra, their interval representations
must overlap (neither can be separated from the other).
-/

/-- **Key Theorem**: For faithful representations, incomparable elements have overlapping intervals.

Proof: By contrapositive. If intervals were separated, faithfulness would imply comparability.
-/
theorem incomparable_implies_overlapping {α : Type*} [PartialKnuthSkillingAlgebra α]
    (R : IntervalRepresentation α) (hfaithful : R.isFaithful) (x y : α)
    (h : PartialKnuthSkillingAlgebra.Incomparable x y) :
    ¬(R.Θ x).separated (R.Θ y) ∧ ¬(R.Θ y).separated (R.Θ x) := by
  constructor
  · intro hsep
    -- If Θ(x) separated below Θ(y), faithfulness gives x ≤ y
    have hle : x ≤ y := hfaithful x y hsep
    -- But we assumed ¬(x ≤ y)
    exact h.1 hle
  · intro hsep
    -- If Θ(y) separated below Θ(x), faithfulness gives y ≤ x
    have hle : y ≤ x := hfaithful y x hsep
    -- But we assumed ¬(y ≤ x)
    exact h.2 hle

/-!
### Theorem 3: Totality eliminates incomparability

In a linear order, there are NO incomparable elements — every pair is comparable.
This is the key structural difference between LinearOrder and PartialOrder.
-/

/-- In a linear order, there are no incomparable elements. -/
theorem linear_order_no_incomparable {α : Type*} [LinearOrder α] (x y : α) :
    ¬(¬(x ≤ y) ∧ ¬(y ≤ x)) := by
  intro ⟨h1, h2⟩
  rcases le_or_gt x y with hle | hgt
  · exact h1 hle
  · exact h2 (le_of_lt hgt)

/-- Equivalently: in a linear order, all pairs are comparable. -/
theorem linear_order_all_comparable {α : Type*} [LinearOrder α] (x y : α) :
    x ≤ y ∨ y ≤ x := by
  rcases le_or_gt x y with hle | hgt
  · exact Or.inl hle
  · exact Or.inr (le_of_lt hgt)

/-!
### Order-Reflecting Point Representations Force Totality

If a partial order admits an order-reflecting point representation into `ℝ` (i.e. an order embedding),
then it must already be total: any two points become comparable because `ℝ` is linearly ordered.

This is stronger than the one-way fidelity used by Knuth and Skilling: their scalar
valuation may consistently add comparisons between incomparable lattice elements.
Dropping order reflection leads naturally to scalar extensions; retaining the
original incomparability leads naturally to interval- or product-valued semantics.
-/

/-- A point-valued representation into `ℝ` that both preserves and reflects order. -/
def OrderReflectingPointRepresentation (α : Type*) [PartialOrder α] : Prop :=
  ∃ Θ : α → ℝ, ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b

theorem totality_of_orderReflectingPointRepresentation {α : Type*} [PartialOrder α]
    (hΘ : OrderReflectingPointRepresentation α) :
    ∀ x y : α, x ≤ y ∨ y ≤ x := by
  rcases hΘ with ⟨Θ, hΘ⟩
  intro x y
  rcases le_total (Θ x) (Θ y) with hxy | hyx
  · exact Or.inl ((hΘ x y).2 hxy)
  · exact Or.inr ((hΘ y x).2 hyx)

theorem no_orderReflectingPointRepresentation_of_incomparable {α : Type*} [PartialOrder α]
    (hinc : ∃ x y : α, ¬(x ≤ y) ∧ ¬(y ≤ x)) :
    ¬ OrderReflectingPointRepresentation α := by
  intro hΘ
  rcases hinc with ⟨x, y, hx, hy⟩
  have htot := totality_of_orderReflectingPointRepresentation (α := α) hΘ x y
  cases htot with
  | inl hxy => exact hx hxy
  | inr hyx => exact hy hyx

theorem no_orderReflectingPointRepresentation_with_incomparables
    {α : Type*} [PartialKnuthSkillingAlgebra α]
    (x y : α) (hxy : PartialKnuthSkillingAlgebra.Incomparable x y) :
    ¬ ∃ (Θ : α → ℝ), ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b := by
  intro hΘ
  -- Any order-reflecting point representation forces totality, contradicting incomparability.
  have hinc : ∃ x y : α, ¬(x ≤ y) ∧ ¬(y ≤ x) := ⟨x, y, hxy.1, hxy.2⟩
  exact no_orderReflectingPointRepresentation_of_incomparable (α := α) hinc (by
    simpa [OrderReflectingPointRepresentation] using hΘ)

/-!
### Theorem 4: Totality Constrains Interval Separation

For faithful representations:
- PartialOrder allows incomparable elements → allows overlapping intervals → imprecision possible
- LinearOrder forbids incomparable elements → forbids overlapping intervals → more constrained

**Note**: Totality alone does NOT force intervals to collapse to points!
You also need density (Archimedean property) for that.

What totality DOES guarantee: intervals can be consistently totally ordered
(no overlapping pairs), which is a necessary (but not sufficient) condition for precision.
-/

/-- Totality ensures all interval pairs are separated or identical (no overlaps).

Note: We state this for a representation where the underlying order is known to be total.
The key insight is that totality (x ≤ y ∨ y ≤ x) combined with order_respecting
means intervals cannot overlap.
-/
theorem totality_no_overlapping_intervals {α : Type*} [PartialKnuthSkillingAlgebra α]
    (R : IntervalRepresentation α)
    (htotal : ∀ x y : α, x ≤ y ∨ y ≤ x)  -- Totality hypothesis
    (x y : α) :
    (R.Θ x).separated (R.Θ y) ∨ (R.Θ y).separated (R.Θ x) ∨ R.Θ x = R.Θ y := by
  -- By totality, either x ≤ y or y ≤ x
  rcases htotal x y with hxy | hyx
  · -- x ≤ y: either x < y (separated) or x = y (equal intervals)
    rcases hxy.lt_or_eq with hlt | heq
    · exact Or.inl (R.order_respecting x y hlt)
    · rw [heq]; exact Or.inr (Or.inr rfl)
  · -- y ≤ x: either y < x (separated) or y = x (equal intervals)
    rcases hyx.lt_or_eq with hlt | heq
    · exact Or.inr (Or.inl (R.order_respecting y x hlt))
    · rw [← heq]; exact Or.inr (Or.inr rfl)

/-!
## Part 4: Labels for Two Representation Policies

The following finite labels describe two representation policies.  They do not
assert that the source order alone determines the codomain or a probability
framework.

| Precision | Order Type | Representation | Framework |
|-----------|------------|----------------|-----------|
| Precise | scalar point model | Θ : α → ℝ | may support precise probability |
| Imprecise | interval model | Θ : α → [ℝ,ℝ] | may support lower/upper probability |
-/

/-- The precision axis values. -/
inductive PrecisionAxis where
  | precise : PrecisionAxis
  | imprecise : PrecisionAxis
deriving DecidableEq, Repr

/-- Map precision axis to order type requirement. -/
def PrecisionAxis.orderRequirement : PrecisionAxis → String
  | .precise => "chosen scalar point model"
  | .imprecise => "chosen interval model"

/-- Map precision axis to representation type. -/
def PrecisionAxis.representationType : PrecisionAxis → String
  | .precise => "Θ : α → ℝ (point-valued)"
  | .imprecise => "Θ : α → [ℝ,ℝ] (interval-valued)"

/-- Map precision axis to probability framework. -/
def PrecisionAxis.framework : PrecisionAxis → String
  | .precise => "compatible with precise probability"
  | .imprecise => "compatible with lower/upper probability"

/-- The labels expose the representation choice without claiming it follows
from the source order. -/
theorem precisionAxis_labels :
    (PrecisionAxis.precise).orderRequirement = "chosen scalar point model" ∧
    (PrecisionAxis.imprecise).orderRequirement = "chosen interval model" := by
  simp [PrecisionAxis.orderRequirement]

/-!
## Summary: Exact Scope of the Proven Results

### What We Have Proven:

1. **`PartialKnuthSkillingAlgebra`**: K&S axioms with PartialOrder instead of LinearOrder
   - Allows incomparable elements (neither x ≤ y nor y ≤ x)

2. **`incomparable_implies_overlapping`**: For a supplied faithful interval
   representation, incomparable algebra elements have non-separated images
   - This is one direction, proved by contrapositive using faithfulness

3. **`linear_order_no_incomparable`**: LinearOrder forbids incomparable elements
   - Proved from trichotomy

4. **`totality_no_overlapping_intervals`**: Under totality and an
   order-respecting interval representation,
   all interval pairs are separated or equal (no overlaps)
   - Proved by case analysis on x ≤ y ∨ y ≤ x

These results do **not** prove that deleting totality from the K&S hypotheses
constructs a Walley-style coherent lower prevision, nor that a partial order
cannot have a one-way faithful scalar valuation.  They identify the stronger
order-reflection hypothesis under which a real-valued point representation
would force totality, and the consequences of choosing a faithful interval
representation when incomparability is to be retained.
-/

end KnuthSkilling.TotalityImprecision
