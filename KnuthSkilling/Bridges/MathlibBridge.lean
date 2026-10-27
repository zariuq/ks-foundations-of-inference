import Mathlib.Algebra.Order.Archimedean.Basic

import KnuthSkilling.Core.Algebra
import KnuthSkilling.Additive.Axioms.SandwichSeparation

namespace KnuthSkilling

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# KS operations as ordered additive monoids

The wrapper retains the supplied operation and order. Separation provides
commutativity and an Archimedean bound; one adapter turns that bound into the
Mathlib class. Group embeddings still require their additional group premises.
-/

/-- Type wrapper interpreting `KnuthSkillingAlgebraBase.op` as addition and `ident` as `0`. -/
structure KSAdd (α : Type*) where
  val : α

namespace KSAdd

@[ext] theorem ext {α : Type*} {x y : KSAdd α} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance {α : Type*} [LE α] : LE (KSAdd α) := ⟨fun x y => x.val ≤ y.val⟩
instance {α : Type*} [LT α] : LT (KSAdd α) := ⟨fun x y => x.val < y.val⟩

instance {α : Type*} [LinearOrder α] : PartialOrder (KSAdd α) where
  le x y := x.val ≤ y.val
  lt x y := x.val < y.val
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm x y hxy hyx := by
    apply KSAdd.ext
    exact le_antisymm hxy hyx
  lt_iff_le_not_ge x y := by
    -- transport the linear-order characterization of `<` from `α`
    simpa using (lt_iff_le_not_ge : x.val < y.val ↔ x.val ≤ y.val ∧ ¬ y.val ≤ x.val)

instance {α : Type*} [KnuthSkillingAlgebraBase α] : Zero (KSAdd α) :=
  ⟨⟨ident⟩⟩

instance {α : Type*} [KnuthSkillingAlgebraBase α] : Add (KSAdd α) :=
  ⟨fun x y => ⟨op x.val y.val⟩⟩

@[simp] theorem val_zero {α : Type*} [KnuthSkillingAlgebraBase α] : (0 : KSAdd α).val = ident := rfl
@[simp] theorem val_add {α : Type*} [KnuthSkillingAlgebraBase α] (x y : KSAdd α) :
    (x + y).val = op x.val y.val := rfl

/-- Turn a commutative K&S operation into an additive commutative monoid structure (on the wrapper). -/
@[instance_reducible] def instAddCommMonoid {α : Type*} [KnuthSkillingAlgebraBase α]
    (hcomm : ∀ x y : α, op x y = op y x) : AddCommMonoid (KSAdd α) where
  add := (· + ·)
  zero := (0 : KSAdd α)
  nsmul n x := ⟨iterate_op x.val n⟩
  nsmul_zero x := by
    ext
    exact iterate_op_zero x.val
  nsmul_succ n x := by
    ext
    have hswap : op x.val (iterate_op x.val n) = op (iterate_op x.val n) x.val := by
      simpa using (hcomm x.val (iterate_op x.val n))
    exact (iterate_op_succ x.val n).trans hswap
  add_assoc x y z := by
    ext
    simpa [val_add] using (op_assoc x.val y.val z.val)
  zero_add x := by
    ext
    simpa [val_add, val_zero] using (op_ident_left x.val)
  add_zero x := by
    ext
    simpa [val_add, val_zero] using (op_ident_right x.val)
  add_comm x y := by
    ext
    simpa [val_add] using (hcomm x.val y.val)

/-- Legacy: `op_archimedean` implies mathlib's `Archimedean` given commutativity.
This version takes an explicit Archimedean hypothesis for use in contexts without `KSSeparation`. -/
theorem archimedean_of_op_archimedean_explicit {α : Type*} [KnuthSkillingAlgebraBase α]
    (hcomm : ∀ x y : α, op x y = op y x)
    (harch : ∀ (a x : α), ident < a → ∃ n : ℕ, x < Nat.iterate (op a) n a) :
    @Archimedean (KSAdd α) (instAddCommMonoid (α := α) hcomm) (by infer_instance) := by
  classical
  let : AddCommMonoid (KSAdd α) := instAddCommMonoid (α := α) hcomm
  refine ⟨?_⟩
  intro x y hy
  obtain ⟨n, hn⟩ := harch y.val x.val (by
    exact hy)
  refine ⟨n + 1, ?_⟩
  have hn' : x.val < iterate_op y.val (n + 1) := by
    simpa [nat_iterate_eq_iterate_op_succ] using hn
  exact (le_of_lt hn')

/-- Under `KSSeparation`, we get mathlib's `Archimedean` once we view `op` as commutative addition.

Commutativity and the Archimedean property are both derived from `KSSeparation`
(see `SandwichSeparation.lean`). -/
theorem archimedean_of_KSSeparation {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α] :
    @Archimedean (KSAdd α) (instAddCommMonoid (α := α)
      (fun x y => SandwichSeparation.ksSeparation_implies_commutative (α := α) x y))
      (by infer_instance) :=
  archimedean_of_op_archimedean_explicit
    (fun x y => SandwichSeparation.ksSeparation_implies_commutative (α := α) x y)
    (fun a x h => SandwichSeparation.SeparationToArchimedean.op_archimedean_of_separation a x h)

end KSAdd

end KnuthSkilling
