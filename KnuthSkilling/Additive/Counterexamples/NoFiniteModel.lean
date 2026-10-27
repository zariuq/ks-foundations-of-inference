import Mathlib.Data.Fintype.EquivFin
import KnuthSkilling.Core.Algebra

namespace KnuthSkilling.Additive.Counterexamples

open Classical KnuthSkillingAlgebra KnuthSkillingAlgebraBase

/-!
# Finite minimum-identity models are trivial

A nonidentity element is positive and has injective natural iteration.
An infinite sequence cannot inject into a finite carrier. This rules out
nontrivial finite countermodel searches without assuming separation.
-/

variable {α : Type*} [Fintype α] [KnuthSkillingAlgebra α]

theorem card_le_one_of_fintype_knuthskilling : Fintype.card α ≤ 1 := by
  by_contra h
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card (Nat.lt_of_not_ge h) (ident : α)
  have hp : ident < a := lt_of_le_of_ne (ident_le a) (Ne.symm ha)
  exact not_injective_infinite_finite (f := iterate_op a) (iterate_op_strictMono a hp).injective

theorem subsingleton_of_fintype_knuthskilling : Subsingleton α :=
  Fintype.card_le_one_iff_subsingleton.mp (card_le_one_of_fintype_knuthskilling (α := α))

end KnuthSkilling.Additive.Counterexamples
