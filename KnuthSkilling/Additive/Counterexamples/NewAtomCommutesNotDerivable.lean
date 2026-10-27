import KnuthSkilling.Additive.Proofs.GridInduction.Core.Induction.Goertzel
import KnuthSkilling.Additive.Counterexamples.SemidirectNoSeparation

/-!
# Base axioms do not force new-atom commutation

The semidirect model satisfies the ordered algebraic base and fails separation.
Its singleton grid does not commute with the new atom. Power decomposition is
equivalent to that commutation, so it fails for the same witness.
This separates the base profile from the stronger separation profile.
-/
namespace KnuthSkilling.Additive.Counterexamples
open KnuthSkillingAlgebra KnuthSkillingAlgebraBase KnuthSkilling.Additive

private theorem exX_pos : (ident : SD) < SD.exX := by
  apply lt_of_le_of_ne (ident_le _)
  simp [KnuthSkillingAlgebraBase.ident, SD.ident, SD.exX]

theorem exists_not_newAtomCommutes :
    ∃ (F : AtomFamily SD 1) (d : SD), ¬ NewAtomCommutes F d := by
  refine ⟨singletonAtomFamily SD.exX exX_pos, SD.exY, ?_⟩
  intro h
  exact SD.op_not_comm (h 0)

theorem exists_not_newAtomDecompose :
    ∃ (F : AtomFamily SD 1) (d : SD), ¬ NewAtomDecompose F d := by
  obtain ⟨F, d, h⟩ := exists_not_newAtomCommutes
  exact ⟨F, d, fun hd => h ((newAtomDecompose_iff_newAtomCommutes).mp hd)⟩
end KnuthSkilling.Additive.Counterexamples
