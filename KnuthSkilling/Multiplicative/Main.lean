import Mathlib.Analysis.SpecialFunctions.Exp
import KnuthSkilling.Multiplicative.FunctionalEquation
import KnuthSkilling.Multiplicative.Basic
import KnuthSkilling.Multiplicative.ScaledMultRep

/-!
# The global inverse-representation route to scaled multiplication

An additive order isomorphism and distributivity give the product equation.
Its exponential solver determines the tensor scale. The shared `ScaledMultRep`
then provides the normalization laws. The separate direct tensor proof has
weaker algebraic premises and supplies the same output interface.
-/

namespace KnuthSkilling.Multiplicative

open Classical
open Set
open scoped Topology

open KnuthSkilling.Literature

variable {tensor : PosReal → PosReal → PosReal}

/-- The inverse `Ψ := Θ⁻¹` satisfies the Appendix B product equation. -/
theorem productEquation_Psi
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ProductEquation (Derived.Psi hRep) (Derived.zeta hRep) :=
  Derived.productEquation_of_distributes (tensor := tensor) hRep hDistrib

/-- Appendix B: `Ψ = Θ⁻¹` is an exponential, given the product equation regularity.

In our setting, continuity and strict monotonicity are *derived* because `Θ` is an order isomorphism.
-/
theorem Psi_is_exp
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ (C A : ℝ), 0 < C ∧ ∀ x : ℝ, Derived.Psi hRep x = C * Real.exp (A * x) := by
  refine
    productEquation_solution_of_continuous_strictMono
      (hEq := productEquation_Psi (tensor := tensor) hRep hDistrib)
      (hPos := fun x => Derived.Psi_pos (tensor := tensor) hRep x)
      (hCont := Derived.Psi_continuous (tensor := tensor) hRep)
      (hMono := Derived.Psi_strictMono (tensor := tensor) hRep)

/-- The direct-product scalar operation is multiplication up to a global constant.

More precisely, if `C := Ψ(0)`, then
`(x ⊗ y) = (x * y) / C` (after coercion to `ℝ`).

This matches the paper's statement that one may set `C = 1` "without loss of generality".
-/
theorem tensor_coe_eq_mul_div_const
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  rcases Psi_is_exp (tensor := tensor) hRep hDistrib with ⟨C, A, hC, hPsi⟩
  refine ⟨C, hC, ?_⟩
  intro x y
  have hC_ne : C ≠ 0 := ne_of_gt hC
  have hx : (x : ℝ) = C * Real.exp (A * hRep.Θ x) := by
    simpa [Derived.Psi] using (hPsi (hRep.Θ x))
  have hy : (y : ℝ) = C * Real.exp (A * hRep.Θ y) := by
    simpa [Derived.Psi] using (hPsi (hRep.Θ y))

  have hxy : ((tensor x y : PosReal) : ℝ) = C * Real.exp (A * (hRep.Θ x + hRep.Θ y)) := by
    have : hRep.Θ (tensor x y) = hRep.Θ x + hRep.Θ y := hRep.map_op x y
    calc
      ((tensor x y : PosReal) : ℝ)
          = Derived.Psi hRep (hRep.Θ (tensor x y)) := by simp [Derived.Psi]
      _ = C * Real.exp (A * (hRep.Θ (tensor x y))) := by simpa using (hPsi (hRep.Θ (tensor x y)))
      _ = C * Real.exp (A * (hRep.Θ x + hRep.Θ y)) := by simp [this]
  calc
    ((tensor x y : PosReal) : ℝ)
        = C * (Real.exp (A * hRep.Θ x) * Real.exp (A * hRep.Θ y)) := by
            simp [hxy, mul_add, Real.exp_add]
    _ = ((C * Real.exp (A * hRep.Θ x)) * (C * Real.exp (A * hRep.Θ y))) / C := by
            field_simp [hC_ne]
    _ = ((x : ℝ) * (y : ℝ)) / C := by
            simp [hx, hy, mul_assoc, mul_left_comm]

/-- Canonical normalization: rescale measures by `C` so that `⊗` becomes literal multiplication.

If `m(x) := x / C`, then `m(x ⊗ y) = m(x) * m(y)`.
-/
theorem tensor_mul_rule_normalized
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : PosReal, 0 < ((x : ℝ) / C)) ∧
      (∀ x y : PosReal,
        ((tensor x y : PosReal) : ℝ) / C = (((x : ℝ) / C) * ((y : ℝ) / C))) := by
  obtain ⟨C, hC, hMul⟩ := tensor_coe_eq_mul_div_const hRep hDistrib
  let result : ScaledMultRep tensor := ⟨C, hC, hMul⟩
  exact ⟨C, hC, fun x => div_pos x.2 hC, result.tensor_normalized⟩

/-- If `⊗` is multiplication up to a global constant `C`, then it admits a concrete additive
order-isomorphism representation with a logarithmic `Θ`.

This is the paper's `Θ(x) = (1/A) * log(x/C)` specialization (with `A = 1` and the shift by
`log C` absorbed into the choice of `Θ`), matching TeX around eq. (\"directprodrule\"). -/
noncomputable def additiveOrderIsoRep_of_mul_div_const
    {tensor : PosReal → PosReal → PosReal}
    (C : ℝ) (hC : 0 < C)
    (hMul : ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C) :
    AdditiveOrderIsoRep PosReal tensor where
  Θ := (Real.expOrderIso.symm).trans (OrderIso.addRight (-Real.log C))
  map_op := by
    intro x y
    change Real.expOrderIso.symm (tensor x y) + -Real.log C =
      (Real.expOrderIso.symm x + -Real.log C) +
        (Real.expOrderIso.symm y + -Real.log C)
    rw [← Real.log_of_pos (tensor x y).2, ← Real.log_of_pos x.2, ← Real.log_of_pos y.2,
      hMul, Real.log_div (mul_ne_zero (ne_of_gt x.2) (ne_of_gt y.2)) (ne_of_gt hC),
      Real.log_mul (ne_of_gt x.2) (ne_of_gt y.2)]
    ring

/-- K&S Appendix B provides the `ScaledMultRep` interface.

This is the K&S path: uses `AdditiveOrderIsoRep` from Appendix A to derive scaled multiplication. -/
noncomputable def scaledMultRep_of_additiveOrderIsoRep
    {tensor : PosReal → PosReal → PosReal}
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ScaledMultRep tensor :=
  ScaledMultRep.ofExists (tensor_coe_eq_mul_div_const hRep hDistrib)

end KnuthSkilling.Multiplicative
