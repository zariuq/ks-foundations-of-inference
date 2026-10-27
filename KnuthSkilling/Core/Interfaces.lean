import KnuthSkilling.Literature.FunctionalEquations
import KnuthSkilling.Additive.Representation
import KnuthSkilling.Multiplicative.FunctionalEquation
import KnuthSkilling.Multiplicative.StrictMonoSolution

/-!
# Stable additive and multiplicative interfaces

Appendix A provides an additive order embedding. `AdditiveOrderIsoRep` is
stronger: it supplies an inverse on every real. The Appendix B product equation,
strict monotonicity and positivity imply continuity and an exponential form.
-/

namespace KnuthSkilling

/-- A *strong* additive representation: an operation `op` is conjugate to real addition
by an order isomorphism `Θ : α ≃o ℝ`.

This form is most useful when we need an explicit inverse `Ψ := Θ⁻¹` (Appendix B).

For Appendix A itself, the default / minimal interface is identity-free:
`KnuthSkilling.Additive.HasRepresentationTheorem`. -/
abbrev AdditiveOrderIsoRep := Literature.AdditiveOrderIsoRep

namespace AdditiveOrderIsoRep

export Literature.AdditiveOrderIsoRep (Θ map_op op_comm op_assoc strictMono_left strictMono_right)

end AdditiveOrderIsoRep

/-- The Appendix B product equation: Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ,η)).

This equation arises from distributivity (Axiom 3) when ⊗ has an additive representation. -/
abbrev ProductEquation := Multiplicative.ProductEquation

/-- **KEY THEOREM**: Continuity is DERIVED from ProductEquation + StrictMono + Positivity.

This is crucial because K&S's approach avoids assuming continuity - it falls out from
the algebraic structure plus monotonicity. The proof uses:
1. Doubling property: Ψ(θ + na) = 2^n · Ψ(θ)
2. Dense range: {m · C/2^k : m ≥ 1, k ∈ ℕ} is dense in (0, ∞)
3. Monotonicity forces continuity (no jumps possible with dense range)
-/
theorem continuity_from_productEquation_strictMono_pos
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hMono : StrictMono Ψ) : Continuous Ψ :=
  Multiplicative.productEquation_strictMono_pos_continuous Ψ ζ hProd hPos hMono

/-- **MAIN APPENDIX B THEOREM** (StrictMono case): If Ψ satisfies the product equation,
is positive, and is strictly monotone, then Ψ(x) = C · exp(A · x) for some C > 0, A ∈ ℝ.

Continuity is derived (not assumed) via `continuity_from_productEquation_strictMono_pos`. -/
theorem appendixB_exponential_strictMono
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hMono : StrictMono Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) :=
  Multiplicative.productEquation_solution_of_strictMono Ψ ζ hProd hPos hMono

/-- **MAIN APPENDIX B THEOREM** (StrictAnti case): Same conclusion for strictly decreasing Ψ. -/
theorem appendixB_exponential_strictAnti
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hAnti : StrictAnti Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) :=
  Multiplicative.productEquation_solution_of_strictAnti Ψ ζ hProd hPos hAnti

end KnuthSkilling
