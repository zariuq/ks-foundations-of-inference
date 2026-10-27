import Mathlib.Topology.Order.MonotoneContinuity
import KnuthSkilling.Multiplicative.FunctionalEquation
import KnuthSkilling.Literature.FunctionalEquations

/-!
# From an additive order isomorphism to the product equation

The supplied representation is onto the real line and therefore has a global
inverse. Distributivity transports through that inverse to `ProductEquation`.
This file consumes the representation; it does not derive its existence from
Cox's interval axioms or from an arbitrary additive embedding.
-/

namespace KnuthSkilling.Multiplicative

open Classical
open Set
open scoped Topology

/-- Positive real numbers, used as the scalar range of measures in Appendix B. -/
abbrev PosReal := Ioi (0 : ℝ)

/-- Addition on positive reals (closed since `0 < x` and `0 < y` implies `0 < x + y`). -/
@[simp] noncomputable def addPos (x y : PosReal) : PosReal :=
  ⟨(x : ℝ) + (y : ℝ), by
    simpa [PosReal] using add_pos x.2 y.2⟩

@[simp] theorem coe_addPos (x y : PosReal) : ((addPos x y : PosReal) : ℝ) = (x : ℝ) + (y : ℝ) := by
  rfl

/-- Multiplication on positive reals (closed since `0 < x` and `0 < y` implies `0 < x * y`). -/
@[simp] def mulPos (x y : PosReal) : PosReal :=
  ⟨(x : ℝ) * (y : ℝ), by
    simpa [PosReal] using mul_pos x.2 y.2⟩

@[simp] theorem coe_mulPos (x y : PosReal) : ((mulPos x y : PosReal) : ℝ) = (x : ℝ) * (y : ℝ) := by
  rfl

/-- The distributivity axiom for `⊗` over `+` (paper eq. ("axiom3"))

`(x ⊗ t) + (y ⊗ t) = (x + y) ⊗ t`.

We package it for `PosReal` using `addPos` for closure. -/
def DistributesOverAdd (tensor : PosReal → PosReal → PosReal) : Prop :=
  ∀ x y t : PosReal, tensor (addPos x y) t = addPos (tensor x t) (tensor y t)

/-- Tensor associativity: `(u ⊗ v) ⊗ w = u ⊗ (v ⊗ w)`. -/
def TensorAssoc (tensor : PosReal → PosReal → PosReal) : Prop :=
  ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w)

/-- Tensor maps positive to positive. This is automatic for `PosReal → PosReal → PosReal`
    but we state it for documentation and uniformity. -/
def TensorPos (tensor : PosReal → PosReal → PosReal) : Prop :=
  ∀ x y : PosReal, 0 < (tensor x y).val

/-- Tensor is strictly monotone in the left argument. -/
def TensorStrictMonoLeft (tensor : PosReal → PosReal → PosReal) : Prop :=
  ∀ t : PosReal, StrictMono (fun x => tensor x t)

/-- Tensor is strictly monotone in the right argument. -/
def TensorStrictMonoRight (tensor : PosReal → PosReal → PosReal) : Prop :=
  ∀ x : PosReal, StrictMono (fun t => tensor x t)

/-- **TensorAlgebra**: Bundled tensor axioms for the K&S Product Theorem.

This bundles:
- Distributivity over addition (`DistributesOverAdd`)
- Associativity (`TensorAssoc`)
- Positivity (`TensorPos`)

Use the unbundled predicates directly for minimal-hypothesis theorems,
or use `[TensorAlgebra tensor]` for convenience in longer proofs. -/
class TensorAlgebra (tensor : PosReal → PosReal → PosReal) : Prop where
  /-- Tensor distributes over addition: `(x + y) ⊗ t = (x ⊗ t) + (y ⊗ t)`. -/
  distributes : DistributesOverAdd tensor
  /-- Tensor is associative: `(u ⊗ v) ⊗ w = u ⊗ (v ⊗ w)`. -/
  assoc : TensorAssoc tensor
  /-- Tensor maps positive reals to positive reals. -/
  pos : TensorPos tensor

namespace TensorAlgebra

variable {tensor : PosReal → PosReal → PosReal} [TensorAlgebra tensor]

/-- Access distributivity from the bundled class. -/
theorem distributesOverAdd : DistributesOverAdd tensor := TensorAlgebra.distributes

/-- Access associativity from the bundled class. -/
theorem tensorAssoc : TensorAssoc tensor := TensorAlgebra.assoc

/-- Access positivity from the bundled class. -/
theorem tensorPos : TensorPos tensor := TensorAlgebra.pos

end TensorAlgebra

namespace Derived

open KnuthSkilling.Literature

variable {tensor : PosReal → PosReal → PosReal}

/-- `Ψ := Θ⁻¹` as a real-valued function (paper uses `Ψ = Θ^{-1}`),
from an additive order-isomorphism representation of `tensor`. -/
noncomputable def Psi (hRep : AdditiveOrderIsoRep PosReal tensor) : ℝ → ℝ :=
  fun r => ((hRep.Θ.symm r : PosReal) : ℝ)

/-- `ζ(ξ,η) := Θ(x+y)` where `x = Ψ ξ`, `y = Ψ η`.

This matches the paper definition `ζ = Θ(x+y)` (see around TeX eq. (\"prodeqn\")). -/
noncomputable def zeta (hRep : AdditiveOrderIsoRep PosReal tensor) : ℝ → ℝ → ℝ :=
  fun ξ η => hRep.Θ (addPos (hRep.Θ.symm ξ) (hRep.Θ.symm η))

/-- Positivity of `Psi`: its values lie in `Ioi 0`. -/
theorem Psi_pos (hRep : AdditiveOrderIsoRep PosReal tensor) (r : ℝ) : 0 < Psi hRep r :=
  (hRep.Θ.symm r).2

/-- `Psi` is strictly monotone (since it is `Subtype.val ∘ Θ.symm`). -/
theorem Psi_strictMono (hRep : AdditiveOrderIsoRep PosReal tensor) : StrictMono (Psi hRep) := by
  intro x y hxy
  have hxy' : hRep.Θ.symm x < hRep.Θ.symm y := hRep.Θ.symm.strictMono hxy
  simpa [Psi] using hxy'

/-- `Psi` is continuous (order isomorphisms are continuous for order topology). -/
theorem Psi_continuous (hRep : AdditiveOrderIsoRep PosReal tensor) : Continuous (Psi hRep) := by
  unfold Psi
  exact continuous_subtype_val.comp hRep.Θ.symm.continuous

/-- The K&S product equation derived from:

1. An additive order-isomorphism representation `Θ(x ⊗ t) = Θ x + Θ t` (paper eq. (\"thetaproduct\"))
2. Distributivity `(x ⊗ t) + (y ⊗ t) = (x+y) ⊗ t` (paper eq. (\"axiom3\")).

This is exactly the paper transition to the product equation (TeX eq. (\"prodeqn\")). -/
theorem productEquation_of_distributes
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ProductEquation (Psi hRep) (zeta hRep) := by
  intro τ ξ η
  have decode (x y : PosReal) : tensor x y = hRep.Θ.symm (hRep.Θ x + hRep.Θ y) := by
    apply hRep.Θ.injective
    rw [hRep.map_op, OrderIso.apply_symm_apply]
  have h := congrArg (fun x : PosReal => (x : ℝ))
    (hDistrib (hRep.Θ.symm ξ) (hRep.Θ.symm η) (hRep.Θ.symm τ))
  simp only [coe_addPos] at h
  simp_rw [decode, OrderIso.apply_symm_apply] at h
  simpa only [Psi, zeta, add_comm] using h.symm

/-- The K&S product equation using bundled `TensorAlgebra` instance.

This is a convenience wrapper around `productEquation_of_distributes` that uses
the bundled class for ergonomics in longer proofs. -/
theorem productEquation_of_tensorAlgebra
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    [TensorAlgebra tensor] :
    ProductEquation (Psi hRep) (zeta hRep) :=
  productEquation_of_distributes hRep TensorAlgebra.distributesOverAdd

end Derived

end KnuthSkilling.Multiplicative
