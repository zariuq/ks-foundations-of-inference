import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import KnuthSkilling.Multiplicative.Basic
import KnuthSkilling.Multiplicative.ScaledMultRep

/-!
# Distributive tensors on positive reals

Distributivity makes the tensor linear in its left argument. Associativity
and injectivity of t ↦ tensor 1 t then force one global multiplication scale.
This algebraic theorem uses no continuity premise. An additive order isomorphism
is a sufficient input to its regularity interface, not a conclusion of Cox's
interval representation theorem.
-/

namespace KnuthSkilling.Multiplicative

open Classical
open Set

open KnuthSkilling.Literature

/-- The distinguished element `1 : (0,∞)` (as a `PosReal`). -/
def onePos : PosReal := ⟨(1 : ℝ), by norm_num⟩

@[simp] theorem coe_onePos : ((onePos : PosReal) : ℝ) = 1 := rfl

/-- A **regularity hypothesis package** for a tensor-like operation `⊗` on positive reals.

This is *not* an additional axiom of the KS project: it is a convenient bundle of properties
used by this file’s direct argument.  When one already has an additive order-isomorphism
representation `Θ (x ⊗ y) = Θ x + Θ y`, these properties are derivable.
-/
structure TensorRegularity (tensor : PosReal → PosReal → PosReal) : Prop where
  /-- Associativity (K&S Axiom 4). -/
  assoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w)
  /-- Injectivity of the “right scaling factor” map `t ↦ 1 ⊗ t`. -/
  inj_kPos : Function.Injective (fun t : PosReal => tensor onePos t)

namespace TensorRegularity

variable {tensor : PosReal → PosReal → PosReal}

/-- If `⊗` is conjugate to addition by an order isomorphism, then it satisfies the regularity
package used in this file. -/
theorem of_additiveOrderIsoRep (hRep : AdditiveOrderIsoRep PosReal tensor) :
    TensorRegularity tensor := by
  refine ⟨?_, ?_⟩
  · intro u v w
    simpa using (AdditiveOrderIsoRep.op_assoc (α := PosReal) (op := tensor) hRep u v w)
  · -- Injectivity follows from strict monotonicity, which is automatic under representation.
    have hmono : StrictMono fun t : PosReal => tensor onePos t := by
      simpa using
        (AdditiveOrderIsoRep.strictMono_right (α := PosReal) (op := tensor) hRep onePos)
    exact hmono.injective

end TensorRegularity

namespace TensorDerivation

variable {tensor : PosReal → PosReal → PosReal}

/-- The “right scaling factor” induced by a tensor: `k(t) := 1 ⊗ t`. -/
def kPos (tensor : PosReal → PosReal → PosReal) (t : PosReal) : PosReal :=
  tensor onePos t

@[simp] theorem coe_kPos (tensor : PosReal → PosReal → PosReal) (t : PosReal) :
    ((kPos tensor t : PosReal) : ℝ) = ((tensor onePos t : PosReal) : ℝ) :=
  rfl

/-- From distributivity over `+`, the tensor is linear in the left argument:
`(x ⊗ t) = x * (1 ⊗ t)` (after coercion to `ℝ`). -/
theorem tensor_coe_eq_mul_kPos
    (hDistrib : DistributesOverAdd tensor) (t x : PosReal) :
    ((tensor x t : PosReal) : ℝ) = ((x : ℝ) * ((kPos tensor t : PosReal) : ℝ)) := by
  let f : ℝ → ℝ := fun r => if hr : 0 < r then ((tensor ⟨r, hr⟩ t : PosReal) : ℝ) else 0

  have hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v := by
    intro u v hu hv
    have huv : 0 < u + v := add_pos hu hv
    have hdis :
        tensor (addPos ⟨u, hu⟩ ⟨v, hv⟩) t = addPos (tensor ⟨u, hu⟩ t) (tensor ⟨v, hv⟩ t) :=
      hDistrib ⟨u, hu⟩ ⟨v, hv⟩ t
    have hdis' : ((tensor (addPos ⟨u, hu⟩ ⟨v, hv⟩) t : PosReal) : ℝ)
        = ((tensor ⟨u, hu⟩ t : PosReal) : ℝ) + ((tensor ⟨v, hv⟩ t : PosReal) : ℝ) := by
      simpa [coe_addPos] using congrArg (fun z : PosReal => (z : ℝ)) hdis
    simpa [f, hu, hv, huv] using hdis'

  have hpos : ∀ {u : ℝ}, 0 < u → 0 < f u := by
    intro u hu
    simp [f, hu]
    have hmem : ((tensor ⟨u, hu⟩ t : PosReal) : ℝ) ∈ PosReal := (tensor ⟨u, hu⟩ t).2
    change ((tensor ⟨u, hu⟩ t : PosReal) : ℝ) ∈ Ioi (0 : ℝ) at hmem
    exact (Set.mem_Ioi).1 hmem

  rcases AdditiveOnPos.exists_mul_const_of_add_of_pos f hadd (hpos := hpos) with ⟨c, hc, hc_spec⟩
  have h1 : f 1 = c := by
    have h := hc_spec (u := (1 : ℝ)) (by norm_num)
    simpa [one_mul] using h

  have hc_eq : c = ((kPos tensor t : PosReal) : ℝ) := by
    have h' : f 1 = ((kPos tensor t : PosReal) : ℝ) := by
      simp [f, kPos, onePos, show (0 : ℝ) < 1 by norm_num]
    exact by simpa [h'] using h1.symm
  have hx_pos : 0 < (x : ℝ) := by
    have hmem : (x : ℝ) ∈ PosReal := x.2
    change (x : ℝ) ∈ Ioi (0 : ℝ) at hmem
    exact (Set.mem_Ioi).1 hmem
  have hx : f (x : ℝ) = c * (x : ℝ) := hc_spec (u := (x : ℝ)) hx_pos
  have hx' : ((tensor x t : PosReal) : ℝ) = c * (x : ℝ) := by
    simpa [f, hx_pos] using hx
  simpa [hc_eq, mul_comm, mul_left_comm, mul_assoc] using hx'

/-- Associativity reflects commutativity of represented scaling factors. -/
theorem tensor_comm (hTensor : TensorRegularity tensor) (hDistrib : DistributesOverAdd tensor)
    (x y : PosReal) : tensor x y = tensor y x := by
  apply hTensor.inj_kPos
  change tensor onePos (tensor x y) = tensor onePos (tensor y x)
  rw [← hTensor.assoc, ← hTensor.assoc]
  apply Subtype.ext
  change (tensor (kPos tensor x) y : ℝ) = (tensor (kPos tensor y) x : ℝ)
  rw [tensor_coe_eq_mul_kPos hDistrib, tensor_coe_eq_mul_kPos hDistrib]
  exact mul_comm _ _

/-- The right scaling map has the constant coefficient observed at one. -/
theorem kPos_coe_eq_mul (hTensor : TensorRegularity tensor) (hDistrib : DistributesOverAdd tensor)
    (y : PosReal) : (kPos tensor y : ℝ) = (y : ℝ) * (kPos tensor onePos : ℝ) := by
  change (tensor onePos y : ℝ) = _
  rw [tensor_comm hTensor hDistrib onePos y]
  exact tensor_coe_eq_mul_kPos hDistrib onePos y

/-- Log of a positive product in `PosReal` is additive. -/
theorem log_mulPos (a b : PosReal) :
    Real.expOrderIso.symm (mulPos a b) = Real.expOrderIso.symm a + Real.expOrderIso.symm b := by
  rw [← Real.log_of_pos a.2, ← Real.log_of_pos b.2,
    ← Real.log_of_pos (mulPos a b).2]
  exact Real.log_mul (ne_of_gt a.2) (ne_of_gt b.2)

/-- `exp` regrades multiplication on `PosReal` into addition on `ℝ`. -/
theorem mulPos_expOrderIso (x y : ℝ) : mulPos (Real.expOrderIso x) (Real.expOrderIso y) = Real.expOrderIso (x + y) := by
  ext
  simp [mulPos, Real.exp_add]

/-- The key functional equation induced by associativity, in logarithmic coordinates. -/
theorem g_equation
    (hTensor : TensorRegularity tensor) (hDistrib : DistributesOverAdd tensor) :
    let g : ℝ → ℝ := fun x => Real.expOrderIso.symm (kPos tensor (Real.expOrderIso x))
    ∀ x y : ℝ, g (x + g y) = g x + g y := by
  intro g x y
  have hg (t : ℝ) : g t = t + Real.log (kPos tensor onePos : ℝ) := by
    change Real.expOrderIso.symm (kPos tensor (Real.expOrderIso t)) = _
    rw [← Real.log_of_pos (kPos tensor (Real.expOrderIso t)).2]
    rw [kPos_coe_eq_mul hTensor hDistrib, Real.coe_expOrderIso_apply,
      Real.log_mul (ne_of_gt (Real.exp_pos t)) (ne_of_gt (kPos tensor onePos).2)]
    simp
  simp only [hg]
  ring

/-- Solve `g(x+g(y)) = g(x) + g(y)` assuming only injectivity of `g`: `g(x) = x + c`. -/
theorem g_eq_add_const_of_injective
    (g : ℝ → ℝ)
    (hg : Function.Injective g)
    (hg_eq : ∀ x y : ℝ, g (x + g y) = g x + g y) :
    ∃ c : ℝ, ∀ x : ℝ, g x = x + c := by
  let c : ℝ := g 0
  refine ⟨c, ?_⟩
  intro y

  have hneg : ∀ y : ℝ, g (-g y) = c - g y := by
    intro y
    have h1 := hg_eq (-g y) y
    have : c = g (-g y) + g y := by
      simpa [c] using h1
    linarith

  have hc0 : g (-c) = 0 := by
    simpa [c] using hneg 0

  have hfix : g (-c + g y) = g y := by
    have h2 := hg_eq (-c) y
    simpa [hc0] using h2

  have : -c + g y = y := hg hfix
  linarith

/-- Main theorem: from tensor axioms and distributivity, `⊗` is multiplication up to a global scale. -/
theorem tensor_coe_eq_mul_div_const_of_tensorRegularity
    (hTensor : TensorRegularity tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  refine ⟨1 / (kPos tensor onePos : ℝ), one_div_pos.mpr (kPos tensor onePos).2, ?_⟩
  intro x y
  rw [tensor_coe_eq_mul_kPos hDistrib, kPos_coe_eq_mul hTensor hDistrib]
  simp [div_eq_mul_inv, mul_assoc]

end TensorDerivation

namespace TensorDerivation

variable {tensor : PosReal → PosReal → PosReal}

/-- Distributivity over `+` forces injectivity in the **left** argument:
for each fixed `t`, the map `x ↦ x ⊗ t` is injective on `(0,∞)`. -/
theorem inj_left_of_distrib
    (hDistrib : DistributesOverAdd tensor) (t : PosReal) :
    Function.Injective (fun x : PosReal => tensor x t) := by
  intro x y h
  apply Subtype.ext
  have hc := congrArg (fun z : PosReal => (z : ℝ)) h
  rw [tensor_coe_eq_mul_kPos hDistrib, tensor_coe_eq_mul_kPos hDistrib] at hc
  exact mul_right_cancel₀ (ne_of_gt (kPos tensor t).2) hc

end TensorDerivation

namespace TensorRegularity

variable {tensor : PosReal → PosReal → PosReal}

/-- If `⊗` is distributive over `+` (Axiom 3) and is symmetric with `1` in the sense that
`1 ⊗ t = t ⊗ 1`, then the map `t ↦ 1 ⊗ t` is injective.

This is the minimal “commutativity-style” hypothesis needed to eliminate an explicit
`inj_kPos` assumption in `TensorRegularity`. -/
theorem inj_kPos_of_distrib_of_comm_one
    (hDistrib : DistributesOverAdd tensor)
    (hCommOne : ∀ t : PosReal, tensor onePos t = tensor t onePos) :
    Function.Injective (fun t : PosReal => tensor onePos t) := by
  intro t₁ t₂ ht
  have ht' : tensor t₁ onePos = tensor t₂ onePos := by
    calc
      tensor t₁ onePos = tensor onePos t₁ := by simpa using (hCommOne t₁).symm
      _ = tensor onePos t₂ := ht
      _ = tensor t₂ onePos := by simpa using (hCommOne t₂)
  have hinj_left : Function.Injective (fun x : PosReal => tensor x onePos) :=
    TensorDerivation.inj_left_of_distrib (tensor := tensor) hDistrib onePos
  exact hinj_left ht'

/-- Full commutativity implies the weaker symmetry hypothesis used in
`inj_kPos_of_distrib_of_comm_one`. -/
theorem inj_kPos_of_distrib_of_comm
    (hDistrib : DistributesOverAdd tensor)
    (hComm : ∀ u v : PosReal, tensor u v = tensor v u) :
    Function.Injective (fun t : PosReal => tensor onePos t) :=
  inj_kPos_of_distrib_of_comm_one (tensor := tensor) hDistrib (fun t => hComm onePos t)

/-- Build `TensorRegularity` from associativity (Axiom 4), distributivity (Axiom 3),
and symmetry with `1` (a commutativity-style “independence” hypothesis). -/
theorem of_assoc_of_distrib_of_comm_one
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hCommOne : ∀ t : PosReal, tensor onePos t = tensor t onePos) :
    TensorRegularity tensor :=
  ⟨hAssoc, inj_kPos_of_distrib_of_comm_one (tensor := tensor) hDistrib hCommOne⟩

/-- Build `TensorRegularity` from associativity (Axiom 4), distributivity (Axiom 3),
and full commutativity (a common “independence” hypothesis). -/
theorem of_assoc_of_distrib_of_comm
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hComm : ∀ u v : PosReal, tensor u v = tensor v u) :
    TensorRegularity tensor :=
  of_assoc_of_distrib_of_comm_one (tensor := tensor) hAssoc hDistrib (fun t => hComm onePos t)

end TensorRegularity

/-- Re-export: from tensor regularity and distributivity, `⊗` is multiplication up to a global
scale constant. This is the Lean-friendly Appendix B route that avoids “Appendix A again”. -/
theorem tensor_coe_eq_mul_div_const_of_tensorRegularity
    {tensor : PosReal → PosReal → PosReal}
    (hTensor : TensorRegularity tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  exact
    TensorDerivation.tensor_coe_eq_mul_div_const_of_tensorRegularity
      (tensor := tensor) hTensor hDistrib

/-- Convenience: an additive order-isomorphism representation implies `TensorRegularity`. -/
theorem tensorRegularity_of_additiveOrderIsoRep
    {tensor : PosReal → PosReal → PosReal}
    (hRep : AdditiveOrderIsoRep PosReal tensor) :
    TensorRegularity tensor :=
  TensorRegularity.of_additiveOrderIsoRep (tensor := tensor) hRep

/-- If `⊗` satisfies Axioms 3–4 and is symmetric with `1`, then `⊗` is scaled multiplication. -/
theorem tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm_one
    {tensor : PosReal → PosReal → PosReal}
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hCommOne : ∀ t : PosReal, tensor onePos t = tensor t onePos) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C :=
  tensor_coe_eq_mul_div_const_of_tensorRegularity
    (tensor := tensor)
    (TensorRegularity.of_assoc_of_distrib_of_comm_one
      (tensor := tensor) hAssoc hDistrib hCommOne)
    hDistrib

/-- If `⊗` satisfies Axioms 3–4 and is commutative, then `⊗` is scaled multiplication. -/
theorem tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm
    {tensor : PosReal → PosReal → PosReal}
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hComm : ∀ u v : PosReal, tensor u v = tensor v u) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C :=
  tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm_one
    (tensor := tensor) hAssoc hDistrib (fun t => hComm onePos t)

/-- If `⊗` is already given with an additive order-isomorphism representation
`Θ(x ⊗ y) = Θ x + Θ y`, then it satisfies `TensorRegularity`, so the Lean-friendly Appendix B
route applies without adding any extra axioms. -/
theorem tensor_coe_eq_mul_div_const_of_additiveOrderIsoRep
    {tensor : PosReal → PosReal → PosReal}
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  exact
    tensor_coe_eq_mul_div_const_of_tensorRegularity
      (tensor := tensor) (TensorRegularity.of_additiveOrderIsoRep (tensor := tensor) hRep) hDistrib

/-- Direct proof provides the `ScaledMultRep` interface.

This is the alternative path: uses `TensorRegularity` + `DistributesOverAdd` directly,
bypassing the need for `AdditiveOrderIsoRep` from Appendix A. -/
noncomputable def scaledMultRep_of_tensorRegularity
    {tensor : PosReal → PosReal → PosReal}
    (hTensor : TensorRegularity tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ScaledMultRep tensor :=
  ScaledMultRep.ofExists (tensor_coe_eq_mul_div_const_of_tensorRegularity hTensor hDistrib)

/-- Convenience: build `ScaledMultRep` from associativity, distributivity, and commutativity. -/
noncomputable def scaledMultRep_of_assoc_distrib_comm
    {tensor : PosReal → PosReal → PosReal}
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hComm : ∀ u v : PosReal, tensor u v = tensor v u) :
    ScaledMultRep tensor :=
  ScaledMultRep.ofExists (tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm hAssoc hDistrib hComm)

/-- Left projection shows why associativity and left distributivity need a regularity premise. -/
def leftProjectionTensor (x _ : PosReal) : PosReal := x

theorem leftProjection_boundary :
    TensorAssoc leftProjectionTensor ∧ DistributesOverAdd leftProjectionTensor ∧
      ¬TensorRegularity leftProjectionTensor := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, ?_⟩
  intro h
  have hc := h.inj_kPos (a₁ := (⟨1, by norm_num⟩ : PosReal))
    (a₂ := (⟨2, by norm_num⟩ : PosReal)) rfl
  have hv := congrArg (fun x : PosReal => (x : ℝ)) hc
  norm_num at hv

end KnuthSkilling.Multiplicative
