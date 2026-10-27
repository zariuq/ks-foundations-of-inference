import KnuthSkilling.Multiplicative.Basic

/-!
# Scaled multiplication and its faithful observations

A fixed tensor determines its scale uniquely. Dividing by that scale is a
faithful multiplicative observation, including finite left folds. This compares
interpretations of the same supplied operation; it does not identify all Cox
regraduations or replace their independent calibration premises.
-/

namespace KnuthSkilling.Multiplicative

open KnuthSkilling.Literature

/-- **ScaledMultRep**: The tensor operation has a scaled multiplication representation.

This is the OUTPUT of K&S Appendix B: the tensor ⊗ on positive reals equals
multiplication up to a global scale constant C > 0.

Multiple proof paths provide this interface:
- K&S path: AdditiveOrderIsoRep + Distributivity → ScaledMultRep
- Direct path: TensorRegularity + Distributivity → ScaledMultRep
-/
structure ScaledMultRep (tensor : PosReal → PosReal → PosReal) where
  /-- The scale constant C > 0 -/
  C : ℝ
  /-- C is positive -/
  C_pos : 0 < C
  /-- The tensor equals scaled multiplication: x ⊗ y = (x * y) / C -/
  tensor_eq : ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C

namespace ScaledMultRep

variable {tensor : PosReal → PosReal → PosReal}

/-- C is nonzero -/
theorem C_ne_zero (h : ScaledMultRep tensor) : h.C ≠ 0 := ne_of_gt h.C_pos

/-- Tensor expressed in terms of C -/
theorem tensor_eq' (h : ScaledMultRep tensor) (x y : PosReal) :
    ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / h.C :=
  h.tensor_eq x y

/-- After normalizing by C, tensor becomes actual multiplication.

This corresponds to K&S's "set C = 1 without loss of generality". -/
theorem tensor_normalized (h : ScaledMultRep tensor) (x y : PosReal) :
    ((tensor x y : PosReal) : ℝ) / h.C = (((x : ℝ) / h.C) * ((y : ℝ) / h.C)) := by
  have hC := h.C_ne_zero
  rw [h.tensor_eq]
  field_simp

/-- Tensor is commutative (follows from multiplication being commutative) -/
theorem tensor_comm (h : ScaledMultRep tensor) (x y : PosReal) :
    tensor x y = tensor y x := by
  apply Subtype.ext
  simp only [h.tensor_eq]
  ring

/-- Tensor is associative (follows from multiplication being associative) -/
theorem tensor_assoc (h : ScaledMultRep tensor) (x y z : PosReal) :
    tensor (tensor x y) z = tensor x (tensor y z) := by
  apply Subtype.ext
  have hC := h.C_ne_zero
  have hC_pos := h.C_pos
  simp only [h.tensor_eq]
  have hxy_pos : 0 < (x : ℝ) * (y : ℝ) := mul_pos x.2 y.2
  have hyz_pos : 0 < (y : ℝ) * (z : ℝ) := mul_pos y.2 z.2
  field_simp

/-- The observed tensor at one determines the scale, independently of proof route. -/
theorem C_unique (h₁ h₂ : ScaledMultRep tensor) : h₁.C = h₂.C := by
  let u : PosReal := ⟨1, by norm_num⟩
  have h := (h₁.tensor_eq u u).symm.trans (h₂.tensor_eq u u)
  have hi : h₁.C⁻¹ = h₂.C⁻¹ := by simpa only [u, one_mul, one_div] using h
  exact inv_inj.mp hi

/-- The derived tensor identity is the scale, not necessarily the real number one. -/
@[instance_reducible] def toMonoid (h : ScaledMultRep tensor) : Monoid PosReal where
  mul := tensor
  one := ⟨h.C, h.C_pos⟩
  mul_assoc := h.tensor_assoc
  one_mul x := by
    apply Subtype.ext
    change (tensor ⟨h.C, h.C_pos⟩ x : ℝ) = (x : ℝ)
    rw [h.tensor_eq]
    field_simp [h.C_ne_zero]
  mul_one x := by
    apply Subtype.ext
    change (tensor x ⟨h.C, h.C_pos⟩ : ℝ) = (x : ℝ)
    rw [h.tensor_eq]
    field_simp [h.C_ne_zero]

/-- A law-carrying observation of the original tensor into real multiplication. -/
noncomputable def normalizationHom (h : ScaledMultRep tensor) :
    let _ : Monoid PosReal := h.toMonoid
    PosReal →* ℝ := by
  let _ : Monoid PosReal := h.toMonoid
  exact { toFun x := (x : ℝ) / h.C
          map_one' := by change h.C / h.C = 1; exact div_self h.C_ne_zero
          map_mul' x y := h.tensor_normalized x y }

theorem normalization_injective (h : ScaledMultRep tensor) :
    Function.Injective h.normalizationHom := by
  intro x y hxy
  apply Subtype.ext
  change (x : ℝ) / h.C = (y : ℝ) / h.C at hxy
  exact (div_left_inj' h.C_ne_zero).mp hxy

/-- All occurrences of the authored fold are interpreted by the same observation. -/
theorem observe_fold (h : ScaledMultRep tensor) (s : PosReal) (xs : List PosReal) :
    ((xs.foldl tensor s : PosReal) : ℝ) / h.C =
      ((s : ℝ) / h.C) * (xs.map (fun (x : PosReal) => (x : ℝ) / h.C)).prod := by
  let _ : Monoid PosReal := h.toMonoid
  exact observe_foldl h.normalizationHom s xs

theorem normalization_independent (h₁ h₂ : ScaledMultRep tensor) (x : PosReal) :
    (x : ℝ) / h₁.C = (x : ℝ) / h₂.C := by rw [C_unique h₁ h₂]

end ScaledMultRep

/-- Build `ScaledMultRep` from an existence proof.

This is the bridge from theorem statements like `tensor_coe_eq_mul_div_const` to the interface. -/
noncomputable def ScaledMultRep.ofExists
    {tensor : PosReal → PosReal → PosReal}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C) :
    ScaledMultRep tensor :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

namespace ScaleExample
/-- A tensor whose identity and normalization scale are two. -/
noncomputable def tensor (x y : PosReal) : PosReal :=
  ⟨(x : ℝ) * (y : ℝ) / 2, by
    change (0 : ℝ) < (x : ℝ) * (y : ℝ) / 2
    exact div_pos (mul_pos x.2 y.2) (by norm_num)⟩

noncomputable def representation : ScaledMultRep tensor where
  C := 2
  C_pos := by norm_num
  tensor_eq _ _ := rfl

/-- Using the unscaled real readout violates the tensor observation law. -/
theorem wrong_scale_fails :
    (tensor ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ : ℝ) ≠ (2 : ℝ) * 2 := by
  norm_num [tensor]

/-- The correctly normalized fold uses the actual tensor and retains both inputs. -/
theorem normalized_fold :
    (([⟨2, by norm_num⟩, ⟨4, by norm_num⟩].foldl tensor ⟨2, by norm_num⟩ : PosReal) : ℝ) / 2 = 2 := by
  have h := representation.observe_fold ⟨2, by norm_num⟩ [⟨2, by norm_num⟩, ⟨4, by norm_num⟩]
  norm_num [representation] at h
  simpa only [List.foldl_cons, List.foldl_nil] using h
end ScaleExample

end KnuthSkilling.Multiplicative
