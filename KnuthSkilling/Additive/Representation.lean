import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.Algebra

namespace KnuthSkilling.Additive

open Classical
open KSSemigroupBase
open KnuthSkillingMonoidBase

/-!
# Representation Interfaces (Identity-Free by Default)

An additive order embedding records both the supplied readout and its preservation laws.
The default carrier is identity-free. An existing identity necessarily maps to zero;
a positive reference instead fixes multiplicative scale by mapping to one.
Finite folds describe accumulated states, not the ordered histories that produced them.
-/

/-- **Representation result** (identity-free version).
    Captures the minimal structure: order embedding + additive homomorphism. -/
structure RepresentationResult (α : Type*) [KSSemigroupBase α] where
  /-- The representation function Θ : α → ℝ -/
  Θ : α → ℝ
  /-- Order-preserving: a ≤ b ↔ Θ a ≤ Θ b -/
  order_preserving : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b
  /-- Additive homomorphism: Θ(x ⊕ y) = Θ x + Θ y -/
  additive : ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- **Normalized representation result** (with identity).
    Extends `RepresentationResult` with canonical normalization Θ(ident) = 0. -/
structure NormalizedRepresentationResult (α : Type*) [KnuthSkillingMonoidBase α]
    extends RepresentationResult α where
  /-- Canonical normalization: Θ(ident) = 0 -/
  ident_zero : Θ ident = 0

/-! ### Basic Lemmas -/

/-- The actual supplied map, bundled as an order embedding. -/
def RepresentationResult.toOrderEmbedding {α : Type*} [KSSemigroupBase α]
    (r : RepresentationResult α) : α ↪o ℝ :=
  OrderEmbedding.ofMapLEIff r.Θ (fun _ _ => (r.order_preserving _ _).symm)

/-- Strict order-preserving: a < b ↔ Θ a < Θ b. -/
theorem RepresentationResult.strict_order_preserving {α : Type*} [KSSemigroupBase α]
    (r : RepresentationResult α) : ∀ a b : α, a < b ↔ r.Θ a < r.Θ b :=
  fun _ _ => r.toOrderEmbedding.lt_iff_lt.symm

/-- Representation is injective (order embedding). -/
theorem RepresentationResult.injective {α : Type*} [KSSemigroupBase α]
    (r : RepresentationResult α) : Function.Injective r.Θ := r.toOrderEmbedding.injective

/-- Additivity + identity forces Θ(ident) = 0. -/
theorem RepresentationResult.ident_zero_of_ident {α : Type*} [KnuthSkillingMonoidBase α]
    (r : RepresentationResult α) : r.Θ ident = 0 := by
  have h := r.additive ident ident
  have h' : r.Θ ident = r.Θ ident + r.Θ ident := by
    simpa [op_ident_left] using h
  linarith

/-- Convert a representation into a normalized representation when identity exists. -/
def RepresentationResult.toNormalized {α : Type*} [KnuthSkillingMonoidBase α]
    (r : RepresentationResult α) : NormalizedRepresentationResult α :=
  { r with ident_zero := r.ident_zero_of_ident }

/-- Positive rationals admit positive-natural numerator and denominator witnesses. -/
theorem positive_rat_fraction (q : ℚ) (hq : 0 < q) : ∃ m n : ℕ+, q = (m : ℚ) / n := by
  refine ⟨⟨q.num.toNat, by have := Rat.num_pos.mpr hq; omega⟩, ⟨q.den, q.den_pos⟩, ?_⟩
  have hnum : (q.num.toNat : ℚ) = q.num := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt (Rat.num_pos.mpr hq))
  simpa only [PNat.mk_coe, hnum] using q.num_div_den.symm

namespace RepresentationResult

variable {α : Type*} [KSSemigroupBase α]

/-- Faithful interpretation derives commutativity rather than assuming it. -/
theorem op_comm (r : RepresentationResult α) (x y : α) : op x y = op y x :=
  r.injective (by rw [r.additive, r.additive, add_comm])

theorem map_iterate_pnat (r : RepresentationResult α) (x : α) (n : ℕ+) :
    r.Θ (iterate_op_pnat x n) = (n : ℝ) * r.Θ x := by
  induction n using PNat.recOn with
  | one => simp [iterate_op_pnat_one]
  | succ n ih => simp [iterate_op_pnat_succ, r.additive, ih, add_mul, add_comm]

/-- A seeded fold needs no identity; each event occurrence contributes once. -/
theorem map_foldl (r : RepresentationResult α) (s : α) (xs : List α) :
    r.Θ (xs.foldl op s) = r.Θ s + (xs.map r.Θ).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, r.additive, List.map_cons,
      List.sum_cons]; ring

theorem isPositive_iff (r : RepresentationResult α) (a : α) :
    IsPositive a ↔ 0 < r.Θ a := by
  constructor
  · intro h
    have hh := (r.strict_order_preserving a (op a a)).mp (h a)
    rw [r.additive] at hh
    linarith
  · intro h z
    apply (r.strict_order_preserving _ _).mpr
    rw [r.additive]
    linarith

/-- A positive element cannot be a zero of a faithful additive readout. -/
theorem positive_anchor_ne_zero (r : RepresentationResult α) (a : α) (ha : IsPositive a) :
    r.Θ a ≠ 0 := ne_of_gt ((r.isPositive_iff a).mp ha)

/-- Translation is not a freedom of additive representations, even without identity. -/
theorem shift_additive_iff (r : RepresentationResult α) (a : α) (c : ℝ) :
    (∀ x y, r.Θ (op x y) + c = (r.Θ x + c) + (r.Θ y + c)) ↔ c = 0 := by
  constructor
  · intro h
    have hh := h a a
    rw [r.additive] at hh
    linarith
  · rintro rfl
    simp [r.additive]

/-- Positive changes of unit preserve both order and addition. -/
def positiveScale (r : RepresentationResult α) (c : ℝ) (hc : 0 < c) :
    RepresentationResult α where
  Θ x := c * r.Θ x
  order_preserving x y := (r.order_preserving x y).trans (mul_le_mul_iff_right₀ hc).symm
  additive x y := by rw [r.additive, mul_add]

/-- Normalize a positive anchor to one, without assuming an identity. -/
noncomputable def calibrate (r : RepresentationResult α) (a : α) (ha : IsPositive a) :
    RepresentationResult α :=
  r.positiveScale (r.Θ a)⁻¹ (inv_pos.mpr ((r.isPositive_iff a).mp ha))

theorem calibrate_apply (r : RepresentationResult α) (a : α) (ha : IsPositive a) (x : α) :
    (r.calibrate a ha).Θ x = r.Θ x / r.Θ a := by
  simp [calibrate, positiveScale, div_eq_mul_inv, mul_comm]

@[simp] theorem calibrate_anchor (r : RepresentationResult α) (a : α) (ha : IsPositive a) :
    (r.calibrate a ha).Θ a = 1 := by
  rw [calibrate_apply, div_self (r.positive_anchor_ne_zero a ha)]

/-- Unit calibration adds no existence assumption to a supplied representation. -/
theorem exists_unit_calibrated_iff (a : α) (ha : IsPositive a) :
    (∃ r : RepresentationResult α, r.Θ a = 1) ↔ Nonempty (RepresentationResult α) := by
  constructor
  · rintro ⟨r, _⟩; exact ⟨r⟩
  · rintro ⟨r⟩; exact ⟨r.calibrate a ha, r.calibrate_anchor a ha⟩

/-- Rational comparisons of normalized positive values are intrinsic power comparisons. -/
private theorem ratio_lt_fraction (r : RepresentationResult α) (a x : α)
    (ha : IsPositive a) (m n : ℕ+) :
    r.Θ x / r.Θ a < (m : ℝ) / n ↔ iterate_op_pnat x n < iterate_op_pnat a m := by
  rw [r.strict_order_preserving, r.map_iterate_pnat, r.map_iterate_pnat]
  rw [div_lt_div_iff₀ ((r.isPositive_iff a).mp ha) (by exact_mod_cast n.pos)]
  simp only [mul_comm]

/-- Any two supplied representations agree up to a positive unit change.
The anchor and the power comparisons suffice; neither identity nor a separation axiom is needed. -/
theorem unique_up_to_posScale (r t : RepresentationResult α) (a : α) (ha : IsPositive a) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, t.Θ x = c * r.Θ x := by
  have hr := (r.isPositive_iff a).mp ha
  have ht := (t.isPositive_iff a).mp ha
  have ratios : ∀ x, IsPositive x → r.Θ x / r.Θ a = t.Θ x / t.Θ a := by
    intro x hx
    apply eq_of_forall_lt_rat_iff_lt
    intro q
    by_cases hq : 0 < q
    · obtain ⟨m, n, eq⟩ := positive_rat_fraction q hq
      have hcast : (q : ℝ) = (m : ℝ) / n := by
        simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun z : ℚ => (z : ℝ)) eq
      rw [hcast]
      exact (r.ratio_lt_fraction a x ha m n).trans (t.ratio_lt_fraction a x ha m n).symm
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast le_of_not_gt hq
      have h1 := div_pos ((r.isPositive_iff x).mp hx) hr
      have h2 := div_pos ((t.isPositive_iff x).mp hx) ht
      constructor <;> intro h <;> linarith
  refine ⟨t.Θ a / r.Θ a, div_pos ht hr, fun x => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (-r.Θ x / r.Θ a))
  have hNp : 0 < N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  let n : ℕ+ := ⟨N, hNp⟩
  have hx : IsPositive (op x (iterate_op_pnat a n)) := by
    apply (r.isPositive_iff _).mpr
    rw [r.additive, r.map_iterate_pnat]
    have hbound := (div_lt_iff₀ hr).mp (lt_of_le_of_lt (le_max_right _ _) hN)
    change 0 < r.Θ x + (N : ℝ) * r.Θ a
    linarith
  have hh := ratios _ hx
  rw [r.additive, t.additive, r.map_iterate_pnat, t.map_iterate_pnat] at hh
  have heq : r.Θ x / r.Θ a = t.Θ x / t.Θ a := by
    simpa [add_div, ne_of_gt hr, ne_of_gt ht] using hh
  have hcross := (div_eq_div_iff (ne_of_gt hr) (ne_of_gt ht)).mp heq
  field_simp
  nlinarith

/-- The calibrated observations agree, regardless of their construction route. -/
theorem calibrate_agree (r t : RepresentationResult α) (a : α) (ha : IsPositive a) (x : α) :
    (r.calibrate a ha).Θ x = (t.calibrate a ha).Θ x := by
  obtain ⟨c, hc, h⟩ := r.unique_up_to_posScale t a ha
  simp only [calibrate_apply, h x, h a]
  exact (mul_div_mul_left _ _ (ne_of_gt hc)).symm

/-- A faithful additive real readout supplies strict separation on the positive cone.
This is a property of the explicit readout, not a surjectivity assumption. -/
theorem separationSemigroupStrict (r : RepresentationResult α) : KSSeparationSemigroupStrict α := by
  have hs : SeparationSemigroupStrictProp (α := α) := by
    intro a x y ha hx _hy hxy
    have ha' := (r.isPositive_iff a).mp ha
    have hx' := (r.isPositive_iff x).mp hx
    obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn
      ((div_lt_div_iff_of_pos_right ha').mpr ((r.strict_order_preserving x y).mp hxy))
    have hq : 0 < q := by exact_mod_cast lt_trans (div_pos hx' ha') hlo
    obtain ⟨n, m, eq⟩ := positive_rat_fraction q hq
    have hcast : (q : ℝ) = (n : ℝ) / m := by simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun z : ℚ => (z : ℝ)) eq
    rw [hcast] at hlo hhi
    have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
    refine ⟨n, m, (r.strict_order_preserving _ _).mpr ?_, (r.strict_order_preserving _ _).mpr ?_⟩
    · rw [r.map_iterate_pnat, r.map_iterate_pnat]
      simpa only [mul_comm] using (div_lt_div_iff₀ ha' hm).mp hlo
    · rw [r.map_iterate_pnat, r.map_iterate_pnat]
      simpa only [mul_comm] using (div_lt_div_iff₀ hm ha').mp hhi
  exact {
    separation_strict := hs
    separation := by
      intro a x y ha hx hy hxy
      obtain ⟨n, m, hlo, hhi⟩ := hs ha hx hy hxy
      exact ⟨n, m, hlo, hhi.le⟩ }

end RepresentationResult

/-- A positive anchor cannot map to zero under any faithful additive readout.
No identity or separation premise is needed. -/
theorem zero_anchor_globalization_impossible {α : Type*} [KSSemigroupBase α]
    (a : α) (ha : IsPositive a) :
    ¬ ∃ r : RepresentationResult α, r.Θ a = 0 := by
  rintro ⟨r, zero⟩
  exact r.positive_anchor_ne_zero a ha zero

/-- A positive-only semigroup cannot at the same time contain an identity.
In particular, positive-only cuts interfaces must not inherit a monoid instance. -/
theorem all_positive_monoid_impossible {α : Type*} [KnuthSkillingMonoidBase α] :
    ¬ (∀ x : α, IsPositive x) := by
  intro h
  exact (lt_irrefl ident) ((isPositive_iff_ident_lt ident).mp (h ident))

theorem RepresentationResult.map_iterate {α : Type*} [KnuthSkillingMonoidBase α]
    (r : RepresentationResult α) (x : α) (n : ℕ) :
    r.Θ (KnuthSkillingAlgebra.iterate_op x n) = (n : ℝ) * r.Θ x := by
  induction n with
  | zero => simp [KnuthSkillingAlgebra.iterate_op_zero, r.ident_zero_of_ident]
  | succ n ih => simp [KnuthSkillingAlgebra.iterate_op_succ, r.additive, ih,
      Nat.cast_succ, add_mul, add_comm]

/-! ### Public Typeclass Interfaces -/

/-- **Identity-free representation theorem** (default).
    Exposes existence of an order-preserving additive representation. -/
class HasRepresentationTheorem (α : Type*) [KSSemigroupBase α] : Prop where
  exists_representation :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- **Normalized representation theorem** (identity-based convenience).
    Exposes existence of an order-preserving additive representation with Θ(ident) = 0. -/
class HasNormalizedRepresentation (α : Type*) [KnuthSkillingMonoidBase α] : Prop where
  exists_representation :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-! ### Convenience Lemmas / Instances -/

/-- Extract a representation from the identity-free interface. -/
theorem exists_Theta_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  simpa using (HasRepresentationTheorem.exists_representation (α := α))

/-- Extract a normalized representation from the identity-based interface. -/
theorem exists_Theta_of_hasNormalizedRepresentation
    (α : Type*) [KnuthSkillingMonoidBase α] [HasNormalizedRepresentation α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  simpa using (HasNormalizedRepresentation.exists_representation (α := α))

/-- Forget normalization: a normalized representation is a representation. -/
instance hasRepresentation_of_hasNormalized
    (α : Type*) [KnuthSkillingMonoidBase α] [HasNormalizedRepresentation α] :
    HasRepresentationTheorem α where
  exists_representation := by
    obtain ⟨Θ, hΘ_order, _hΘ_ident, hΘ_add⟩ :=
      HasNormalizedRepresentation.exists_representation (α := α)
    exact ⟨Θ, hΘ_order, hΘ_add⟩

/-- Identity makes every representation automatically normalized. -/
instance hasNormalized_of_hasRepresentation
    (α : Type*) [KnuthSkillingMonoidBase α] [HasRepresentationTheorem α] :
    HasNormalizedRepresentation α where
  exists_representation := by
    classical
    obtain ⟨Θ, hΘ_order, hΘ_add⟩ :=
      HasRepresentationTheorem.exists_representation (α := α)
    exact ⟨Θ, hΘ_order, (RepresentationResult.mk Θ hΘ_order hΘ_add).ident_zero_of_ident, hΘ_add⟩

end KnuthSkilling.Additive
