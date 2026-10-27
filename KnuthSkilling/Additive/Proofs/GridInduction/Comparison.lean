import KnuthSkilling.Additive.Main
import KnuthSkilling.Additive.Proofs.GridInduction.Main

/-!
# Comparing supplied representations and their construction routes

A supplied additive order embedding determines iteration, separation and calibrated
observations. These laws do not require selecting a construction route. The existence
interfaces below separately identify which provider supplies such an embedding.

The no-anomalous-pairs equivalence is identity-free. An identity maps to zero;
a positive anchor fixes the unit through shared calibration. Constructing a global
identity-free Grid provider is a separate problem. Local grid realizations consume
explicit representation data.
-/

namespace KnuthSkilling.Additive.Proofs.GridInduction.Comparison
open Classical KnuthSkillingMonoidBase KnuthSkillingAlgebraBase KnuthSkillingAlgebra
open KnuthSkilling.Additive.Axioms.AnomalousPairs
open KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

instance grid_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [RepresentationGlobalizationSemigroup α] :
    HasRepresentationTheorem α where
  exists_representation := RepresentationGlobalizationSemigroup.exists_Theta

instance representationGlobalizationSemigroup_of_noAnomalousPairs
    (α : Type*) [KSSemigroupBase α] [NoAnomalousPairs α] :
    RepresentationGlobalizationSemigroup α where
  exists_Theta := representation_semigroup

instance representationGlobalization_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α] :
    RepresentationGlobalization α where
  exists_Theta := representation_from_noAnomalousPairs

/-- A faithful supplied readout derives commutativity. -/
theorem op_comm_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∀ x y : α, op x y = op y x := by
  obtain ⟨Θ, ho, ha⟩ := HasRepresentationTheorem.exists_representation (α := α)
  exact (RepresentationResult.mk Θ ho ha).op_comm

theorem noAnomalousPairs_of_KSSeparation_IdentIsMinimum
    (α : Type*) [KnuthSkillingMonoidBase α] [KSSeparation α] [IdentIsMinimum α] :
    NoAnomalousPairs α := KSSeparation.noAnomalousPairs_of_KSSeparation_with_IdentMin

lemma theta_iterate_op_pnat_eq_nsmul
    (α : Type*) [KSSemigroupBase α]
    (Θ : α → ℝ) (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y)
    (a : α) (n : ℕ+) : Θ (iterate_op_pnat a n) = (n : ℝ) * Θ a := by
  induction n using PNat.recOn with
  | one => simp [iterate_op_pnat_one]
  | succ n ih => simp [iterate_op_pnat_succ, hΘ_add, ih, add_mul, add_comm]

lemma theta_iterate_op_eq_nsmul
    (α : Type*) [KnuthSkillingMonoidBase α]
    (Θ : α → ℝ) (hΘ_ident : Θ ident = 0) (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y)
    (a : α) (n : ℕ) : Θ (iterate_op a n) = n * Θ a := by
  induction n with
  | zero => simp [iterate_op, hΘ_ident]
  | succ n ih => simp [iterate_op_succ, hΘ_add, ih, Nat.cast_succ, add_mul, add_comm]

/-- An anomalous pair would bound a positive readout gap at every positive-natural stage. -/
theorem noAnomalousPairs_of_representation
    (α : Type*) [KSSemigroupBase α]
    (Θ : α → ℝ) (hΘ_order : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b)
    (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y) : NoAnomalousPairs α := by
  let r : RepresentationResult α := ⟨Θ, hΘ_order, hΘ_add⟩
  refine ⟨fun a b h => ?_⟩
  have step (n : ℕ+) := h n
  have numeric (n : ℕ+) :
      ((n : ℝ) * Θ a < n * Θ b ∧ n * Θ b < ((n : ℝ) + 1) * Θ a) ∨
      ((n : ℝ) * Θ b < n * Θ a ∧ ((n : ℝ) + 1) * Θ a < n * Θ b) := by
    simpa only [r.strict_order_preserving, r, theta_iterate_op_pnat_eq_nsmul α Θ hΘ_add,
      PNat.add_coe, Nat.cast_add, Nat.cast_one, PNat.val_ofNat] using step n
  have hne : Θ b - Θ a ≠ 0 := by
    rcases numeric 1 with h | h <;> norm_num at h <;> linarith
  have bound (n : ℕ+) : (n : ℝ) * |Θ b - Θ a| < |Θ a| := by
    have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
    rcases numeric n with h | h
    · have hp : 0 < Θ b - Θ a := by nlinarith only [h.1, hn]
      rw [abs_of_pos hp]
      nlinarith only [h.2, le_abs_self (Θ a)]
    · have hp : Θ b - Θ a < 0 := by nlinarith only [h.1, hn]
      rw [abs_of_neg hp]
      nlinarith only [h.2, neg_le_abs (Θ a)]
  obtain ⟨N, hN⟩ := exists_nat_gt (|Θ a| / |Θ b - Θ a|)
  have hp := abs_pos.mpr hne
  have hNp : 0 < N := by
    have := div_nonneg (abs_nonneg (Θ a)) hp.le
    by_contra hh
    have : N = 0 := by omega
    simp [this] at hN
    linarith
  have hn := bound ⟨N, hNp⟩
  have ht := (div_lt_iff₀ hp).mp hN
  change (N : ℝ) * |Θ b - Θ a| < |Θ a| at hn
  linarith

/-- Existence uses the declared provider; the converse uses the supplied readout alone. -/
theorem noAnomalousPairs_iff_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] :
    NoAnomalousPairs α ↔ HasRepresentationTheorem α := by
  constructor
  · intro h; exact @holder_hasRepresentationTheorem α _ h
  · intro h
    obtain ⟨Θ, ho, ha⟩ := h.exists_representation
    exact noAnomalousPairs_of_representation α Θ ho ha

/-- Reversing the order retains the operation and identity, without asserting a minimum identity. -/
@[instance_reducible] private def dualProfile (α : Type*) [KnuthSkillingMonoidBase α] :
    KnuthSkillingMonoidBase αᵒᵈ where
  toLinearOrder := OrderDual.instLinearOrder α
  op x y := OrderDual.toDual (op (α := α) (OrderDual.ofDual x) (OrderDual.ofDual y))
  op_assoc := @KSSemigroupBase.op_assoc α _
  op_strictMono_left y _a _b h := op_strictMono_left (α := α) y h
  op_strictMono_right x _a _b h := op_strictMono_right (α := α) x h
  ident := ident (α := α)
  op_ident_left := @KnuthSkillingMonoidBase.op_ident_left α _
  op_ident_right := @KnuthSkillingMonoidBase.op_ident_right α _

private def dualReadout {α : Type*} [KnuthSkillingMonoidBase α] (r : RepresentationResult α) :
    letI := dualProfile α; RepresentationResult αᵒᵈ := by
  let := dualProfile α
  refine ⟨fun x => -r.Θ (OrderDual.ofDual x), ?_, ?_⟩
  · intro x y
    change (@LE.le α _ (OrderDual.ofDual y) (OrderDual.ofDual x)) ↔
      -r.Θ (OrderDual.ofDual x) ≤ -r.Θ (OrderDual.ofDual y)
    rw [neg_le_neg_iff]
    exact r.order_preserving (OrderDual.ofDual y) (OrderDual.ofDual x)
  · intro x y
    change -r.Θ (op (α := α) (OrderDual.ofDual x) (OrderDual.ofDual y)) =
      -r.Θ (OrderDual.ofDual x) + -r.Θ (OrderDual.ofDual y)
    rw [r.additive, neg_add]

private theorem negativeSeparation {α : Type*} [KnuthSkillingMonoidBase α]
    (r : RepresentationResult α) {a x y : α}
    (ha : a < ident) (hx : x < ident) (hy : y < ident) (hxy : x < y) :
    ∃ n m : ℕ+, iterate_op_pnat x m < iterate_op_pnat a n ∧
      iterate_op_pnat a n < iterate_op_pnat y m := by
  let := dualProfile α
  let t := dualReadout r
  have pos z (hz : @LT.lt α _ z ident) : IsPositive (OrderDual.toDual z) := by
    apply (t.isPositive_iff (OrderDual.toDual z)).mpr
    change 0 < -r.Θ z
    have hh := (r.strict_order_preserving z ident).mp hz
    rw [r.ident_zero_of_ident] at hh
    linarith
  have hxyD : OrderDual.toDual y < OrderDual.toDual x := hxy
  obtain ⟨n, m, hlo, hhi⟩ := t.separationSemigroupStrict.separation_strict
    (pos a ha) (pos y hy) (pos x hx) hxyD
  refine ⟨n, m, (r.strict_order_preserving _ _).mpr ?_, (r.strict_order_preserving _ _).mpr ?_⟩
  all_goals rw [r.map_iterate_pnat, r.map_iterate_pnat]
  · have hh := (t.strict_order_preserving _ _).mp hhi
    rw [t.map_iterate_pnat, t.map_iterate_pnat] at hh
    change (n : ℝ) * (-r.Θ a) < (m : ℝ) * (-r.Θ x) at hh
    nlinarith only [hh]
  · have hh := (t.strict_order_preserving _ _).mp hlo
    rw [t.map_iterate_pnat, t.map_iterate_pnat] at hh
    change (m : ℝ) * (-r.Θ y) < (n : ℝ) * (-r.Θ a) at hh
    nlinarith only [hh]

theorem ksSeparation_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α]
    {a x y : α} (ha : ident < a) (hx : ident < x) (hy : ident < y) (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  obtain ⟨Θ, ho, _, hadd⟩ := representation_from_noAnomalousPairs (α := α)
  let r : RepresentationResult α := ⟨Θ, ho, hadd⟩
  let := r.separationSemigroupStrict
  exact (KSSeparation_of_KSSeparationSemigroup (α := α)).separation ha hx hy hxy

theorem ksSeparation_neg_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α]
    {a x y : α} (ha : a < ident) (hx : x < ident) (hy : y < ident) (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  obtain ⟨Θ, ho, _, hadd⟩ := representation_from_noAnomalousPairs (α := α)
  obtain ⟨n, m, hlo, hhi⟩ := negativeSeparation (RepresentationResult.mk Θ ho hadd) ha hx hy hxy
  exact ⟨n, m, m.pos, by simpa only [iterate_op_pnat_eq] using hlo,
    by simpa only [iterate_op_pnat_eq] using hhi.le⟩

theorem separationBilateralProp_of_noAnomalousPairs
    (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α] :
    SeparationBilateralProp (α := α) := by
  obtain ⟨Θ, ho, _, hadd⟩ := representation_from_noAnomalousPairs (α := α)
  let r : RepresentationResult α := ⟨Θ, ho, hadd⟩
  refine ⟨r.separationSemigroupStrict.separation, ?_⟩
  intro a x y ha hx hy hxy
  obtain ⟨n, m, hlo, hhi⟩ := negativeSeparation r
    ((isNegative_iff_lt_ident (a := a)).mp ha) ((isNegative_iff_lt_ident (a := x)).mp hx)
    ((isNegative_iff_lt_ident (a := y)).mp hy) hxy
  exact ⟨n, m, hlo, hhi.le⟩

/-- A supplied representation realizes the raw extension on actual grid states. -/
theorem realizesThetaRaw_of_representation {α : Type*} [KnuthSkillingAlgebraBase α]
    [KSSeparation α] {k : ℕ} (F : AtomFamily α k) (r : RepresentationResult α)
    (d : α) (hd : ident < d) :
    RealizesThetaRaw (MultiGridRep.ofRepresentation F r) d hd (r.Θ d) := by
  refine ⟨fun p => r.Θ p.val, fun _ _ h => (r.strict_order_preserving _ _).mp h, ?_⟩
  intro v t
  change r.Θ (mu (extendAtomFamily F d hd) (joinMulti v t)) = r.Θ (mu F v) + (t : ℝ) * r.Θ d
  rw [mu_extend_last, r.additive, r.map_iterate]

/-- Calibrated supplied representations have the same observations on every grid state. -/
theorem calibrated_grid_readouts_agree {α : Type*} [KnuthSkillingAlgebraBase α]
    [KSSeparation α] {k : ℕ} (F : AtomFamily α k) (r t : RepresentationResult α)
    (a : α) (ha : IsPositive a) (p : {x // x ∈ kGrid F}) :
    (MultiGridRep.ofRepresentation F (r.calibrate a ha)).Θ_grid p =
      (MultiGridRep.ofRepresentation F (t.calibrate a ha)).Θ_grid p :=
  r.calibrate_agree t a ha p.val

end KnuthSkilling.Additive.Proofs.GridInduction.Comparison
