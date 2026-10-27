import KnuthSkilling.Core.Basic
import KnuthSkilling.Additive.Representation
import KnuthSkilling.Probability.BooleanRepresentation
import Mathlib.Data.NNReal.Basic

/-!
# Event models and their probability observations

An event model preserves disjoint joins in a supplied ordered scale.
An additive order embedding gives real weights; probability additionally needs
positive total weight. Calibration changes units without changing event answers.
Finite weighted events and the non-Boolean three-element chain are concrete models.
-/

namespace KnuthSkilling
open KnuthSkillingMonoidBase

/-- Monotone, bottom-preserving, disjoint-additive event weights. -/
structure KSModel (E S : Type*)
    [PlausibilitySpace E] [KnuthSkillingMonoidBase S] where
  v : E → S
  mono : Monotone v
  v_bot : v ⊥ = ident
  v_sup_of_disjoint : ∀ {a b : E}, Disjoint a b → v (a ⊔ b) = op (v a) (v b)

namespace KSModel
variable {E S : Type*} [PlausibilitySpace E] [KnuthSkillingMonoidBase S] (m : KSModel E S)

theorem v_ident_le (a : E) : ident ≤ m.v a := m.v_bot ▸ m.mono bot_le

theorem v_sup_bot (a : E) : m.v (a ⊔ ⊥) = m.v a := by rw [sup_bot_eq]
theorem v_bot_sup (a : E) : m.v (⊥ ⊔ a) = m.v a := by rw [bot_sup_eq]
theorem v_bot_sup' (a : E) : m.v (⊥ ⊔ a) = op ident (m.v a) := by
  rw [m.v_sup_of_disjoint disjoint_bot_left, m.v_bot]
theorem v_bot_sup_consistent (a : E) : op ident (m.v a) = m.v a := op_ident_left _
theorem op_assoc' (x y z : S) : op (op x y) z = op x (op y z) := op_assoc x y z

theorem v_sup_three {a b c : E}
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    m.v (a ⊔ b ⊔ c) = op (op (m.v a) (m.v b)) (m.v c) := by
  rw [m.v_sup_of_disjoint (hac.sup_left hbc), m.v_sup_of_disjoint hab]

theorem v_sup_three' {a b c : E}
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    m.v (a ⊔ b ⊔ c) = op (m.v a) (op (m.v b) (m.v c)) := by
  rw [m.v_sup_three hab hac hbc, op_assoc]
theorem v_le_of_le {a b : E} (h : a ≤ b) : m.v a ≤ m.v b := m.mono h
end KSModel

/-- The original event model and an explicitly supplied additive representation. -/
structure KSModelWithRepresentation (E S : Type*)
    [PlausibilitySpace E] [KnuthSkillingMonoidBase S] extends KSModel E S where
  Θ : S → ℝ
  Θ_orderEmb : ∀ x y : S, x ≤ y ↔ Θ x ≤ Θ y
  Θ_ident : Θ ident = 0
  Θ_hom : ∀ x y : S, Θ (op x y) = Θ x + Θ y

namespace KSModelWithRepresentation
variable {E S : Type*} [PlausibilitySpace E] [KnuthSkillingMonoidBase S]

def ofRepresentation (m : KSModel E S) (r : Additive.RepresentationResult S) :
    KSModelWithRepresentation E S :=
  { m with Θ := r.Θ, Θ_orderEmb := r.order_preserving,
           Θ_ident := r.ident_zero_of_ident, Θ_hom := r.additive }

def representation (m : KSModelWithRepresentation E S) : Additive.RepresentationResult S :=
  ⟨m.Θ, m.Θ_orderEmb, m.Θ_hom⟩

variable (m : KSModelWithRepresentation E S)
def v_ℝ : E → ℝ := m.Θ ∘ m.v

theorem v_ℝ_mono : Monotone m.v_ℝ := fun _ _ h => (m.Θ_orderEmb _ _).mp (m.mono h)
theorem v_ℝ_bot : m.v_ℝ ⊥ = 0 := by simp [v_ℝ, m.v_bot, m.Θ_ident]
theorem v_ℝ_sup_of_disjoint {a b : E} (h : Disjoint a b) :
    m.v_ℝ (a ⊔ b) = m.v_ℝ a + m.v_ℝ b := by
  simp only [v_ℝ, Function.comp_apply, m.v_sup_of_disjoint h, m.Θ_hom]
theorem v_ℝ_nonneg (a : E) : 0 ≤ m.v_ℝ a := by
  simpa [v_ℝ, m.Θ_ident] using (m.Θ_orderEmb _ _).mp (m.v_ident_le a)

/-- Normalization is an actual additive valuation only at positive total weight. -/
noncomputable def probability (h : 0 < m.v_ℝ ⊤) :
    ProbabilityTheory.Common.AdditiveValuation E where
  val a := m.v_ℝ a / m.v_ℝ ⊤
  mono _ _ hab := div_le_div_of_nonneg_right (m.v_ℝ_mono hab) h.le
  val_bot := by rw [m.v_ℝ_bot, zero_div]
  val_top := div_self (ne_of_gt h)
  additive a b hab := by rw [m.v_ℝ_sup_of_disjoint (disjoint_iff.mpr hab), add_div]

/-- Changing the representation route preserves normalized event answers. -/
theorem normalization_independent (m : KSModel E S) (r t : Additive.RepresentationResult S)
    (h : ident < m.v ⊤) (a : E) :
    r.Θ (m.v a) / r.Θ (m.v ⊤) = t.Θ (m.v a) / t.Θ (m.v ⊤) := by
  simpa only [Additive.RepresentationResult.calibrate_apply] using
    r.calibrate_agree t (m.v ⊤) ((isPositive_iff_ident_lt _).mpr h) (m.v a)
end KSModelWithRepresentation

namespace FiniteEvents
open Classical
open Probability.BooleanRepresentation
variable {ι : Type*} [Fintype ι]

/-- The event observation retains the supplied atomic weights. -/
noncomputable def weight (w : ι → ℝ) (s : Set ι) : ℝ := ∑ i, if i ∈ s then w i else 0

theorem weight_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (s : Set ι) :
    0 ≤ weight w s := Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all

theorem weight_mono (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) : Monotone (weight w) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : i ∈ a
  · simp [ha, hab ha]
  · simp only [if_neg ha]; split_ifs <;> simp_all

theorem weight_modular (w : ι → ℝ) (a b : Set ι) :
    weight w (a ∪ b) + weight w (a ∩ b) = weight w a + weight w b := by
  simp only [weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp [ha, hb]

@[simp] theorem weight_empty (w : ι → ℝ) : weight w ∅ = 0 := by simp [weight]
@[simp] theorem weight_univ (w : ι → ℝ) : weight w Set.univ = ∑ i, w i := by simp [weight]
@[simp] theorem weight_singleton (w : ι → ℝ) (i : ι) : weight w {i} = w i := by
  simp [weight]

theorem weight_scale (w : ι → ℝ) (c : ℝ) (s : Set ι) :
    weight (fun i => c * w i) s = c * weight w s := by
  simp only [weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

noncomputable def representation (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    KSBooleanRepresentation (Set ι) where
  Θ := weight w
  Θ_nonneg := weight_nonneg w hw
  Θ_mono := fun _ _ h => weight_mono w hw h
  Θ_bot := weight_empty w
  Θ_modular := weight_modular w

/-- Exact normalization of each supplied atomic weight. -/
theorem probability_singleton (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h : (∑ i, w i) ≠ 0) (i : ι) :
    (representation w hw).probability {i} = w i / ∑ j, w j := by
  simp [KSBooleanRepresentation.probability, representation, h]
end FiniteEvents

/-- Nonnegative addition supplies a concrete ordered scale. -/
noncomputable instance instKSAlgebraNNReal : KnuthSkillingAlgebraBase NNReal where
  toLinearOrder := inferInstance
  op := (· + ·)
  ident := 0
  op_assoc := add_assoc
  op_ident_right := add_zero
  op_ident_left := zero_add
  op_strictMono_left := fun y => fun _ _ h => add_lt_add_left h y
  op_strictMono_right := fun x => fun _ _ h => add_lt_add_right h x
  ident_le := fun _ => zero_le

theorem nnreal_op_is_add :
    @op NNReal instKSAlgebraNNReal.toKnuthSkillingMonoidBase.toKSSemigroupBase = (· + ·) := rfl
theorem nnreal_ident_is_zero : @ident NNReal instKSAlgebraNNReal.toKnuthSkillingMonoidBase = 0 := rfl

/-- A finite non-Boolean event model with an interior truth value. -/
inductive Three' : Type where
  | bot : Three'
  | mid : Three'
  | top : Three'
  deriving DecidableEq

namespace Three'

def toNat : Three' → ℕ
  | bot => 0
  | mid => 1
  | top => 2

instance : LinearOrder Three' where
  le := fun a b => a.toNat ≤ b.toNat
  lt := fun a b => a.toNat < b.toNat
  le_refl := fun _ => Nat.le_refl _
  le_trans := fun _ _ _ => Nat.le_trans
  le_antisymm := fun a b hab hba => by
    cases a <;> cases b <;> simp_all [toNat]
  le_total := fun a b => Nat.le_total _ _
  lt_iff_le_not_ge := fun _ _ => Nat.lt_iff_le_and_not_ge
  toDecidableEq := inferInstance
  toDecidableLE := fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
  toDecidableLT := fun a b => inferInstanceAs (Decidable (a.toNat < b.toNat))
  max := fun a b => if a.toNat ≤ b.toNat then b else a
  min := fun a b => if a.toNat ≤ b.toNat then a else b

instance : Lattice Three' where
  sup := max
  inf := min
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  sup_le := fun _ _ _ hac hbc => max_le hac hbc
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  le_inf := fun _ _ _ hab hac => le_min hab hac

instance : DistribLattice Three' where
  le_sup_inf := fun _ _ _ => le_sup_inf

instance : BoundedOrder Three' where
  top := top
  le_top := fun a => by cases a <;> decide
  bot := bot
  bot_le := fun a => by cases a <;> decide

instance : PlausibilitySpace Three' := inferInstance

/-- In Three', disjointness means at least one is bot -/
theorem disjoint_iff_has_bot (a b : Three') : Disjoint a b ↔ a = bot ∨ b = bot := by
  constructor
  · intro h
    rw [disjoint_iff] at h
    cases a <;> cases b <;> simp_all
  · intro h
    cases h with
    | inl ha => subst ha; exact disjoint_bot_left
    | inr hb => subst hb; exact disjoint_bot_right

/-- A KSModel on Three' with scale NNReal.
    v(bot) = 0, v(mid) = p, v(top) = 1 for a given p ∈ (0,1). -/
noncomputable def threeKSModel (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1) :
    KSModel Three' NNReal where
  v := fun a => match a with
    | bot => 0
    | mid => p
    | top => 1
  mono := fun a b hab => by
    cases a <;> cases b
    · exact le_rfl
    · exact hp0.le
    · exact zero_le
    · exfalso; exact (by decide : ¬mid ≤ bot) hab
    · exact le_rfl
    · exact hp1.le
    · exfalso; exact (by decide : ¬top ≤ bot) hab
    · exfalso; exact (by decide : ¬top ≤ mid) hab
    · exact le_rfl
  v_bot := nnreal_ident_is_zero.symm  -- v ⊥ = 0 = ident
  v_sup_of_disjoint := fun {a b} h => by
    rcases (disjoint_iff_has_bot a b).mp h with rfl | rfl
    · cases b <;> simp [nnreal_op_is_add, max_eq_right (show bot ≤ mid by decide),
        max_eq_right (show bot ≤ top by decide)]
    · cases a <;> simp [nnreal_op_is_add, max_eq_left (show bot ≤ mid by decide),
        max_eq_left (show bot ≤ top by decide)]

/-- Standard model with p = 1/2 -/
noncomputable def standardThreeKSModel : KSModel Three' NNReal :=
  threeKSModel (1/2 : NNReal) (by norm_num) (by norm_num)

/-- Verify the model satisfies the key K&S axiom -/
theorem threeKSModel_additive (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1)
    {a b : Three'} (h : Disjoint a b) :
    (threeKSModel p hp0 hp1).v (a ⊔ b) =
    @op NNReal instKSAlgebraNNReal.toKnuthSkillingMonoidBase.toKSSemigroupBase
      ((threeKSModel p hp0 hp1).v a) ((threeKSModel p hp0 hp1).v b) :=
  (threeKSModel p hp0 hp1).v_sup_of_disjoint h

/-- Three' is not Boolean -/
theorem not_boolean : ¬∃ (compl : Three' → Three'),
    (∀ a, a ⊔ compl a = ⊤) ∧ (∀ a, a ⊓ compl a = ⊥) := by
  rintro ⟨c, hs, hi⟩
  have hs := hs mid
  have hi := hi mid
  cases hc : c mid <;> simp_all

/-- Summary: Three' is a K&S compatible non-Boolean lattice -/
theorem three_is_ks_compatible :
    Nonempty (PlausibilitySpace Three') ∧
    Nonempty (KSModel Three' NNReal) ∧
    ¬∃ (compl : Three' → Three'), (∀ a, a ⊔ compl a = ⊤) ∧ (∀ a, a ⊓ compl a = ⊥) :=
  ⟨⟨inferInstance⟩, ⟨standardThreeKSModel⟩, not_boolean⟩

end Three'

end KnuthSkilling
