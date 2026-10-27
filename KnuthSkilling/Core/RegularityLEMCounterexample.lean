/-
# Regularity, excluded middle and valuation observations

Double-negation regularity need not give excluded middle, even on a finite
Heyting algebra. Dense-Top is equivalent to excluded middle for every element;
requiring excluded middle only for regular elements is weaker. The three-chain,
five-element lattice and real-open examples separate these conditions.

Complement gaps measure a valuation's observation. Reflecting their zero back
to a lattice identity requires an additional separation hypothesis.
-/

import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Regular
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import KnuthSkilling.Core.HeytingBounds

namespace KnuthSkilling.Heyting.RegularityLEMCounterexample

open TopologicalSpace Set

variable {α : Type*} [HeytingAlgebra α]

/-- An element is "dense" if its Heyting complement is bottom -/
def IsDense (a : α) : Prop := aᶜ = ⊥

/-- The Dense-Top property: every dense element equals top -/
class HasDenseTopProperty (α : Type*) [HeytingAlgebra α] : Prop where
  dense_eq_top : ∀ a : α, IsDense a → a = ⊤

/-- KEY THEOREM: In any Heyting algebra with Dense-Top, regular elements satisfy LEM -/
theorem regular_implies_LEM_of_denseTop [HasDenseTopProperty α] (a : α)
    (ha : Heyting.IsRegular a) : a ⊔ aᶜ = ⊤ := by
  have step1 : (a ⊔ aᶜ)ᶜ = ⊥ := by
    rw [compl_sup, ha.eq, inf_comm, inf_compl_eq_bot]
  have hDense : IsDense (a ⊔ aᶜ) := step1
  exact HasDenseTopProperty.dense_eq_top (a ⊔ aᶜ) hDense

/-- The contrapositive of the sufficient Dense-Top condition. -/
theorem not_denseTop_of_regular_not_LEM
    (h : ∃ a : α, Heyting.IsRegular a ∧ a ⊔ aᶜ ≠ ⊤) :
    ¬HasDenseTopProperty α := by
  intro hDT
  obtain ⟨a, ha_reg, ha_not_LEM⟩ := h
  exact ha_not_LEM (@regular_implies_LEM_of_denseTop α _ hDT a ha_reg)

/-- Dense-Top characterizes excluded middle for all elements, not just regular ones. -/
theorem denseTop_iff_excludedMiddle :
    HasDenseTopProperty α ↔ ∀ a : α, a ⊔ aᶜ = ⊤ := by
  constructor
  · intro h a
    apply h.dense_eq_top
    change (a ⊔ aᶜ)ᶜ = ⊥
    rw [compl_sup, inf_compl_eq_bot]
  · intro h
    exact ⟨fun a ha => by
      change aᶜ = ⊥ at ha
      simpa [ha] using h a⟩

/-- The converse restricted to regular elements fails on the three-chain. -/
theorem threeChain_regular_LEM_without_denseTop :
    (∀ a : Fin 3, Heyting.IsRegular a → a ⊔ aᶜ = ⊤) ∧
      ¬HasDenseTopProperty (Fin 3) := by
  constructor
  · decide
  · intro h
    have := h.dense_eq_top (1 : Fin 3) (by change (1 : Fin 3)ᶜ = 0; decide)
    exact (by decide : (1 : Fin 3) ≠ ⊤) this

section BooleanDenseTop

variable {β : Type*} [BooleanAlgebra β]

/-- In a BOOLEAN algebra, dense implies top.
    This is the correct version - Boolean algebras always have Dense-Top. -/
theorem dense_eq_top_of_boolean (a : β) (h : aᶜ = ⊥) : a = ⊤ := by
  exact compl_eq_bot.mp h

/-- Boolean algebras have the Dense-Top property -/
instance boolean_has_denseTop : HasDenseTopProperty β where
  dense_eq_top := fun a h => dense_eq_top_of_boolean a h

/-- COROLLARY: In Boolean algebras, regular elements satisfy LEM (trivially, all elements do) -/
theorem regular_implies_LEM_boolean (a : β) : a ⊔ aᶜ = ⊤ :=
  sup_compl_eq_top

end BooleanDenseTop

namespace FiniteCounterexample

inductive H5 : Type
  | bot : H5
  | a : H5
  | b : H5
  | ab : H5
  | top : H5
  deriving DecidableEq

instance : Fintype H5 where
  elems := {.bot, .a, .b, .ab, .top}
  complete value := by cases value <;> simp

namespace H5

open H5

def le' (x y : H5) : Prop :=
  match x, y with
  | bot, _ => True
  | a, a => True
  | a, ab => True
  | a, top => True
  | b, b => True
  | b, ab => True
  | b, top => True
  | ab, ab => True
  | ab, top => True
  | top, top => True
  | _, _ => False

instance : LE H5 := ⟨le'⟩

instance : DecidableRel (LE.le (α := H5)) := by
  intro x y
  cases x <;> cases y <;> (first | exact isTrue trivial | exact isFalse (fun h => h))

private theorem le_refl' (x : H5) : x ≤ x := by cases x <;> trivial
private theorem le_trans' {x y z : H5} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  cases x <;> cases y <;> cases z <;> trivial

private theorem le_antisymm' {x y : H5} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd hyx (fun h => h) | exact absurd hxy (fun h => h)

instance : Preorder H5 where
  le_refl := le_refl'
  le_trans := @le_trans'
  lt_iff_le_not_ge _ _ := Iff.rfl

instance : PartialOrder H5 where
  le_antisymm := @le_antisymm'

instance : BoundedOrder H5 where
  top := top
  le_top x := by cases x <;> trivial
  bot := bot
  bot_le x := by cases x <;> trivial

def inf' (x y : H5) : H5 :=
  match x, y with
  | bot, _ => bot
  | _, bot => bot
  | top, y => y
  | x, top => x
  | a, a => a
  | a, b => bot
  | b, a => bot
  | b, b => b
  | a, ab => a
  | ab, a => a
  | b, ab => b
  | ab, b => b
  | ab, ab => ab

def sup' (x y : H5) : H5 :=
  match x, y with
  | top, _ => top
  | _, top => top
  | bot, y => y
  | x, bot => x
  | a, a => a
  | b, b => b
  | a, b => ab
  | b, a => ab
  | a, ab => ab
  | ab, a => ab
  | b, ab => ab
  | ab, b => ab
  | ab, ab => ab

instance : Lattice H5 where
  inf := inf'
  sup := sup'
  inf_le_left x y := by cases x <;> cases y <;> trivial
  inf_le_right x y := by cases x <;> cases y <;> trivial
  le_inf x y z _ _ := by cases x <;> cases y <;> cases z <;> trivial
  le_sup_left x y := by cases x <;> cases y <;> trivial
  le_sup_right x y := by cases x <;> cases y <;> trivial
  sup_le x y z _ _ := by cases x <;> cases y <;> cases z <;> trivial

instance : DistribLattice H5 where
  le_sup_inf x y z := by cases x <;> cases y <;> cases z <;> trivial

def himp' (x y : H5) : H5 :=
  match x, y with
  | bot, _ => top
  | top, y => y
  | a, bot => b
  | a, a => top
  | a, b => b
  | a, ab => top
  | a, top => top
  | b, bot => a
  | b, a => a
  | b, b => top
  | b, ab => top
  | b, top => top
  | ab, bot => bot
  | ab, a => a
  | ab, b => b
  | ab, ab => top
  | ab, top => top

instance : HImp H5 := ⟨himp'⟩
instance : Compl H5 := ⟨fun x => himp' x bot⟩

instance : HeytingAlgebra H5 where
  himp := himp'
  le_himp_iff x y z := by
    cases x <;> cases y <;> cases z <;> decide
  compl := fun x => himp' x bot
  himp_bot x := by
    cases x <;> rfl

theorem a_is_regular : Heyting.IsRegular (a : H5) := by
  rfl

theorem a_not_LEM : (a : H5) ⊔ aᶜ ≠ (⊤ : H5) := by
  decide

private noncomputable def rank : H5 → ℝ
  | bot => 0 | a => 1 / 3 | b => 1 / 3 | ab => 2 / 3 | top => 1

/-- Equal atom weights with a positive mass above their join. -/
noncomputable def rankValuation : ModularValuation H5 where
  val := rank
  monotone := by
    intro x y h
    change le' x y at h
    cases x <;> cases y <;> norm_num [rank, le'] at *
  val_bot := rfl
  val_top := rfl
  modular := by
    intro x y
    change rank x + rank y = rank (sup' x y) + rank (inf' x y)
    cases x <;> cases y <;> norm_num [rank, sup', inf']

/-- Exact negation of a regular element does not force a point interval. -/
theorem regular_exact_negation_with_positive_width :
    Heyting.IsRegular (a : H5) ∧
      heytingInterval rankValuation aᶜ =
        (fun x : ℝ => 1 - x) ⁻¹' heytingInterval rankValuation a ∧
      heytingWidth rankValuation a = 1 / 3 := by
  refine ⟨a_is_regular, heytingInterval_compl_eq_of_regular _ _ rfl, ?_⟩
  norm_num [heytingWidth, upperBound, lowerBound, rankValuation, rank,
    Compl.compl, himp']

end H5

/-- There exists a finite Heyting algebra with a regular element that fails LEM. -/
theorem exists_finite_regular_not_LEM :
    ∃ (α : Type) (_ : HeytingAlgebra α) (_ : Fintype α),
      ∃ a : α, Heyting.IsRegular a ∧ a ⊔ aᶜ ≠ (⊤ : α) := by
  refine ⟨H5, inferInstance, inferInstance, H5.a, ?_, ?_⟩
  · exact H5.a_is_regular
  · exact H5.a_not_LEM

end FiniteCounterexample

section TopologicalCounterexample

variable {X : Type*} [TopologicalSpace X]

/-- Opens form a HeytingAlgebra (via Frame structure from Mathlib) -/
example : HeytingAlgebra (Opens X) := inferInstance

/-- The Heyting complement of an open set equals the interior of its set complement.

This is a fundamental fact about the Frame structure of Opens X. The Heyting complement Uᶜ
is the largest open set disjoint from U, which equals Opens.interior((U : Set X)ᶜ).
-/
theorem opens_compl_eq_interior_compl (U : Opens X) :
    ((Uᶜ : Opens X) : Set X) = interior (U : Set X)ᶜ := by
  exact Opens.coe_compl_eq_interior_compl

/-- An open set is "dense" in the Heyting sense if its complement has empty interior.

For Opens X (a Frame = complete Heyting algebra):
- The Heyting complement Uᶜ = U ⇨ ⊥ = ⨆ {V | V ⊓ U = ⊥}
- This equals the largest open set disjoint from U
- Which is interior((U : Set X)ᶜ)

So IsDense U (i.e., Uᶜ = ⊥) iff interior(Uᶜ) = ∅, i.e., U is topologically dense. -/
theorem opens_dense_iff (U : Opens X) :
    IsDense U ↔ interior (U : Set X)ᶜ = ∅ := by
  rw [IsDense, ← opens_compl_eq_interior_compl]
  exact ⟨fun h => by rw [h]; rfl, fun h => SetLike.coe_injective h⟩

/-- The counterexample structure: X has a dense open proper subset -/
def HasDenseProperOpen (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ U : Opens X, interior (U : Set X)ᶜ = ∅ ∧ (U : Set X) ≠ univ

/-- If X has a dense proper open, then Opens X does NOT have Dense-Top -/
theorem not_denseTop_of_dense_proper_open (h : HasDenseProperOpen X) :
    ¬HasDenseTopProperty (Opens X) := by
  intro ⟨hDT⟩
  obtain ⟨U, hDense_set, hProper⟩ := h
  have hDense : IsDense U := by
    rw [opens_dense_iff]
    exact hDense_set
  have hTop : U = ⊤ := hDT U hDense
  have : (U : Set X) = univ := by
    rw [hTop]
    rfl
  exact hProper this

/-- ℝ has a dense proper open (any interval missing boundary points) -/
theorem real_has_dense_proper_open : HasDenseProperOpen ℝ := by
  refine ⟨⟨({0} : Set ℝ)ᶜ, isClosed_singleton.isOpen_compl⟩, ?_, ?_⟩
  · change interior (({0} : Set ℝ)ᶜ)ᶜ = ∅
    simpa only [compl_compl] using interior_singleton (0 : ℝ)
  · intro h
    have := congrArg (fun s : Set ℝ => (0 : ℝ) ∈ s) h
    simp at this

/-- MAIN COUNTEREXAMPLE: Opens of ℝ does NOT have Dense-Top property -/
theorem opens_real_not_denseTop : ¬HasDenseTopProperty (Opens ℝ) :=
  not_denseTop_of_dense_proper_open real_has_dense_proper_open

/-- Helper: interior of (0,1)ᶜ in ℝ equals (-∞,0) ∪ (1,∞). -/
private lemma interior_Ioo_01_compl : interior (Ioo (0:ℝ) 1)ᶜ = Iio 0 ∪ Ioi 1 := by
  rw [interior_compl, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  ext x
  simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]

/-- Helper: The double complement of (0,1) in Opens ℝ equals (0,1) -/
lemma Ioo_01_is_regular :
    let U : Opens ℝ := ⟨Ioo (0:ℝ) 1, isOpen_Ioo⟩
    U = Uᶜᶜ := by
  intro U
  apply SetLike.ext'
  change Ioo (0 : ℝ) 1 = (↑(Uᶜᶜ) : Set ℝ)
  rw [opens_compl_eq_interior_compl, opens_compl_eq_interior_compl,
    ← closure_eq_compl_interior_compl]
  change Ioo (0 : ℝ) 1 = interior (closure (Ioo (0 : ℝ) 1))
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), interior_Icc]

/-- COROLLARY: There exists a regular element in Opens ℝ that fails LEM -/
theorem exists_regular_not_LEM_in_opens_real :
    ∃ U : Opens ℝ, Heyting.IsRegular U ∧ U ⊔ Uᶜ ≠ ⊤ := by
  let U : Opens ℝ := ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩
  refine ⟨U, Ioo_01_is_regular.symm, ?_⟩
  intro h
  have h0 : (0 : ℝ) ∈ (U ⊔ Uᶜ : Opens ℝ) := by rw [h]; trivial
  change (0 : ℝ) ∈ (U : Set ℝ) ∪ (↑Uᶜ : Set ℝ) at h0
  rw [opens_compl_eq_interior_compl] at h0
  change (0 : ℝ) ∈ Ioo 0 1 ∪ interior (Ioo (0 : ℝ) 1)ᶜ at h0
  rw [interior_Ioo_01_compl] at h0
  norm_num at h0

end TopologicalCounterexample

section ProbabilityRamifications

variable {α : Type*} [HeytingAlgebra α]

/-- A "probability-like" function satisfies additivity on disjoint elements -/
structure ProbabilityFunction (α : Type*) [HeytingAlgebra α] where
  P : α → ℝ
  P_top : P ⊤ = 1
  P_bot : P ⊥ = 0
  P_mono : ∀ x y, x ≤ y → P x ≤ P y
  P_add : ∀ x y, Disjoint x y → P (x ⊔ y) = P x + P y

/-- Preserve the supplied function while exposing its additive law. -/
def ProbabilityFunction.toAdditiveValuation (μ : ProbabilityFunction α) :
    ProbabilityTheory.Common.AdditiveValuation α where
  val := μ.P
  mono := μ.P_mono
  val_bot := μ.P_bot
  val_top := μ.P_top
  additive a b hab := μ.P_add a b (disjoint_iff.mpr hab)

/-- Excluded middle suffices for the classical complement sum rule. -/
theorem sum_rule_requires_LEM (μ : ProbabilityFunction α) (a : α)
    (hLEM : a ⊔ aᶜ = ⊤) : μ.P a + μ.P aᶜ = 1 := by
  calc μ.P a + μ.P aᶜ = μ.P (a ⊔ aᶜ) :=
        complementSum_eq_sup μ.toAdditiveValuation a
    _ = 1 := by rw [hLEM, μ.P_top]

/-- Without LEM, we only get an INEQUALITY: P(A) + P(Aᶜ) ≤ 1 -/
theorem sum_rule_inequality (μ : ProbabilityFunction α) (a : α) :
    μ.P a + μ.P aᶜ ≤ 1 := by
  calc μ.P a + μ.P aᶜ = μ.P (a ⊔ aᶜ) :=
        complementSum_eq_sup μ.toAdditiveValuation a
    _ ≤ 1 := μ.toAdditiveValuation.le_one _

/-- The observed complement defect; zero need not reflect a lattice identity. -/
def excludedMiddleGap (μ : ProbabilityFunction α) (a : α) : ℝ :=
  1 - (μ.P a + μ.P aᶜ)

/-- The gap is always non-negative -/
theorem excludedMiddleGap_nonneg (μ : ProbabilityFunction α) (a : α) :
    0 ≤ excludedMiddleGap μ a := by
  unfold excludedMiddleGap
  linarith [sum_rule_inequality μ a]

/-- The gap is zero iff LEM holds (assuming P is strictly monotone on relevant part) -/
theorem excludedMiddleGap_zero_iff_LEM (μ : ProbabilityFunction α) (a : α)
    (hStrict : ∀ x y, x < y → μ.P x < μ.P y) :
    excludedMiddleGap μ a = 0 ↔ a ⊔ aᶜ = ⊤ := by
  apply complementGap_zero_iff_of_reflects_top μ.toAdditiveValuation
  intro x hx
  by_contra h
  have hlt := hStrict x ⊤ (lt_top_iff_ne_top.mpr h)
  rw [μ.P_top] at hlt
  exact (ne_of_lt hlt) hx

end ProbabilityRamifications

end KnuthSkilling.Heyting.RegularityLEMCounterexample
