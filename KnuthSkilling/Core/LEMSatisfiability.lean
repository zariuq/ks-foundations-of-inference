/-
# The sharp two-thirds gap for finite Heyting algebras

Bumpus and Kocsis, “Degree of Satisfiability in Heyting Algebras,”
https://arxiv.org/abs/2110.11515 (Theorem 2.4).

`lemDegree` counts elements uniformly: a non-Boolean finite algebra has degree
at most two thirds, attained by the three-chain. This counting result supplies
no approximation bound for an arbitrary weighted valuation or inference rule.
The proof decomposes along complemented elements and inducts on cardinality.
-/

import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Heyting.Regular
import Mathlib.Order.LatticeIntervals
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic
import KnuthSkilling.Core.RegularityLEMCounterexample

namespace KnuthSkilling.Heyting.LEMSatisfiability

universe u

variable {α : Type u} [HeytingAlgebra α]

/-- An element satisfies the Law of Excluded Middle if a ⊔ aᶜ = ⊤ -/
def SatisfiesLEM (a : α) : Prop := a ⊔ aᶜ = ⊤

/-- The set of elements satisfying LEM -/
def LEMElements (α : Type*) [HeytingAlgebra α] : Set α :=
  {a | SatisfiesLEM a}

/-- Complemented elements: those with a true complement (not just pseudo-complement) -/
def IsComplemented (a : α) : Prop :=
  ∃ b : α, a ⊔ b = ⊤ ∧ a ⊓ b = ⊥

/-- ⊤ always satisfies LEM -/
theorem top_satisfiesLEM : SatisfiesLEM (⊤ : α) := by
  simp [SatisfiesLEM, compl_top]

/-- ⊥ always satisfies LEM -/
theorem bot_satisfiesLEM : SatisfiesLEM (⊥ : α) := by
  simp [SatisfiesLEM, compl_bot]

/-- In a Boolean algebra, ALL elements satisfy LEM -/
theorem boolean_all_satisfyLEM {β : Type*} [BooleanAlgebra β] (a : β) :
    SatisfiesLEM a := by
  simp [SatisfiesLEM, sup_compl_eq_top]

/-- If a satisfies LEM, then aᶜᶜ = a (double negation elimination for that element) -/
theorem compl_compl_of_satisfiesLEM (a : α) (h : SatisfiesLEM a) : aᶜᶜ = a := by
  apply le_antisymm
  · calc aᶜᶜ = aᶜᶜ ⊓ ⊤ := by simp
      _ = aᶜᶜ ⊓ (a ⊔ aᶜ) := by rw [h]
      _ = (aᶜᶜ ⊓ a) ⊔ (aᶜᶜ ⊓ aᶜ) := by rw [inf_sup_left]
      _ = (aᶜᶜ ⊓ a) ⊔ ⊥ := by simp only [inf_comm, inf_compl_eq_bot]
      _ = aᶜᶜ ⊓ a := by simp
      _ ≤ a := inf_le_right
  · exact le_compl_compl

section Finite

variable [Fintype α]

/-- The count of elements satisfying LEM -/
noncomputable def lemCount (α : Type*) [HeytingAlgebra α] [Fintype α] : ℕ :=
  Finset.card (@Finset.filter α (fun a => a ⊔ aᶜ = ⊤)
    (Classical.decPred (fun a : α => a ⊔ aᶜ = ⊤)) Finset.univ)

/-- The degree of LEM satisfiability (as a rational number) -/
noncomputable def lemDegree (α : Type*) [HeytingAlgebra α] [Fintype α] : ℚ :=
  (lemCount α : ℚ) / (Fintype.card α : ℚ)

/-- `lemCount` is bounded by the total cardinality. -/
theorem lemCount_le_card (α : Type*) [HeytingAlgebra α] [Fintype α] :
    lemCount α ≤ Fintype.card α := by
  classical
  unfold lemCount
  simpa using
    (Finset.card_filter_le (s := (Finset.univ : Finset α)) (p := fun a : α => a ⊔ aᶜ = ⊤))

/-- `lemDegree` is always nonnegative. -/
theorem lemDegree_nonneg (α : Type*) [HeytingAlgebra α] [Fintype α] :
    0 ≤ lemDegree α := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `lemDegree` is always at most `1`. -/
theorem lemDegree_le_one (α : Type*) [HeytingAlgebra α] [Fintype α] :
    lemDegree α ≤ 1 := by
  unfold lemDegree
  exact div_le_one_of_le₀ (by exact_mod_cast lemCount_le_card α) (Nat.cast_nonneg _)

/-- In a Boolean algebra, the LEM degree is 1 -/
theorem lemDegree_boolean {β : Type*} [BooleanAlgebra β] [Fintype β]
    (_hcard : 0 < Fintype.card β) : lemDegree β = 1 := by
  simp only [lemDegree, lemCount]
  have h : @Finset.filter β (fun a => a ⊔ aᶜ = ⊤) (Classical.decPred _) Finset.univ = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sup_compl_eq_top]
  rw [h, Finset.card_univ]
  field_simp

end Finite

inductive Chain3 : Type
  | bot : Chain3
  | mid : Chain3
  | top : Chain3
  deriving DecidableEq

instance : Fintype Chain3 where
  elems := {.bot, .mid, .top}
  complete value := by cases value <;> simp

namespace Chain3

open Chain3

/-- Order predicate for Chain3 -/
def le' (a b : Chain3) : Prop := match a, b with
  | bot, _ => True
  | mid, mid => True
  | mid, top => True
  | top, top => True
  | _, _ => False

instance : LE Chain3 := ⟨le'⟩

instance : LT Chain3 where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : DecidableRel (LE.le (α := Chain3)) := fun a b =>
  match a, b with
  | bot, _ => isTrue trivial
  | mid, mid => isTrue trivial
  | mid, top => isTrue trivial
  | top, top => isTrue trivial
  | mid, bot => isFalse (fun h => h)
  | top, bot => isFalse (fun h => h)
  | top, mid => isFalse (fun h => h)

private theorem le_refl' (a : Chain3) : a ≤ a := by cases a <;> trivial

private theorem le_trans' {a b c : Chain3} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> trivial

private theorem le_antisymm' {a b : Chain3} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd hba (fun h => h) | exact absurd hab (fun h => h)

instance : Preorder Chain3 where
  le_refl := le_refl'
  le_trans := @le_trans'
  lt_iff_le_not_ge _ _ := Iff.rfl

instance : PartialOrder Chain3 where
  le_antisymm := @le_antisymm'

instance : BoundedOrder Chain3 where
  top := top
  le_top a := by cases a <;> trivial
  bot := bot
  bot_le a := trivial

/-- Meet on Chain3 -/
def inf' (a b : Chain3) : Chain3 := match a, b with
  | bot, _ => bot | _, bot => bot
  | mid, mid => mid | mid, top => mid | top, mid => mid
  | top, top => top

/-- Join on Chain3 -/
def sup' (a b : Chain3) : Chain3 := match a, b with
  | top, _ => top | _, top => top
  | mid, mid => mid | mid, bot => mid | bot, mid => mid
  | bot, bot => bot

instance : Lattice Chain3 where
  inf := inf'
  sup := sup'
  inf_le_left a b := by cases a <;> cases b <;> trivial
  inf_le_right a b := by cases a <;> cases b <;> trivial
  le_inf a b c _ _ := by cases a <;> cases b <;> cases c <;> trivial
  le_sup_left a b := by cases a <;> cases b <;> trivial
  le_sup_right a b := by cases a <;> cases b <;> trivial
  sup_le a b c _ _ := by cases a <;> cases b <;> cases c <;> trivial

instance : DistribLattice Chain3 where
  le_sup_inf a b c := by cases a <;> cases b <;> cases c <;> trivial

/-- Heyting implication: x ⇨ y = greatest z such that x ⊓ z ≤ y -/
def himp' (a b : Chain3) : Chain3 := match a, b with
  | _, top => top
  | bot, _ => top
  | mid, mid => top
  | mid, bot => bot
  | top, mid => mid
  | top, bot => bot

/-- Complement: a ⇨ ⊥ -/
def compl' (a : Chain3) : Chain3 := match a with
  | bot => top
  | mid => bot
  | top => bot

instance : HImp Chain3 := ⟨himp'⟩
instance : Compl Chain3 := ⟨compl'⟩

instance : HeytingAlgebra Chain3 where
  himp := himp'
  le_himp_iff a b c := by
    cases a <;> cases b <;> cases c <;> decide
  compl := compl'
  himp_bot a := by cases a <;> rfl

/-- The middle element does NOT satisfy LEM: mid ⊔ midᶜ = mid ⊔ ⊥ = mid ≠ ⊤ -/
theorem mid_not_satisfies_lem : ¬SatisfiesLEM (mid : Chain3) := by
  unfold SatisfiesLEM
  intro h
  cases h

/-- ⊥ satisfies LEM -/
theorem chain3_bot_satisfies_lem : SatisfiesLEM (bot : Chain3) := by
  unfold SatisfiesLEM
  rfl

/-- ⊤ satisfies LEM -/
theorem chain3_top_satisfies_lem : SatisfiesLEM (top : Chain3) := by
  unfold SatisfiesLEM
  rfl

/-- Helper: decide satisfiesLEM for Chain3 elements -/
private def chain3_satisfies_lem_dec (a : Chain3) : Decidable (a ⊔ aᶜ = ⊤) :=
  match a with
  | bot => isTrue rfl
  | mid => isFalse (fun h => by cases h)
  | top => isTrue rfl

/-- The LEM count for Chain3 is exactly 2 (only ⊥ and ⊤ satisfy LEM) -/
theorem chain3_lemCount : lemCount Chain3 = 2 := by
  have h : @Finset.filter Chain3 (fun a => a ⊔ aᶜ = ⊤) (Classical.decPred _) Finset.univ =
      {bot, top} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    cases x <;> decide
  rw [lemCount, h]
  decide

/-- Chain3 has exactly 3 elements -/
theorem chain3_card : Fintype.card Chain3 = 3 := by decide

/-- **The 2/3 Threshold**: Chain3 achieves exactly 2/3 LEM degree -/
theorem chain3_lemDegree : lemDegree Chain3 = 2/3 := by
  simp only [lemDegree, chain3_lemCount, chain3_card]
  norm_num

/-- Chain3 is NOT Boolean (has non-complemented element) -/
theorem chain3_not_boolean : ∃ a : Chain3, a ⊔ aᶜ ≠ ⊤ := by
  use mid
  intro h
  cases h

end Chain3

/-- If a satisfies LEM, then aᶜ satisfies LEM -/
theorem satisfiesLEM_compl (a : α) (h : SatisfiesLEM a) : SatisfiesLEM aᶜ := by
  unfold SatisfiesLEM at *
  have hcc : aᶜᶜ = a := compl_compl_of_satisfiesLEM a h
  rw [hcc, sup_comm]
  exact h

theorem exists_finite_regular_not_satisfiesLEM :
    ∃ (β : Type) (_ : HeytingAlgebra β) (_ : Fintype β),
      ∃ a : β, Heyting.IsRegular a ∧ ¬SatisfiesLEM a := by
  have h :=
    KnuthSkilling.Heyting.RegularityLEMCounterexample.FiniteCounterexample.exists_finite_regular_not_LEM
  rcases h with ⟨β, instβ, instF, a, haReg, haNot⟩
  refine ⟨β, instβ, instF, a, haReg, ?_⟩
  exact haNot

section TwoThirdsTechnical

private lemma exists_mem_ne_ne_of_card_gt_two {δ : Type*} [DecidableEq δ] (s : Finset δ)
    (a b : δ) (hcard : 2 < s.card) : ∃ x ∈ s, x ≠ a ∧ x ≠ b := by
  classical
  by_contra h
  push Not at h
  have hs : s ⊆ ({a, b} : Finset δ) := by
    intro x hx
    by_cases hxa : x = a
    · simp [hxa]
    · simp [h x hx hxa]
  have := (Finset.card_le_card hs).trans (Finset.card_le_two (a := a) (b := b))
  omega

theorem satisfiesLEM_prod_iff {β γ : Type*} [HeytingAlgebra β] [HeytingAlgebra γ] (x : β × γ) :
    SatisfiesLEM x ↔ SatisfiesLEM x.1 ∧ SatisfiesLEM x.2 := by
  cases x with
  | mk b c =>
    unfold SatisfiesLEM
    simp [Prod.ext_iff]

theorem lemCount_prod (β γ : Type*) [HeytingAlgebra β] [Fintype β] [HeytingAlgebra γ] [Fintype γ] :
    lemCount (β × γ) = lemCount β * lemCount γ := by
  classical
  unfold lemCount
  rw [← Finset.univ_product_univ]
  have hfilter :
      (@Finset.filter (β × γ) (fun x => x ⊔ xᶜ = (⊤ : β × γ)) (Classical.decPred _)
          (Finset.univ ×ˢ Finset.univ)) =
        (@Finset.filter β (fun b => b ⊔ bᶜ = (⊤ : β)) (Classical.decPred _) Finset.univ) ×ˢ
          (@Finset.filter γ (fun c => c ⊔ cᶜ = (⊤ : γ)) (Classical.decPred _) Finset.univ) := by
    simpa [Prod.ext_iff] using
      (Finset.filter_product (s := (Finset.univ : Finset β)) (t := (Finset.univ : Finset γ))
        (p := fun b : β => b ⊔ bᶜ = (⊤ : β)) (q := fun c : γ => c ⊔ cᶜ = (⊤ : γ)))
  rw [hfilter, Finset.card_product]

theorem lemDegree_prod (β γ : Type*) [HeytingAlgebra β] [Fintype β] [HeytingAlgebra γ] [Fintype γ] :
    lemDegree (β × γ) = lemDegree β * lemDegree γ := by
  classical
  unfold lemDegree
  simp [lemCount_prod, Fintype.card_prod, div_mul_div_comm]

namespace IicHeyting

variable {β : Type*} [HeytingAlgebra β]

noncomputable def himpIic (c : β) : Set.Iic c → Set.Iic c → Set.Iic c :=
  fun x y => ⟨(x.1 ⇨ y.1) ⊓ c, inf_le_right⟩

noncomputable instance (c : β) : HImp (Set.Iic c) := ⟨himpIic (β := β) c⟩

instance (c : β) : DistribLattice (Set.Iic c) where
  le_sup_inf x y z := by
    change ((x.1 ⊔ y.1) ⊓ (x.1 ⊔ z.1) ≤ x.1 ⊔ (y.1 ⊓ z.1))
    simpa using (le_sup_inf (x := x.1) (y := y.1) (z := z.1))

noncomputable instance (c : β) : HeytingAlgebra (Set.Iic c) := by
  classical
  refine HeytingAlgebra.ofHImp (α := Set.Iic c) (himp := fun x y => himpIic (β := β) c x y) ?_
  intro d a b
  dsimp [himpIic]
  change (d.1 ≤ (a.1 ⇨ b.1) ⊓ c) ↔ (d.1 ⊓ a.1 ≤ b.1)
  constructor
  · intro h
    have h1 : d.1 ≤ a.1 ⇨ b.1 := le_trans h inf_le_left
    exact (le_himp_iff).1 h1
  · intro h
    apply le_inf
    · exact (le_himp_iff).2 h
    · exact d.2

end IicHeyting

open IicHeyting

private noncomputable def decompOrderIso {β : Type*} [HeytingAlgebra β] (c : β)
    (hc : c ⊔ cᶜ = (⊤ : β)) : β ≃o (Set.Iic c × Set.Iic cᶜ) := by
  have reconstruct (x : β) : (x ⊓ c) ⊔ (x ⊓ cᶜ) = x := by
    rw [← inf_sup_left, hc, inf_top_eq]
  refine
    { toFun := fun x => (⟨x ⊓ c, inf_le_right⟩, ⟨x ⊓ cᶜ, inf_le_right⟩)
      invFun := fun y => y.1.1 ⊔ y.2.1
      left_inv := reconstruct
      right_inv := ?_
      map_rel_iff' := ?_ }
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxc : x ⊓ cᶜ = ⊥ := le_antisymm
      ((inf_le_inf_right _ hx).trans_eq inf_compl_eq_bot) bot_le
    have hyc : y ⊓ c = ⊥ := le_antisymm
      ((inf_le_inf_right _ hy).trans_eq (compl_inf_self c)) bot_le
    apply Prod.ext <;> apply Subtype.ext
    · simp only [inf_sup_right, inf_eq_left.mpr hx, hyc, sup_bot_eq]
    · simp only [inf_sup_right, inf_eq_left.mpr hy, hxc, bot_sup_eq]
  · intro x y
    constructor
    · intro h
      have h' : x ⊓ c ≤ y ⊓ c ∧ x ⊓ cᶜ ≤ y ⊓ cᶜ := h
      simpa only [reconstruct] using sup_le_sup h'.1 h'.2
    · exact fun h => ⟨inf_le_inf_right _ h, inf_le_inf_right _ h⟩

private theorem satisfiesLEM_iff_of_orderIso {β γ : Type*} [HeytingAlgebra β] [HeytingAlgebra γ]
    (f : β ≃o γ) (a : β) : SatisfiesLEM a ↔ SatisfiesLEM (f a) := by
  unfold SatisfiesLEM
  rw [← map_compl, ← map_sup, ← map_top f]
  exact f.injective.eq_iff.symm

private theorem lemCount_congr_of_orderIso {β γ : Type*} [HeytingAlgebra β] [Fintype β]
    [HeytingAlgebra γ] [Fintype γ] (f : β ≃o γ) :
    lemCount β = lemCount γ := by
  classical
  let pβ : β → Prop := fun a => a ⊔ aᶜ = (⊤ : β)
  let pγ : γ → Prop := fun a => a ⊔ aᶜ = (⊤ : γ)
  let _ : DecidablePred pβ := Classical.decPred _
  let _ : DecidablePred pγ := Classical.decPred _
  let e : {a : β // pβ a} ≃ {b : γ // pγ b} :=
    { toFun := fun x => ⟨f x.1, (satisfiesLEM_iff_of_orderIso f x.1).1 x.2⟩
      invFun := fun y => ⟨f.symm y.1, (satisfiesLEM_iff_of_orderIso f.symm y.1).1 y.2⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro y; ext; simp }
  have hc : Fintype.card {a : β // pβ a} = Fintype.card {b : γ // pγ b} :=
    Fintype.card_congr e
  have hβ : lemCount β = Fintype.card {a : β // pβ a} := by
    simpa [lemCount, pβ] using (Fintype.card_subtype (α := β) pβ).symm
  have hγ : lemCount γ = Fintype.card {b : γ // pγ b} := by
    simpa [lemCount, pγ] using (Fintype.card_subtype (α := γ) pγ).symm
  simpa [hβ, hγ] using hc

private theorem lemDegree_congr_of_orderIso {β γ : Type*} [HeytingAlgebra β] [Fintype β]
    [HeytingAlgebra γ] [Fintype γ] (f : β ≃o γ) :
    lemDegree β = lemDegree γ := by
  classical
  unfold lemDegree
  have hCount : lemCount β = lemCount γ := lemCount_congr_of_orderIso f
  have hCard : Fintype.card β = Fintype.card γ := Fintype.card_congr f.toEquiv
  simp [hCount, hCard]

private lemma compl_eq_top_iff {β : Type*} [HeytingAlgebra β] (a : β) :
    aᶜ = (⊤ : β) ↔ a = ⊥ := by
  constructor
  · intro h
    apply (le_compl_self (a := a)).1
    simp [h]
  · intro h
    simp [h]

private lemma two_div_card_le_two_thirds (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℚ) / (n : ℚ) ≤ 2/3 := by
  have hn0 : (0 : ℚ) < (n : ℚ) := by
    have : (0 : ℕ) < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hn
    exact_mod_cast this
  have : (2 : ℚ) ≤ (2/3 : ℚ) * (n : ℚ) := by
    have hn' : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have hnonneg : (0 : ℚ) ≤ (2/3 : ℚ) := by norm_num
    calc
      (2 : ℚ) = (2/3 : ℚ) * (3 : ℚ) := by norm_num
      _ ≤ (2/3 : ℚ) * (n : ℚ) := mul_le_mul_of_nonneg_left hn' hnonneg
  exact (div_le_iff₀ hn0).2 this

end TwoThirdsTechnical

section Finite
variable [Fintype α]

/-- The 2/3 threshold is achievable: Chain3 achieves exactly 2/3 -/
theorem two_thirds_achievable : ∃ (β : Type) (_ : HeytingAlgebra β) (_ : Fintype β),
    (∃ a : β, a ⊔ aᶜ ≠ ⊤) ∧ @lemDegree β _ _ = 2/3 := by
  exact ⟨Chain3, inferInstance, inferInstance, Chain3.chain3_not_boolean, Chain3.chain3_lemDegree⟩

/-- **Theorem 2.4 (Bumpus–Kocsis)**: For any finite non-Boolean Heyting algebra,
the LEM degree is at most `2/3`. -/
theorem lem_degree_le_two_thirds
    (hNotBoolean : ∃ a : α, a ⊔ aᶜ ≠ ⊤)
    (_hCard : 0 < Fintype.card α) :
    lemDegree α ≤ 2/3 := by
  classical
  let P : ℕ → Prop :=
    fun n =>
      ∀ (β : Type u) [HeytingAlgebra β] [Fintype β],
        Fintype.card β = n →
          (∃ a : β, a ⊔ aᶜ ≠ (⊤ : β)) →
            lemDegree β ≤ 2/3
  have hP : P (Fintype.card α) := by
    refine Nat.strong_induction_on (n := Fintype.card α) ?_
    intro n ih β instβ instF hcardβ hNotBooleanβ
    classical
    by_cases hlem : lemCount β ≤ 2
    ·
      obtain ⟨a, ha⟩ := hNotBooleanβ
      have ha_notLEM : ¬SatisfiesLEM a := by
        intro h
        exact ha (by simpa [SatisfiesLEM] using h)
      have hcard_ge_three : 3 ≤ Fintype.card β := by
        have ha_bot : a ≠ (⊥ : β) := by
          intro ha'
          subst ha'
          have : SatisfiesLEM (⊥ : β) := by
            unfold SatisfiesLEM
            simp
          exact ha_notLEM this
        have ha_top : a ≠ (⊤ : β) := by
          intro ha'
          subst ha'
          have : SatisfiesLEM (⊤ : β) := by
            unfold SatisfiesLEM
            simp
          exact ha_notLEM this
        have hbot_top : (⊥ : β) ≠ (⊤ : β) := by
          intro hbt
          have : a ≤ (⊥ : β) := by
            simp [hbt]
          have ha' : a = (⊥ : β) := le_bot_iff.mp this
          exact ha_top (by simp [ha', hbt])
        let f : Fin 3 → β := fun i =>
          match (i : Nat) with
          | 0 => (⊥ : β)
          | 1 => a
          | _ => (⊤ : β)
        have hinj : Function.Injective f := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp [f] at hij
          all_goals try rfl
          · exact False.elim (ha_bot hij.symm)
          · exact False.elim (hbot_top hij)
          · exact False.elim (ha_bot hij)
          · exact False.elim (ha_top hij)
          · exact False.elim (hbot_top hij.symm)
          · exact False.elim (ha_top hij.symm)
        have : Fintype.card (Fin 3) ≤ Fintype.card β :=
          Fintype.card_le_of_injective (f := f) hinj
        simpa using this
      have hcard_ge_three' : 3 ≤ n := by simpa [hcardβ] using hcard_ge_three
      have hle_num : (lemCount β : ℚ) ≤ 2 := by exact_mod_cast hlem
      have hden_nonneg : 0 ≤ (Fintype.card β : ℚ) := by exact_mod_cast (Nat.zero_le _)
      have hdiv_le : lemDegree β ≤ (2 : ℚ) / (Fintype.card β : ℚ) := by
        unfold lemDegree
        exact (div_le_div_of_nonneg_right hle_num hden_nonneg)
      have htwo_div : (2 : ℚ) / (Fintype.card β : ℚ) ≤ 2/3 := by
        simpa [hcardβ] using two_div_card_le_two_thirds n hcard_ge_three'
      exact le_trans hdiv_le htwo_div
    ·
      have hlem_gt : 2 < lemCount β := lt_of_not_ge hlem
      let s : Finset β :=
        @Finset.filter β (fun a => a ⊔ aᶜ = (⊤ : β)) (Classical.decPred _) Finset.univ
      have hs_card : s.card = lemCount β := by
        simp [lemCount, s]
      have hs_gt : 2 < s.card := by simpa [hs_card] using hlem_gt
      have hbot_mem : (⊥ : β) ∈ s := by
        simp [s]
      have htop_mem : (⊤ : β) ∈ s := by
        simp [s]
      obtain ⟨c, hc_mem, hc_ne_bot, hc_ne_top⟩ :=
        exists_mem_ne_ne_of_card_gt_two (δ := β) s (⊥ : β) (⊤ : β) hs_gt
      have hc : c ⊔ cᶜ = (⊤ : β) := by
        simpa [s] using (Finset.mem_filter.1 hc_mem).2
      let f := decompOrderIso (β := β) c hc
      let _ : Fintype (Set.Iic c) := by classical exact inferInstance
      let _ : Fintype (Set.Iic cᶜ) := by classical exact inferInstance
      have hdeg_congr : lemDegree β = lemDegree (Set.Iic c × Set.Iic cᶜ) :=
        lemDegree_congr_of_orderIso (β := β) (γ := Set.Iic c × Set.Iic cᶜ) f
      have hdeg_prod : lemDegree (Set.Iic c × Set.Iic cᶜ) = lemDegree (Set.Iic c) * lemDegree (Set.Iic cᶜ) :=
        lemDegree_prod (Set.Iic c) (Set.Iic cᶜ)
      obtain ⟨a, ha_notLEM⟩ := hNotBooleanβ
      have ha_notLEM' : ¬SatisfiesLEM a := by
        intro h
        exact ha_notLEM (by simpa [SatisfiesLEM] using h)
      have ha_prod_notLEM : ¬SatisfiesLEM (f a) := by
        exact (satisfiesLEM_iff_of_orderIso f a).not.mp ha_notLEM'
      have hsplit : (¬SatisfiesLEM (f a).1) ∨ (¬SatisfiesLEM (f a).2) := by
        have : ¬(SatisfiesLEM (f a).1 ∧ SatisfiesLEM (f a).2) := by
          intro hboth
          exact ha_prod_notLEM ((satisfiesLEM_prod_iff (x := f a)).2 hboth)
        exact not_and_or.mp this
      have hc_ne_top' : c ≠ (⊤ : β) := hc_ne_top
      have hccompl_ne_top : cᶜ ≠ (⊤ : β) := by
        intro hctop
        have : c = (⊥ : β) := (compl_eq_top_iff (β := β) c).1 hctop
        exact hc_ne_bot this
      have factor_card_lt (d : β) (hd : d ≠ ⊤) : Fintype.card (Set.Iic d) < n := by
        have hlt := Fintype.card_subtype_lt (p := fun x : β => x ≤ d)
          (x := (⊤ : β)) (fun h => hd (top_le_iff.mp h))
        rw [hcardβ] at hlt
        exact hlt
      have hcard_Iic_lt := factor_card_lt c hc_ne_top'
      have hcard_IicCompl_lt := factor_card_lt cᶜ hccompl_ne_top
      have hdeg1_le1 : lemDegree (Set.Iic c) ≤ 1 := lemDegree_le_one (Set.Iic c)
      have hdeg2_le1 : lemDegree (Set.Iic cᶜ) ≤ 1 := lemDegree_le_one (Set.Iic cᶜ)
      have hdeg1_nonneg : 0 ≤ lemDegree (Set.Iic c) := lemDegree_nonneg (Set.Iic c)
      have hdeg2_nonneg : 0 ≤ lemDegree (Set.Iic cᶜ) := lemDegree_nonneg (Set.Iic cᶜ)
      have hbound :
          lemDegree (Set.Iic c) * lemDegree (Set.Iic cᶜ) ≤ 2/3 := by
        rcases hsplit with hbad1 | hbad2
        · exact (mul_le_of_le_one_right hdeg1_nonneg hdeg2_le1).trans
            (ih _ hcard_Iic_lt (Set.Iic c) rfl ⟨(f a).1, hbad1⟩)
        · exact (mul_le_of_le_one_left hdeg2_nonneg hdeg1_le1).trans
            (ih _ hcard_IicCompl_lt (Set.Iic cᶜ) rfl ⟨(f a).2, hbad2⟩)
      calc
        lemDegree β = lemDegree (Set.Iic c × Set.Iic cᶜ) := hdeg_congr
        _ = lemDegree (Set.Iic c) * lemDegree (Set.Iic cᶜ) := hdeg_prod
        _ ≤ 2/3 := hbound
  have := hP α rfl hNotBoolean
  exact this

/-- Contrapositive: If lemDegree > 2/3, the algebra is Boolean -/
theorem boolean_of_lem_degree_gt_two_thirds
    (hCard : 0 < Fintype.card α)
    (hDegree : 2/3 < lemDegree α) :
    ∀ a : α, a ⊔ aᶜ = ⊤ := by
  by_contra h
  push Not at h
  have := lem_degree_le_two_thirds h hCard
  linarith

end Finite

end KnuthSkilling.Heyting.LEMSatisfiability
