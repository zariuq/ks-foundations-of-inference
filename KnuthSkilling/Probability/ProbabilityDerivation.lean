/-
# Probability Derivation: Probability Calculus from K&S Representation

Derives the probability calculus (Sum Rule, Product Rule, etc.) from the
Knuth-Skilling representation theorem. This is NOT Cox's theorem itself,
but rather the probability rules that follow from having an additive representation.

Key structures:
- WeakRegraduation and Regraduation structures
- Probability rules (sum rule, product rule, Bayes' theorem, complement rule)
-/

import KnuthSkilling.Probability.Regraduation
import KnuthSkilling.Probability.BooleanRepresentation
import KnuthSkilling.Multiplicative
import KnuthSkilling.Multiplicative.DirectProduct

namespace KnuthSkilling.Probability


/-- A supplied normalized additive representation is an ordered embedding.
No surjectivity onto all nonnegative reals is asserted. -/
theorem ks_representation_theorem
    [KnuthSkillingMonoidBase α]
    [KnuthSkilling.Additive.HasNormalizedRepresentation α] :
    ∃ (Θ : α → ℝ),
      StrictMono Θ ∧
        Θ (KnuthSkillingMonoidBase.ident (α := α)) = 0 ∧
          (∀ x y : α, Θ (KSSemigroupBase.op x y) = Θ x + Θ y) := by
  classical
  obtain ⟨Θ, hΘ_order, hΘ_ident, hΘ_add⟩ :=
    KnuthSkilling.Additive.HasNormalizedRepresentation.exists_representation (α := α)
  refine ⟨Θ, ?_, hΘ_ident, ?_⟩
  · intro x y hxy
    have hx_le : x ≤ y := le_of_lt hxy
    have hy_not_le : ¬ y ≤ x := not_le.mpr hxy
    have hΘ_le : Θ x ≤ Θ y := (hΘ_order x y).1 hx_le
    have hΘ_ne : Θ x ≠ Θ y := by
      intro hEq
      have : Θ y ≤ Θ x := by simp [hEq]
      have : y ≤ x := (hΘ_order y x).2 this
      exact hy_not_le this
    exact lt_of_le_of_ne hΘ_le hΘ_ne
  · exact hΘ_add

def Regraduation.mk' (W : WeakRegraduation combine_fn)
    (h_additive : ∀ x y, W.regrade (x + y) = W.regrade x + W.regrade y) :
    Regraduation combine_fn where
  regrade := W.regrade
  strictMono := W.strictMono
  zero := W.zero
  one := W.one
  combine_eq_add := W.combine_eq_add
  additive := h_additive

/-- A supplied event-combination law with a normalized linearizer and rational calibration.
The rational agreement is an explicit premise, not a consequence of associativity alone. -/
structure CoxConsistency (α : Type*) [PlausibilitySpace α] [ComplementedLattice α]
    (v : Valuation α) where
  /-- There exists a function S for combining disjoint plausibilities -/
  combine_fn : ℝ → ℝ → ℝ
  /-- Combining disjoint events uses S -/
  combine_disjoint : ∀ {a b}, Disjoint a b →
    v.val (a ⊔ b) = combine_fn (v.val a) (v.val b)
  /-- S is commutative (symmetry) -/
  combine_comm : ∀ x y, combine_fn x y = combine_fn y x
  /-- S is associative -/
  combine_assoc : ∀ x y z, combine_fn (combine_fn x y) z = combine_fn x (combine_fn y z)
  /-- S(x, 0) = x (identity) -/
  combine_zero : ∀ x, combine_fn x 0 = x
  /-- S is strictly increasing in first argument when second is positive -/
  combine_strict_mono : ∀ {x₁ x₂ y}, 0 < y → x₁ < x₂ →
    combine_fn x₁ y < combine_fn x₂ y
  /-- Disjoint events have zero overlap -/
  disjoint_zero : ∀ {a b}, Disjoint a b → v.val (a ⊓ b) = 0
  /-- WeakRegraduation: the core linearizer from K&S Appendix A.
  This provides φ with φ(S(x,y)) = φ(x) + φ(y), calibrated to φ(0)=0, φ(1)=1. -/
  weakRegrade : WeakRegraduation combine_fn
  /-- S = + on ℚ ∩ [0,1]. This follows from associativity + the grid construction.
  Combined with weakRegrade, this derives φ = id on [0,1], hence S = +. -/
  combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
    combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ)

variable {α : Type*} [PlausibilitySpace α] [ComplementedLattice α] (v : Valuation α)

/-! ## Key Theorem: Deriving Additivity

From the Cox consistency axioms, we can PROVE that combine_fn must be addition!
This is the core of why probability is additive.
-/

/-- Basic property: S(0, x) = x follows from commutativity and identity -/
lemma combine_zero_left (hC : CoxConsistency α v) (x : ℝ) :
    hC.combine_fn 0 x = x := by
  rw [hC.combine_comm, hC.combine_zero]

/-- Basic property: S(0, 0) = 0 -/
lemma combine_zero_zero (hC : CoxConsistency α v) :
    hC.combine_fn 0 0 = 0 := by
  exact hC.combine_zero 0

/-- Rational calibration fixes the supplied combination law at valid event values. -/
theorem combine_fn_is_add (hC : CoxConsistency α v) :
    ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    hC.combine_fn x y ≤ 1 → hC.combine_fn x y = x + y := by
  intro x y hx0 hx1 hy0 hy1 hComb_le1
  have hx := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat x hx0 hx1
  have hy := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat y hy0 hy1
  have hnonneg : 0 ≤ hC.combine_fn x y := hC.weakRegrade.strictMono.le_iff_le.mp (by
    rw [hC.weakRegrade.zero, hC.weakRegrade.combine_eq_add, hx, hy]
    exact add_nonneg hx0 hy0)
  have hc := regrade_eq_id_on_unit hC.weakRegrade hC.combine_rat _ hnonneg hComb_le1
  simpa only [hc, hx, hy] using hC.weakRegrade.combine_eq_add x y

lemma combine_double (hC : CoxConsistency α v) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) (hComb_le1 : hC.combine_fn x x ≤ 1) :
    hC.combine_fn x x = 2 * x := by
  rw [combine_fn_is_add v hC x x hx0 (by linarith) hx0 (by linarith) hComb_le1]
  ring

/-! ## Supplied linear negation profile

The following record includes linearity as data. Its accessor is not a
linearity derivation. Eventwise compatibility with an additive valuation
will separately imply the complement equation on attained values.
-/

structure NegationData (α : Type*) [PlausibilitySpace α]
    [ComplementedLattice α] (v : Valuation α) where
  /-- The negation function N from Cox's theorem -/
  negate : ℝ → ℝ
  /-- Consistency: For complementary events, v(b) = N(v(a)) -/
  negate_val : ∀ a b, Disjoint a b → a ⊔ b = ⊤ →
    v.val b = negate (v.val a)
  /-- N is antitone (order-reversing) -/
  negate_antimono : Antitone negate
  /-- N(0) = 1 (complement of impossible is certain) -/
  negate_zero : negate 0 = 1
  /-- N(1) = 0 (complement of certain is impossible) -/
  negate_one : negate 1 = 0
  /-- N(N(x)) = x (involutive: complement of complement is original) -/
  negate_involutive : ∀ x, negate (negate x) = x
  /-- Regularity condition: N is continuous -/
  negate_continuous : Continuous negate
  /-- Linearity: N(x) = 1 - x on [0,1].
  This is supplied, rather than derived from the preceding regularity fields.
  Eventwise compatibility only determines values attained by the valuation. -/
  negate_linear : ∀ x, 0 ≤ x → x ≤ 1 → negate x = 1 - x

/-- Extract linearity from NegationData. -/
theorem negate_is_linear (nd : NegationData α v) :
    ∀ x, 0 ≤ x → x ≤ 1 → nd.negate x = 1 - x :=
  nd.negate_linear

/-! ### Counterexample: Involution Properties Don't Imply Linearity

The function N(x) = √(1 - x²) satisfies:
- Continuous ✓
- Antitone ✓
- Involutive: N(N(x)) = √(1 - (1-x²)) = √(x²) = |x| = x for x ∈ [0,1] ✓
- N(0) = 1, N(1) = 0 ✓

But N(1/2) = √(3/4) = √3/2 ≈ 0.866 ≠ 0.5 = 1 - 1/2.

This shows that linearity does NOT follow from these properties alone.
It DOES follow when combined with CoxConsistency (sum rule) via complement_rule.
-/

/-- The p-norm involution: N_p(x) = (1 - x^p)^{1/p} for p > 0.
For p = 1: N₁(x) = 1 - x (linear)
For p = 2: N₂(x) = √(1 - x²) (not linear)
For p → ∞: N_∞(x) → max(1-x, 0) ∨ similar -/
noncomputable def pNormInvolution (p : ℝ) (_hp : 0 < p) (x : ℝ) : ℝ :=
  (1 - x ^ p) ^ (1 / p)

/-- The p-norm involution satisfies N(0) = 1. -/
lemma pNormInvolution_zero (p : ℝ) (hp : 0 < p) :
    pNormInvolution p hp 0 = 1 := by
  simp [pNormInvolution, Real.zero_rpow (ne_of_gt hp)]

/-- The p-norm involution satisfies N(1) = 0. -/
lemma pNormInvolution_one (p : ℝ) (hp : 0 < p) :
    pNormInvolution p hp 1 = 0 := by
  simp only [pNormInvolution, Real.one_rpow, sub_self]
  exact Real.zero_rpow (one_div_ne_zero (ne_of_gt hp))

/-- The p-norm involution is involutive on [0,1]. -/
lemma pNormInvolution_involutive (p : ℝ) (hp : 0 < p) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    pNormInvolution p hp (pNormInvolution p hp x) = x := by
  simp only [pNormInvolution]
  -- First, establish that 0 ≤ 1 - x^p since x ∈ [0,1]
  have h1 : 0 ≤ 1 - x ^ p := by
    have hxp : x ^ p ≤ 1 := Real.rpow_le_one hx0 hx1 (le_of_lt hp)
    linarith
  -- Establish nonnegativity for the inner term
  have h_inner_nn : 0 ≤ (1 - x ^ p) ^ (1 / p) := Real.rpow_nonneg h1 (1 / p)
  -- Key: ((1 - x^p)^(1/p))^p = 1 - x^p using rpow_mul
  have h2 : ((1 - x ^ p) ^ (1 / p)) ^ p = 1 - x ^ p := by
    rw [← Real.rpow_mul h1]
    simp only [one_div, inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  -- Now simplify: 1 - ((1 - x^p)^(1/p))^p = x^p
  have h3 : 1 - ((1 - x ^ p) ^ (1 / p)) ^ p = x ^ p := by
    rw [h2]; ring
  -- Finally: (x^p)^(1/p) = x for x ≥ 0
  calc (1 - ((1 - x ^ p) ^ (1 / p)) ^ p) ^ (1 / p)
      = (x ^ p) ^ (1 / p) := by rw [h3]
    _ = x ^ (p * (1 / p)) := by rw [← Real.rpow_mul hx0]
    _ = x ^ (1 : ℝ) := by rw [mul_one_div_cancel (ne_of_gt hp)]
    _ = x := Real.rpow_one x

/-- The p=2 involution (√(1-x²)) is NOT linear: N(1/2) ≠ 1/2. -/
theorem involution_counterexample :
    pNormInvolution 2 (by norm_num : (0 : ℝ) < 2) (1/2) ≠ 1 - 1/2 := by
  simp only [pNormInvolution]
  -- N(1/2) = (1 - (1/2)²)^{1/2} = (3/4)^{1/2} ≈ 0.866
  -- But 1 - 1/2 = 1/2 = 0.5
  -- So we need (3/4)^(1/2) ≠ 1/2
  norm_num
  intro h
  -- If (3/4)^(1/2) = 1/2, then squaring: 3/4 = (1/2)² = 1/4, which is false
  have h_nn : (0 : ℝ) ≤ 3/4 := by norm_num
  -- Square both sides: ((3/4)^(1/2))^2 = (1/2)^2
  have h_sq : (((3 : ℝ) / 4) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = ((1 : ℝ) / 2) ^ (2 : ℕ) := by
    rw [h]
  -- Simplify LHS: ((3/4)^(1/2))^2 = 3/4 using rpow_mul
  rw [← Real.rpow_natCast (((3 : ℝ)/4)^((1:ℝ)/2)) 2, ← Real.rpow_mul h_nn] at h_sq
  simp only [one_div] at h_sq
  norm_num at h_sq

/-- Extended Cox consistency including negation function -/
structure CoxConsistencyFull (α : Type*) [PlausibilitySpace α]
    [ComplementedLattice α] (v : Valuation α) extends
    CoxConsistency α v, NegationData α v

/-- Sum rule: For disjoint events, v(a ⊔ b) = v(a) + v(b).
This is now a THEOREM, not an axiom! It follows from combine_fn_is_add.

**Key insight**: For disjoint events, S(v(a), v(b)) = v(a ⊔ b) ≤ 1,
which is exactly the bound needed to apply combine_fn_is_add. -/
theorem sum_rule (hC : CoxConsistency α v) {a b : α} (hDisj : Disjoint a b) :
    v.val (a ⊔ b) = v.val a + v.val b := by
  -- Start with the defining equation for disjoint events
  rw [hC.combine_disjoint hDisj]
  -- Apply the key theorem that combine_fn = addition
  apply combine_fn_is_add
  · exact v.nonneg a  -- 0 ≤ v(a)
  · exact v.le_one a  -- v(a) ≤ 1
  · exact v.nonneg b  -- 0 ≤ v(b)
  · exact v.le_one b  -- v(b) ≤ 1
  -- NEW: S(v(a), v(b)) = v(a ⊔ b) ≤ 1
  · rw [← hC.combine_disjoint hDisj]
    exact v.le_one (a ⊔ b)

/-- The derived event law supplies the common sum-rule valuation with identical values. -/
def CoxConsistency.toSumRuleValuation (hC : CoxConsistency α v) :
    ProbabilityTheory.Common.SumRuleValuation α where
  toNormalizedValuation := v.toNormalizedValuation
  sum_rule a b := by
    change v.val (a ⊔ b) = v.val a + v.val b - v.val (a ⊓ b)
    have h := BooleanRepresentation.modular_of_disjoint_add v.val
      (fun _ _ hd => sum_rule v hC hd) a b
    linarith

/-!
## Independence (Appendix B): direct product rule

K&S introduces a **direct product** operation between independent lattices, written `×`
at the lattice level and `⊗` at the scalar level. After Appendix A regrades `⊕` to `+`,
Appendix B shows that `⊗` must be multiplication up to a single global scale constant.

In our formalization, Appendix B is proved in two routes:

- `KnuthSkilling.Multiplicative.Main` (via the product equation)
- `KnuthSkilling.Multiplicative.DirectProof` (Lean-friendly direct route)

The lemma below is the “pipeline glue” used by `ProbabilityDerivation`:
once you have *some* scalar `tensor` used to interpret direct products of events, the
Appendix B theorem converts it into literal multiplication after normalization.
-/

namespace AppendixB

open KnuthSkilling.Literature

open _root_.KnuthSkilling.Multiplicative

variable {β γ : Type*} [PlausibilitySpace β] [PlausibilitySpace γ]

/-- Compatibility predicate: the valuation on the composite lattice uses `tensor` on the
measures of rectangle events. This is the intended reading of K&S “`x ⊗ t = m(x × t)`”. -/
def RectTensorCompatible
    {α : Type*} [PlausibilitySpace α]
    (P : Multiplicative.DirectProduct α β γ)
    (vα : Valuation α) (vβ : Valuation β) (vγ : Valuation γ)
    (tensor : Multiplicative.PosReal → Multiplicative.PosReal → Multiplicative.PosReal) : Prop :=
  ∀ a : α, ∀ b : β, ∀ ha : 0 < vα.val a, ∀ hb : 0 < vβ.val b,
    vγ.val (P.prod a b) = ((tensor ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩ : Multiplicative.PosReal) : ℝ)

/-- Appendix B consequence: any `tensor` satisfying the Independence axioms is multiplication
up to a global scale, hence the measure of rectangle events obeys the direct-product rule. -/
theorem directProduct_rule_mul_div_const
    {α : Type*} [PlausibilitySpace α]
    (P : Multiplicative.DirectProduct α β γ)
    (vα : Valuation α) (vβ : Valuation β) (vγ : Valuation γ)
    {tensor : Multiplicative.PosReal → Multiplicative.PosReal → Multiplicative.PosReal}
    (hAssoc : ∀ u v w : Multiplicative.PosReal,
      tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : Multiplicative.DistributesOverAdd tensor)
    (hCommOne : ∀ t : Multiplicative.PosReal,
      tensor Multiplicative.onePos t = tensor t Multiplicative.onePos)
    (hCompat : RectTensorCompatible (β := β) (γ := γ) P vα vβ vγ tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : α, ∀ b : β, 0 < vα.val a → 0 < vβ.val b →
        vγ.val (P.prod a b) = (vα.val a * vβ.val b) / C := by
  rcases Multiplicative.tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm_one
      (tensor := tensor) hAssoc hDistrib hCommOne with ⟨C, hC, hMul⟩
  refine ⟨C, hC, ?_⟩
  intro a b ha hb
  have hRect : vγ.val (P.prod a b) =
      ((tensor ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩ : Multiplicative.PosReal) : ℝ) :=
    hCompat a b ha hb
  -- Replace `tensor` by multiplication (up to `C`) via Appendix B.
  calc
    vγ.val (P.prod a b)
        = ((tensor ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩ : Multiplicative.PosReal) : ℝ) := hRect
    _ = ((vα.val a) * (vβ.val b)) / C := by
        simpa using hMul ⟨vα.val a, ha⟩ ⟨vβ.val b, hb⟩

end AppendixB

/-- Product rule: v(a ⊓ b) = v(a|b) · v(b) follows from definition of condVal -/
theorem product_rule_ks (_hC : CoxConsistency α v) (a b : α) (hB : v.val b ≠ 0) :
    v.val (a ⊓ b) = Valuation.condVal v a b * v.val b := by
  calc
    v.val (a ⊓ b) = (v.val (a ⊓ b) / v.val b) * v.val b := by field_simp [hB]
    _ = Valuation.condVal v a b * v.val b := by simp [Valuation.condVal, hB]

/-- **Bayes' Theorem** (derived from symmetry).

The product rule gives: v(a ⊓ b) = v(a|b) · v(b).
Since a ⊓ b = b ⊓ a (commutativity of lattice meet), we also have:
v(b ⊓ a) = v(b|a) · v(a).

Therefore: v(a|b) · v(b) = v(b|a) · v(a), which rearranges to:
**v(a|b) = v(b|a) · v(a) / v(b)**

This is the "Fundamental Theorem of Rational Inference" (Eq. 20 in Skilling-Knuth).
Bayesian inference isn't an "interpretation" — it's a mathematical necessity once
you accept the symmetry of conjunction (A ∧ B = B ∧ A).
-/
theorem bayes_theorem_ks (_hC : CoxConsistency α v) (a b : α)
    (ha : v.val a ≠ 0) (hb : v.val b ≠ 0) :
    Valuation.condVal v a b = Valuation.condVal v b a * v.val a / v.val b := by
  -- Expand conditional probability definitions
  simp only [Valuation.condVal, ha, hb, dite_false]
  -- Use commutativity: a ⊓ b = b ⊓ a
  rw [inf_comm]
  -- Field algebra: v(a ⊓ b)/v(b) = (v(a ⊓ b)/v(a)) · v(a)/v(b)
  field_simp

/-- Complement rule: For any element a, if b is its complement (disjoint and a ⊔ b = ⊤),
then v(b) = 1 - v(a). -/
theorem complement_rule (hC : CoxConsistency α v) (a b : α)
    (h_disj : Disjoint a b) (h_top : a ⊔ b = ⊤) :
    v.val b = 1 - v.val a := by
  have h1 : v.val (a ⊔ b) = v.val a + v.val b := sum_rule v hC h_disj
  rw [h_top, v.val_top] at h1
  linarith

/-- Compatibility determines complement values without assuming linearity of the scalar map. -/
theorem negate_on_attained (hC : CoxConsistency α v) (N : ℝ → ℝ)
    (hN : ∀ a b, Disjoint a b → a ⊔ b = ⊤ → v.val b = N (v.val a))
    (a b : α) (h_disj : Disjoint a b) (h_top : a ⊔ b = ⊤) :
    N (v.val a) = 1 - v.val a := by
  rw [← hN a b h_disj h_top, complement_rule v hC a b h_disj h_top]

/-- Historical linear-profile interface, obtained from event compatibility alone. -/
theorem negate_linear_from_cox (hCF : CoxConsistencyFull α v)
    (a b : α) (h_disj : Disjoint a b) (h_top : a ⊔ b = ⊤) :
    hCF.negate (v.val a) = 1 - v.val a :=
  negate_on_attained v hCF.toCoxConsistency hCF.negate hCF.negate_val a b h_disj h_top

end KnuthSkilling.Probability
