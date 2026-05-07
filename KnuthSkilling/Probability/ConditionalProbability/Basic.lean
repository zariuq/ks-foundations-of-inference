import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.ENNReal.Basic
import KnuthSkilling.Core.Basic
import KnuthSkilling.Multiplicative

/-!
# K&S Section 7: Conditional Probability via Chaining Associativity (Axiom 5)

**IMPORTANT**: For canonical probability calculus results (Bayes' theorem, product rule, etc.),
use `ProbabilityCalculus.lean` which provides the single source of truth. This file contains
the lattice-theoretic `Bivaluation` formalism from K&S Section 7, which is complementary
to (not a replacement for) the main derivation.

**Architecture**:
- `ProbabilityCalculus.lean`: Canonical interface for end-results (use this!)
- `Probability/ProbabilityDerivation.lean`: Main K&S derivation (provides the canonical implementation)
- This file: K&S Section 7's `Bivaluation` + `ChainingAssociativity` formalism

The theorems in this file (e.g., `bayesTheorem`, `productRule`) are specific to the
`Bivaluation` structure and demonstrate how Section 7's framework derives the same
results. For general use, prefer `ProbabilityCalculus.sumRule`, etc.

This file uses `DirectProof.lean` for the Appendix B result, which is an alternative
proof technique (not a different axiom system) that avoids "apply Appendix A again".

## The Story

K&S derives conditional probability `p(x|t)` as a **bivaluation** - a function taking pairs of
lattice elements to reals. The key axiom is:

**Axiom 5 (Chaining Associativity)**: For chains `a < b < c < d`:
```
(p(a|b) ⊙ p(b|c)) ⊙ p(c|d) = p(a|b) ⊙ (p(b|c) ⊙ p(c|d))
```

Combined with the sum rule (from Appendix A), this gives the **same product equation** as
Appendix B! The solution (Θ = log, ⊙ = multiplication) yields:

**Chain-Product Rule**: `p(x|z) = p(x|y) · p(y|z)`

From this, K&S derives:
- Bayes' Theorem: `Pr(x|θ) · Pr(θ) = Pr(θ|x) · Pr(x)`
- Probability as ratio: `Pr(x|t) = m(x ∧ t) / m(t)`

## Main Results

- `ChainingAssociativity`: Axiom 5 as a typeclass
- `chainProductRule`: `p(a|c) = p(a|b) · p(b|c)` for chains
- `bayesTheorem`: From commutativity of ∧
- `prob_eq_measure_ratio`: `Pr(x|t) = m(x ∧ t) / m(t)`

## References

- K&S "Foundations of Inference" (2012), Section 7 "Probability Calculus"
- Especially Section 7.1 "Chained Arguments"
-/

namespace KnuthSkilling.Probability.ConditionalProbability

open Classical
open KnuthSkilling.Multiplicative

/-! ## Bivaluation: Conditional Plausibility -/

/-- A **bivaluation** assigns a real number to pairs of lattice elements.
This represents conditional plausibility `p(x|t)` - the plausibility of `x` given context `t`.

K&S requires:
- Positivity: `p(x|t) > 0` when `⊥ < x ≤ t`
- Sum rule in first argument: `p(x ⊔ y|t) = p(x|t) + p(y|t)` for disjoint `x, y`
-/
structure Bivaluation (α : Type*) [Lattice α] [BoundedOrder α] where
  /-- The bivaluation function `p(x|t)` -/
  p : α → α → ℝ
  /-- Positivity: plausibility is positive for non-bottom elements within context -/
  p_pos : ∀ x t : α, ⊥ < x → x ≤ t → 0 < p x t
  /-- Sum rule: additive on disjoint joins in the first argument -/
  p_sum_disjoint : ∀ x y t : α, Disjoint x y → x ⊔ y ≤ t →
    p (x ⊔ y) t = p x t + p y t
  /-- Monotonicity in first argument -/
  p_mono_left : ∀ x y t : α, x ≤ y → y ≤ t → p x t ≤ p y t
  /-- Context intersection: p(x|t) only depends on x ∩ t.
  This is implicit in K&S: "the plausibility of x given t" is really "the plausibility
  of x ∧ t given t". -/
  p_context : ∀ x t : α, p x t = p (x ⊓ t) t

namespace Bivaluation

variable {α : Type*} [Lattice α] [BoundedOrder α] (B : Bivaluation α)

/-- The plausibility of bottom is 0 -/
theorem p_bot (t : α) (ht : ⊥ < t) : B.p ⊥ t = 0 := by
  -- From sum rule: p(⊥ ⊔ ⊥|t) = p(⊥|t) + p(⊥|t)
  -- But ⊥ ⊔ ⊥ = ⊥, so p(⊥|t) = 2 · p(⊥|t)
  -- Hence p(⊥|t) = 0
  have h : B.p (⊥ ⊔ ⊥) t = B.p ⊥ t + B.p ⊥ t := by
    apply B.p_sum_disjoint
    · exact disjoint_bot_left
    · simp [le_of_lt ht]
  simp at h
  linarith

/-- Notation for bivaluation -/
scoped notation "𝕡[" B "](" x " | " t ")" => Bivaluation.p B x t

end Bivaluation

/-! ## Chaining Operation

For a chain `a < b < c`, K&S defines the chaining operation ⊙ implicitly via:
`p(a|c) = p(a|b) ⊙ p(b|c)`

Axiom 5 says this operation is associative.
-/

/-- The **chaining operation** combines conditional plausibilities along a chain.

For `a ≤ b ≤ c`, we have `p(a|c) = p(a|b) ⊙ p(b|c)` where ⊙ is this operation.

K&S proves (via the product equation) that ⊙ must be multiplication (up to scale).
-/
structure ChainingOp where
  /-- The binary operation on plausibilities -/
  chain : ℝ → ℝ → ℝ
  /-- Associativity (Axiom 5) -/
  chain_assoc : ∀ x y z : ℝ, chain (chain x y) z = chain x (chain y z)
  /-- Strict monotonicity (from order preservation) -/
  chain_strictMono_left : ∀ z : ℝ, 0 < z → StrictMono (fun x => chain x z)
  chain_strictMono_right : ∀ x : ℝ, 0 < x → StrictMono (fun z => chain x z)
  /-- Positivity preservation -/
  chain_pos : ∀ x y : ℝ, 0 < x → 0 < y → 0 < chain x y
  /-- Left-distributivity over addition (from sum rule + chain rule interaction).
  This says: chain(a, t) + chain(b, t) = chain(a + b, t).

  **Derivation from K&S**: At context s, the sum rule gives p(x⊔y|s) = p(x|s) + p(y|s).
  By chain rule: p(x|s) = chain(p(x|t), p(t|s)) for intermediate t.
  Combining: chain(p(x|t), p(t|s)) + chain(p(y|t), p(t|s)) = chain(p(x|t)+p(y|t), p(t|s)).
  -/
  chain_distrib_left : ∀ a b t : ℝ, 0 < a → 0 < b → 0 < t →
    chain a t + chain b t = chain (a + b) t

namespace ChainingOp

/-! ## Applying Appendix B to the chaining operation

K&S Axiom 5 provides an associative chaining operation `⊙` on positive reals.
Combining it with the sum rule forces left-distributivity over addition.

This is exactly the Appendix B setup: any `tensor : (0,∞) → (0,∞) → (0,∞)` that is
associative and distributive over `+` must be multiplication up to a global scale.

We implement the bridge by turning `chain : ℝ → ℝ → ℝ` into a `PosReal → PosReal → PosReal`,
then invoking `Multiplicative.tensor_coe_eq_mul_div_const_of_tensorRegularity`. -/

/-- The chaining operation restricted to positive reals as a `PosReal` tensor. -/
noncomputable def tensor (C : ChainingOp) : PosReal → PosReal → PosReal :=
  fun x y =>
    ⟨C.chain (x : ℝ) (y : ℝ), C.chain_pos (x : ℝ) (y : ℝ) x.2 y.2⟩

@[simp] theorem coe_tensor (C : ChainingOp) (x y : PosReal) :
    ((tensor C x y : PosReal) : ℝ) = C.chain (x : ℝ) (y : ℝ) :=
  rfl

theorem tensor_assoc (C : ChainingOp) (u v w : PosReal) :
    tensor C (tensor C u v) w = tensor C u (tensor C v w) := by
  ext
  simp [tensor, C.chain_assoc]

theorem tensor_distributesOverAdd (C : ChainingOp) : DistributesOverAdd (tensor C) := by
  intro x y t
  ext
  -- `chain (x+y) t = chain x t + chain y t`
  simpa [tensor, addPos, add_comm, add_left_comm, add_assoc] using
    (C.chain_distrib_left (x : ℝ) (y : ℝ) (t : ℝ) x.2 y.2 t.2).symm

theorem tensor_inj_kPos (C : ChainingOp) : Function.Injective (fun t : PosReal => tensor C onePos t) := by
  intro t₁ t₂ ht
  have ht' :
      C.chain (1 : ℝ) (t₁ : ℝ) = C.chain (1 : ℝ) (t₂ : ℝ) := by
    have := congrArg (fun z : PosReal => (z : ℝ)) ht
    simpa [tensor, onePos] using this
  have hinj : Function.Injective (fun z : ℝ => C.chain (1 : ℝ) z) :=
    (C.chain_strictMono_right (1 : ℝ) (by norm_num)).injective
  have hcoe : (t₁ : ℝ) = (t₂ : ℝ) := hinj ht'
  exact Subtype.ext (by simpa using hcoe)

theorem tensor_regular (C : ChainingOp) : TensorRegularity (tensor C) :=
  ⟨fun u v w => tensor_assoc C u v w, tensor_inj_kPos C⟩

/-- Appendix B applied to chaining: the operation is scaled multiplication on `(0,∞)`. -/
theorem chain_eq_mul_div_const (C : ChainingOp) :
    ∃ K : ℝ, 0 < K ∧
      ∀ x y : ℝ, 0 < x → 0 < y → C.chain x y = (x * y) / K := by
  rcases tensor_coe_eq_mul_div_const_of_tensorRegularity
      (tensor := tensor C) (tensor_regular C) (tensor_distributesOverAdd C) with
    ⟨K, hK, h⟩
  refine ⟨K, hK, ?_⟩
  intro x y hx hy
  have := h ⟨x, hx⟩ ⟨y, hy⟩
  simpa [tensor] using this

end ChainingOp

/-! ## Axiom 5: Chaining Associativity

K&S's Axiom 5 states that chaining conditional plausibilities is associative.
Combined with the sum rule, this forces the chaining operation to be multiplication.
-/

/-- **Axiom 5 (Chaining Associativity)**: A bivaluation satisfies chaining associativity
if there exists a chaining operation ⊙ such that:

1. For chains `a ≤ b ≤ c`: `p(a|c) = p(a|b) ⊙ p(b|c)`
2. The operation ⊙ is associative
3. The sum rule interacts correctly with chaining
-/
class ChainingAssociativity (α : Type*) [Lattice α] [BoundedOrder α]
    (B : Bivaluation α) where
  /-- The chaining operation -/
  chainOp : ChainingOp
  /-- Chain rule: `p(a|c) = p(a|b) ⊙ p(b|c)` for `a ≤ b ≤ c` -/
  chain_rule : ∀ a b c : α, a ≤ b → b ≤ c → ⊥ < a →
    B.p a c = chainOp.chain (B.p a b) (B.p b c)

/-! ## The Product Equation Reappears

K&S's key observation: combining the sum rule with chaining associativity gives
the SAME product equation as Appendix B!

If we define Θ such that chaining becomes addition under Θ, then:
- `Θ(p(a|c)) = Θ(p(a|b)) + Θ(p(b|c))`

Substituting into the sum rule term by term yields:
- `Ψ(ζ(ξ,η) + τ) = Ψ(ξ + τ) + Ψ(η + τ)`

where Ψ = Θ⁻¹. This is exactly the Appendix B product equation!
-/

/-- The chaining operation, combined with the sum rule, satisfies the product equation.

**KEY THEOREM**: This establishes the conceptual link between K&S Section 7 (conditional
probability via Axiom 5) and Appendix B (product equation → exponential).

K&S's key insight: The SAME functional equation (ProductEquation) that arises from
distributivity in Appendix B ALSO arises from chaining + sum rule in Section 7!

The product equation is: `Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ,η))`
where Ψ = Θ⁻¹ and ζ(ξ,η) = Θ(Ψ(ξ) + Ψ(η)) encodes the sum rule.

**Proof strategy**:
- Let a = Ψ(ξ), b = Ψ(η), t = Ψ(τ)
- By hΘ_chain: Ψ(Θ(x) + Θ(y)) = chain(x, y)
- So Ψ(τ + ξ) = chain(a, t) and Ψ(τ + η) = chain(b, t)
- By distributivity: chain(a,t) + chain(b,t) = chain(a+b, t)
- And Ψ(τ + ζ(ξ,η)) = Ψ(Θ(t) + Θ(a+b)) = chain(a+b, t)
- Hence LHS = RHS ∎
-/
theorem chaining_gives_productEquation
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (_B : Bivaluation α) [CA : ChainingAssociativity α _B]
    (Θ : ℝ → ℝ)
    (hΘ_chain : ∀ x y : ℝ, 0 < x → 0 < y →
      Θ (CA.chainOp.chain x y) = Θ x + Θ y)
    -- Ψ = Θ⁻¹ (exists by bijectivity)
    (Ψ : ℝ → ℝ) (hΨΘ : ∀ x, Ψ (Θ x) = x) (hΘΨ : ∀ r, Θ (Ψ r) = r)
    -- Additional hypothesis: Ψ maps to positive reals (true when Θ = A·log)
    (hΨ_pos : ∀ r : ℝ, 0 < Ψ r) :
    ∃ (Ψ' : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ),
      (∀ x, Ψ' (Θ x) = x) ∧
      Multiplicative.ProductEquation Ψ' ζ := by
  -- Step 1: Use the given Ψ = Θ⁻¹
  -- Step 2: Construct ζ(ξ,η) = Θ(Ψ(ξ) + Ψ(η))
  let ζ : ℝ → ℝ → ℝ := fun ξ η => Θ (Ψ ξ + Ψ η)

  -- Step 3: Verify ProductEquation
  refine ⟨Ψ, ζ, hΨΘ, ?_⟩
  intro τ ξ η

  -- Let a = Ψ(ξ), b = Ψ(η), t = Ψ(τ)
  set a := Ψ ξ with ha_def
  set b := Ψ η with hb_def
  set t := Ψ τ with ht_def

  -- Positivity (from hΨ_pos)
  have ha : 0 < a := hΨ_pos ξ
  have hb : 0 < b := hΨ_pos η
  have ht : 0 < t := hΨ_pos τ
  have hab : 0 < a + b := add_pos ha hb

  -- Key: Ψ(Θ(x) + Θ(y)) = chain(x, y) for positive x, y
  have hΨ_chain : ∀ x y : ℝ, 0 < x → 0 < y →
      Ψ (Θ x + Θ y) = CA.chainOp.chain x y := fun x y hx hy => by
    have h := hΘ_chain x y hx hy
    rw [← h, hΨΘ]

  -- Compute LHS pieces
  -- τ + ξ = Θ(Ψ τ) + Θ(Ψ ξ) = Θ t + Θ a, so Ψ(τ + ξ) = Ψ(Θ t + Θ a) = chain(a, t)
  have hLHS1 : Ψ (τ + ξ) = CA.chainOp.chain a t := by
    have h_eq : τ + ξ = Θ t + Θ a := by
      simp only [ht_def, ha_def, hΘΨ]
    rw [h_eq, add_comm (Θ t) (Θ a)]
    exact hΨ_chain a t ha ht

  have hLHS2 : Ψ (τ + η) = CA.chainOp.chain b t := by
    have h_eq : τ + η = Θ t + Θ b := by
      simp only [ht_def, hb_def, hΘΨ]
    rw [h_eq, add_comm (Θ t) (Θ b)]
    exact hΨ_chain b t hb ht

  -- Distributivity: chain(a,t) + chain(b,t) = chain(a+b, t)
  have hDistrib : CA.chainOp.chain a t + CA.chainOp.chain b t =
      CA.chainOp.chain (a + b) t :=
    CA.chainOp.chain_distrib_left a b t ha hb ht

  -- Compute RHS
  -- ζ(ξ,η) = Θ(Ψ ξ + Ψ η) = Θ(a + b)
  -- τ + ζ(ξ,η) = Θ(Ψ τ) + Θ(a+b) = Θ t + Θ(a+b)
  -- So Ψ(τ + ζ(ξ,η)) = Ψ(Θ t + Θ(a+b)) = chain(a+b, t)
  have hRHS : Ψ (τ + ζ ξ η) = CA.chainOp.chain (a + b) t := by
    show Ψ (τ + Θ (Ψ ξ + Ψ η)) = _
    have h1 : τ + Θ (Ψ ξ + Ψ η) = Θ t + Θ (a + b) := by
      simp only [ha_def, hb_def, ht_def, hΘΨ]
    rw [h1, add_comm (Θ t) (Θ (a + b))]
    exact hΨ_chain (a + b) t hab ht

  -- Combine
  rw [hLHS1, hLHS2, hDistrib, hRHS]

/-! ## Main Theorem: Chain-Product Rule

By Appendix B, the product equation forces Θ = A·log for some A.
Hence the chaining operation ⊙ is multiplication (up to scale C).

Setting C = 1 (normalization), we get the **chain-product rule**:
`p(x|z) = p(x|y) · p(y|z)`
-/

/-- **Chain-Product Rule**: For chains `a ≤ b ≤ c`, conditional probability multiplies:
`Pr(a|c) = Pr(a|b) · Pr(b|c)`

This is derived from Axiom 5 via the Appendix B solution to the product equation.
-/
theorem chainProductRule
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α) [CA : ChainingAssociativity α B]
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1) :
    ∀ a b c : α, a ≤ b → b ≤ c → ⊥ < a →
      B.p a c = B.p a b * B.p b c := by
  intro a b c hab hbc ha_pos
  -- Appendix B gives: chain(x,y) = (x*y)/K for some global K>0.
  rcases ChainingOp.chain_eq_mul_div_const CA.chainOp with ⟨K, hK, hchain⟩
  -- Use normalization + chaining at (a,a,a) to force K = 1.
  have hId : (1 : ℝ) = CA.chainOp.chain (1 : ℝ) (1 : ℝ) := by
    have hAA : B.p a a = CA.chainOp.chain (B.p a a) (B.p a a) := by
      simpa using (CA.chain_rule a a a (le_rfl) (le_rfl) ha_pos)
    have hNorm : B.p a a = 1 := hNormalized a ha_pos
    simpa [hNorm] using hAA
  have hK_eq : K = 1 := by
    have hchain11 : CA.chainOp.chain (1 : ℝ) (1 : ℝ) = (1 : ℝ) / K := by
      simpa using (hchain 1 1 (by norm_num) (by norm_num))
    have hne : (K : ℝ) ≠ 0 := ne_of_gt hK
    -- From `1 = 1/K` get `K = 1`.
    have : (1 : ℝ) = (1 : ℝ) / K := by simpa [hchain11] using hId
    field_simp [hne] at this
    linarith

  -- Now apply the chain rule and rewrite the chain operation to multiplication.
  have hb_pos : ⊥ < b := lt_of_lt_of_le ha_pos hab
  have hPab : 0 < B.p a b := B.p_pos a b ha_pos hab
  have hPbc : 0 < B.p b c := B.p_pos b c hb_pos hbc
  calc
    B.p a c = CA.chainOp.chain (B.p a b) (B.p b c) := by
      simpa using (CA.chain_rule a b c hab hbc ha_pos)
    _ = (B.p a b * B.p b c) / K := hchain (B.p a b) (B.p b c) hPab hPbc
    _ = B.p a b * B.p b c := by simp [hK_eq]

/-! ## K&S Product Rule (7.5)

The product rule from K&S Section 7.1:
`p(x ∧ y | z) = p(x | y) · p(y | z)` when `y ≤ z`

This combines the chain rule with the context intersection axiom.
-/

/-- **K&S Product Rule (7.5)**: `p(x ⊓ y | z) = p(x | y) · p(y | z)` when `y ≤ z`.

Proof: By the chain rule, p(x ⊓ y | z) = p(x ⊓ y | y) · p(y | z) since x ⊓ y ≤ y ≤ z.
By p_context, p(x | y) = p(x ⊓ y | y). Combining gives the result.
-/
theorem productRule
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α) [CA : ChainingAssociativity α B]
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (x y z : α) (hxy_pos : ⊥ < x ⊓ y) (hyz : y ≤ z) (_hy_pos : ⊥ < y) :
    B.p (x ⊓ y) z = B.p x y * B.p y z := by
  -- Step 1: x ⊓ y ≤ y ≤ z, so chain rule applies
  have hxy_le_y : x ⊓ y ≤ y := inf_le_right
  -- Step 2: Apply chain rule
  have h_chain := chainProductRule B hNormalized (x ⊓ y) y z hxy_le_y hyz hxy_pos
  -- Step 3: By p_context, p(x | y) = p(x ⊓ y | y)
  have h_ctx : B.p x y = B.p (x ⊓ y) y := B.p_context x y
  -- Combine
  rw [h_chain, ← h_ctx]

/-! ## Bayes' Theorem

From the product rule and commutativity of ⊓, K&S derives Bayes' theorem:
`Pr(x|θ) · Pr(θ|t) = Pr(θ|x) · Pr(x|t)` when `x, θ ≤ t`

Or equivalently: `Pr(x ⊓ θ|t) = Pr(x|θ) · Pr(θ|t) = Pr(θ|x) · Pr(x|t)`
-/

/-- **Bayes' Theorem**: From commutativity of ⊓ and the product rule.

Both sides equal `p(x ⊓ θ | t)`:
- LHS: `p(x | θ) · p(θ | t) = p(x ⊓ θ | t)` by product rule
- RHS: `p(θ | x) · p(x | t) = p(θ ⊓ x | t) = p(x ⊓ θ | t)` by product rule + commutativity
-/
theorem bayesTheorem
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α) [CA : ChainingAssociativity α B]
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (x θ t : α) (hxθ_pos : ⊥ < x ⊓ θ) (hx : x ≤ t) (hθ : θ ≤ t)
    (hx_pos : ⊥ < x) (hθ_pos : ⊥ < θ) :
    B.p x θ * B.p θ t = B.p θ x * B.p x t := by
  -- LHS = p(x ⊓ θ | t) by product rule
  have hLHS : B.p x θ * B.p θ t = B.p (x ⊓ θ) t := by
    rw [productRule B hNormalized x θ t hxθ_pos hθ hθ_pos]
  -- RHS = p(θ ⊓ x | t) by product rule
  have hθx_pos : ⊥ < θ ⊓ x := by rw [inf_comm θ x]; exact hxθ_pos
  have hRHS : B.p θ x * B.p x t = B.p (θ ⊓ x) t := by
    rw [productRule B hNormalized θ x t hθx_pos hx hx_pos]
  -- x ⊓ θ = θ ⊓ x by commutativity
  have h_comm : x ⊓ θ = θ ⊓ x := inf_comm x θ
  -- Combine
  rw [hLHS, hRHS, h_comm]

/-! ## Probability as Ratio of Measures

The culmination of K&S Section 7: probability is a ratio of measures.

`Pr(x|t) = m(x ∧ t) / m(t)`

This subsumes the sum rule, chain-product rule, and range [0,1].
-/

/-- The **unconditional measure** induced by a bivaluation: `m(x) := p(x|⊤)`. -/
noncomputable def baseMeasure
    {α : Type*} [Lattice α] [BoundedOrder α]
    (B : Bivaluation α) : α → ℝ :=
  fun x => B.p x ⊤

/-! ### Measure Properties of baseMeasure

We prove that `baseMeasure` satisfies the standard measure axioms:
1. `baseMeasure_bot`: m(⊥) = 0
2. `baseMeasure_additive`: m(x ⊔ y) = m(x) + m(y) for disjoint x, y
3. `baseMeasure_pos`: ⊥ < x → 0 < m(x)
4. `baseMeasure_mono`: x ≤ y → m(x) ≤ m(y)
5. `baseMeasure_nonneg`: 0 ≤ m(x)
-/

namespace baseMeasure

variable {α : Type*} [Lattice α] [BoundedOrder α] (B : Bivaluation α)

/-- The measure of bottom is zero: m(⊥) = 0.

This is the first measure axiom, following from the bivaluation's p_bot property. -/
theorem bot (hTop : (⊤ : α) ≠ ⊥) : baseMeasure B ⊥ = 0 := by
  have htop : ⊥ < (⊤ : α) := bot_lt_iff_ne_bot.mpr hTop
  exact B.p_bot ⊤ htop

/-- Finite additivity: m(x ⊔ y) = m(x) + m(y) for disjoint x, y.

This is the second measure axiom (finite additivity version). -/
theorem additive (x y : α) (hDisj : Disjoint x y) :
    baseMeasure B (x ⊔ y) = baseMeasure B x + baseMeasure B y := by
  exact B.p_sum_disjoint x y ⊤ hDisj le_top

/-- Strict positivity: m(x) > 0 when ⊥ < x. -/
theorem pos (x : α) (hx : ⊥ < x) : 0 < baseMeasure B x := by
  exact B.p_pos x ⊤ hx le_top

/-- Monotonicity: x ≤ y → m(x) ≤ m(y). -/
theorem mono (x y : α) (hxy : x ≤ y) : baseMeasure B x ≤ baseMeasure B y := by
  exact B.p_mono_left x y ⊤ hxy le_top

/-- Non-negativity: 0 ≤ m(x) for all x.

This follows from positivity for non-bottom elements and m(⊥) = 0. -/
theorem nonneg (hTop : (⊤ : α) ≠ ⊥) (x : α) : 0 ≤ baseMeasure B x := by
  by_cases hx : x = ⊥
  · rw [hx, bot B hTop]
  · exact le_of_lt (pos B x (bot_lt_iff_ne_bot.mpr hx))

/-- The measure is bounded above by m(⊤). -/
theorem le_measure_top (x : α) : baseMeasure B x ≤ baseMeasure B ⊤ := by
  exact mono B x ⊤ le_top

/-- For normalized bivaluations (p(t|t) = 1), we have m(⊤) = 1.

This makes baseMeasure a probability measure on the lattice. -/
theorem top_eq_one (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1) (hTop : (⊤ : α) ≠ ⊥) :
    baseMeasure B ⊤ = 1 := by
  have htop : ⊥ < (⊤ : α) := bot_lt_iff_ne_bot.mpr hTop
  calc baseMeasure B ⊤ = B.p ⊤ ⊤ := rfl
    _ = 1 := hNormalized ⊤ htop

/-- For normalized bivaluations, baseMeasure is bounded in [0, 1]. -/
theorem bounded (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1) (hTop : (⊤ : α) ≠ ⊥) (x : α) :
    0 ≤ baseMeasure B x ∧ baseMeasure B x ≤ 1 := by
  constructor
  · exact nonneg B hTop x
  · calc baseMeasure B x ≤ baseMeasure B ⊤ := le_measure_top B x
      _ = 1 := top_eq_one B hNormalized hTop

end baseMeasure

/-! ### Connection to Mathlib Measure Theory

For finite Boolean algebras, `baseMeasure` induces a proper `MeasureTheory.Measure`.
The key insight is that:
1. A finite Boolean algebra is a σ-algebra (all subsets are measurable)
2. Finite additivity = σ-additivity for finite types
3. baseMeasure ≥ 0 and baseMeasure(⊥) = 0

We construct the measure via ENNReal (extended non-negative reals). -/

section MeasureAxioms

/-! ### baseMeasure Satisfies Measure Axioms

We prove that `baseMeasure` satisfies all standard measure axioms,
making it a finitely additive probability measure on the lattice.

For finite Boolean algebras, finite additivity is equivalent to σ-additivity,
so this is a bona fide probability measure. For infinite lattices, K&S only
guarantees finite additivity (extending to σ-additivity would require
additional continuity assumptions not present in the K&S framework). -/

variable {α : Type*} [BooleanAlgebra α] (B : Bivaluation α)

/-- **Main Theorem**: baseMeasure satisfies all measure axioms.

This theorem states that baseMeasure from a normalized Bivaluation satisfies:
1. m(⊥) = 0 (empty set has measure zero)
2. Finite additivity: m(x ⊔ y) = m(x) + m(y) for disjoint x, y
3. Non-negativity: 0 ≤ m(x)
4. Normalization: m(⊤) = 1 (probability measure)

For finite Boolean algebras, finite additivity is equivalent to σ-additivity,
so this is a bona fide probability measure. -/
theorem baseMeasure_satisfies_measure_axioms
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (hTop : (⊤ : α) ≠ ⊥) :
    -- Axiom 1: Empty set has measure zero
    baseMeasure B ⊥ = 0 ∧
    -- Axiom 2: Finite additivity (which equals σ-additivity for finite sets)
    (∀ x y : α, Disjoint x y → baseMeasure B (x ⊔ y) = baseMeasure B x + baseMeasure B y) ∧
    -- Axiom 3: Non-negativity
    (∀ x : α, 0 ≤ baseMeasure B x) ∧
    -- Axiom 4: Bounded (probability measure property)
    baseMeasure B ⊤ = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact baseMeasure.bot B hTop
  · intro x y hDisj
    exact baseMeasure.additive B x y hDisj
  · intro x
    exact baseMeasure.nonneg B hTop x
  · exact baseMeasure.top_eq_one B hNormalized hTop

/-- The inclusion-exclusion formula for baseMeasure in Boolean algebras.

This is the measure-theoretic version of the general sum rule:
m(x ∪ y) + m(x ∩ y) = m(x) + m(y)

which rearranges to the familiar:
m(x ∪ y) = m(x) + m(y) - m(x ∩ y)

**Note**: This is proven directly here using the bivaluation axioms.
The general `sumRule_general` theorem (proven later in this file) also gives this. -/
theorem baseMeasure_inclusion_exclusion
    (x y : α) :
    baseMeasure B (x ⊔ y) + baseMeasure B (x ⊓ y) = baseMeasure B x + baseMeasure B y := by
  -- Reduce to context ⊤ via baseMeasure definition
  unfold baseMeasure
  -- Decompose x = (x ⊓ yᶜ) ⊔ (x ⊓ y) (disjoint union)
  have hdecomp_x : (x ⊓ yᶜ) ⊔ (x ⊓ y) = x := by
    calc (x ⊓ yᶜ) ⊔ (x ⊓ y) = x ⊓ (yᶜ ⊔ y) := by rw [← inf_sup_left]
      _ = x ⊓ ⊤ := by simp
      _ = x := by simp
  have hdisj_x : Disjoint (x ⊓ yᶜ) (x ⊓ y) := by
    rw [disjoint_iff]
    calc (x ⊓ yᶜ) ⊓ (x ⊓ y) = x ⊓ (yᶜ ⊓ y) := by simp [inf_left_comm, inf_comm]
      _ = ⊥ := by simp
  have hle_x : (x ⊓ yᶜ) ⊔ (x ⊓ y) ≤ (⊤ : α) := le_top
  have hadd_x : B.p x ⊤ = B.p (x ⊓ yᶜ) ⊤ + B.p (x ⊓ y) ⊤ := by
    have h := B.p_sum_disjoint (x ⊓ yᶜ) (x ⊓ y) ⊤ hdisj_x hle_x
    rw [hdecomp_x] at h
    exact h
  -- Similarly decompose x ⊔ y = (x ⊓ yᶜ) ⊔ y
  have hjoin_sup : (x ⊓ yᶜ) ⊔ y = x ⊔ y := by
    apply le_antisymm
    · exact sup_le (le_trans inf_le_left le_sup_left) le_sup_right
    · refine sup_le ?_ le_sup_right
      calc x = (x ⊓ yᶜ) ⊔ (x ⊓ y) := hdecomp_x.symm
        _ ≤ (x ⊓ yᶜ) ⊔ y := sup_le le_sup_left (le_trans inf_le_right le_sup_right)
  have hdisj_sup : Disjoint (x ⊓ yᶜ) y := by
    rw [disjoint_iff]
    calc (x ⊓ yᶜ) ⊓ y = x ⊓ (yᶜ ⊓ y) := by simp [inf_left_comm, inf_comm]
      _ = ⊥ := by simp
  have hle_sup : (x ⊓ yᶜ) ⊔ y ≤ (⊤ : α) := le_top
  have hadd_sup : B.p (x ⊔ y) ⊤ = B.p (x ⊓ yᶜ) ⊤ + B.p y ⊤ := by
    have h := B.p_sum_disjoint (x ⊓ yᶜ) y ⊤ hdisj_sup hle_sup
    rw [hjoin_sup] at h
    exact h
  -- Combine: (x⊔y) + (x⊓y) = (x⊓yᶜ) + y + (x⊓y) = (x⊓yᶜ) + (x⊓y) + y = x + y
  linarith

/-- Complement rule for baseMeasure: m(xᶜ) = m(⊤) - m(x).

For normalized measures where m(⊤) = 1, this gives m(xᶜ) = 1 - m(x). -/
theorem baseMeasure_compl
    (_hTop : (⊤ : α) ≠ ⊥) (x : α) :
    baseMeasure B xᶜ = baseMeasure B ⊤ - baseMeasure B x := by
  -- x and xᶜ partition ⊤
  have hDisj : Disjoint x xᶜ := disjoint_compl_right
  have hJoin : x ⊔ xᶜ = ⊤ := sup_compl_eq_top
  have hAdd := baseMeasure.additive B x xᶜ hDisj
  rw [hJoin] at hAdd
  linarith

/-- For normalized measures, m(xᶜ) = 1 - m(x). -/
theorem baseMeasure_compl_normalized
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (hTop : (⊤ : α) ≠ ⊥) (x : α) :
    baseMeasure B xᶜ = 1 - baseMeasure B x := by
  rw [baseMeasure_compl B hTop x, baseMeasure.top_eq_one B hNormalized hTop]

/-- Subadditivity for baseMeasure: m(x ⊔ y) ≤ m(x) + m(y).

This follows from inclusion-exclusion since m(x ⊓ y) ≥ 0. -/
theorem baseMeasure_subadditive
    (hTop : (⊤ : α) ≠ ⊥) (x y : α) :
    baseMeasure B (x ⊔ y) ≤ baseMeasure B x + baseMeasure B y := by
  have h := baseMeasure_inclusion_exclusion B x y
  have hnn : 0 ≤ baseMeasure B (x ⊓ y) := baseMeasure.nonneg B hTop (x ⊓ y)
  linarith

end MeasureAxioms

section ENNRealMeasure

/-! ### ENNReal Version for Mathlib Compatibility

We provide a version of baseMeasure taking values in ℝ≥0∞ (extended non-negative reals)
for compatibility with Mathlib's measure theory framework. -/

variable {α : Type*} [Lattice α] [BoundedOrder α]

open scoped ENNReal

/-- Convert baseMeasure to ENNReal for use with Mathlib's measure theory.

Since baseMeasure is non-negative (for normalized bivaluations), we can safely convert.
Values are finite (not ∞) since baseMeasure is bounded by m(⊤). -/
noncomputable def baseMeasureENNReal (B : Bivaluation α) (_hTop : (⊤ : α) ≠ (⊥ : α)) : α → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (baseMeasure B x)

theorem baseMeasureENNReal_bot (B : Bivaluation α) (hTop : (⊤ : α) ≠ (⊥ : α)) :
    baseMeasureENNReal B hTop ⊥ = 0 := by
  simp only [baseMeasureENNReal, baseMeasure.bot B hTop, ENNReal.ofReal_zero]

theorem baseMeasureENNReal_ne_top (B : Bivaluation α) (hTop : (⊤ : α) ≠ (⊥ : α)) (x : α) :
    baseMeasureENNReal B hTop x ≠ ⊤ := by
  simp only [baseMeasureENNReal, ne_eq]
  exact ENNReal.ofReal_ne_top

theorem baseMeasureENNReal_mono (B : Bivaluation α) (hTop : (⊤ : α) ≠ (⊥ : α)) {x y : α} (hxy : x ≤ y) :
    baseMeasureENNReal B hTop x ≤ baseMeasureENNReal B hTop y := by
  simp only [baseMeasureENNReal]
  exact ENNReal.ofReal_le_ofReal (baseMeasure.mono B x y hxy)

theorem baseMeasureENNReal_additive (B : Bivaluation α) (hTop : (⊤ : α) ≠ (⊥ : α))
    {x y : α} (hDisj : Disjoint x y) :
    baseMeasureENNReal B hTop (x ⊔ y) =
    baseMeasureENNReal B hTop x + baseMeasureENNReal B hTop y := by
  simp only [baseMeasureENNReal]
  rw [baseMeasure.additive B x y hDisj]
  have ha : 0 ≤ baseMeasure B x := baseMeasure.nonneg B hTop x
  have hb : 0 ≤ baseMeasure B y := baseMeasure.nonneg B hTop y
  exact ENNReal.ofReal_add ha hb

theorem baseMeasureENNReal_top_eq_one (B : Bivaluation α)
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1) (hTop : (⊤ : α) ≠ (⊥ : α)) :
    baseMeasureENNReal B hTop ⊤ = 1 := by
  simp only [baseMeasureENNReal, baseMeasure.top_eq_one B hNormalized hTop, ENNReal.ofReal_one]

end ENNRealMeasure

/-- **Probability as a ratio of measures** (K&S Eq. (ratio)).

With the chain-product rule in hand, define the underlying measure by `m(x) := p(x|⊤)`.
Then for any context `t ≠ ⊥` we have:

`p(x|t) = m(x ⊓ t) / m(t)`.
-/
theorem prob_eq_measure_ratio
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α) [CA : ChainingAssociativity α B]
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1) :
    ∀ x t : α, t ≠ ⊥ → B.p x t = baseMeasure B (x ⊓ t) / baseMeasure B t := by
  intro x t ht_ne_bot
  let m : α → ℝ := baseMeasure B
  have ht : ⊥ < t := (bot_lt_iff_ne_bot).2 ht_ne_bot
  have hm_t_pos : 0 < m t := by
    simpa [m, baseMeasure] using (B.p_pos t ⊤ ht le_top)
  have hm_t_ne : m t ≠ 0 := ne_of_gt hm_t_pos

  by_cases hxt : x ⊓ t = ⊥
  · -- If `x ⊓ t = ⊥`, then `p(x|t) = 0`, and the ratio is `0 / m(t)`.
    have htop_ne_bot : (⊤ : α) ≠ ⊥ := by
      intro htop
      have ht_le_bot : t ≤ (⊥ : α) := by
        simpa [htop] using (le_top : t ≤ ⊤)
      have : t = (⊥ : α) := le_antisymm ht_le_bot bot_le
      exact ht_ne_bot this
    have htop : (⊥ : α) < ⊤ := (bot_lt_iff_ne_bot).2 htop_ne_bot
    have hm_bot : m ⊥ = 0 := by
      simpa [m, baseMeasure] using (B.p_bot ⊤ htop)
    have hpxt : B.p x t = 0 := by
      calc
        B.p x t = B.p (x ⊓ t) t := B.p_context x t
        _ = B.p ⊥ t := by simp [hxt]
        _ = 0 := B.p_bot t ht
    have hpbot_top : B.p ⊥ ⊤ = 0 := by
      -- We only need `p(⊥|⊤)=0` to simplify the numerator.
      simpa [m, baseMeasure] using (B.p_bot ⊤ htop)
    have hnum : baseMeasure B (x ⊓ t) = 0 := by
      simpa [baseMeasure, hxt] using hpbot_top
    calc
      B.p x t = 0 := hpxt
      _ = baseMeasure B (x ⊓ t) / baseMeasure B t := by
          simp [hnum]
  · -- If `x ⊓ t ≠ ⊥`, apply chain-product rule on the chain `x ⊓ t ≤ t ≤ ⊤`.
    have hxt_pos : ⊥ < x ⊓ t := (bot_lt_iff_ne_bot).2 hxt
    have hchain :
        B.p (x ⊓ t) ⊤ = B.p (x ⊓ t) t * B.p t ⊤ := by
      simpa using
        (chainProductRule B hNormalized (x ⊓ t) t ⊤ (inf_le_right) le_top hxt_pos)
    have hpxt : B.p x t = B.p (x ⊓ t) t := by
      simpa using (B.p_context x t)
    have hmxt : m (x ⊓ t) = B.p x t * m t := by
      -- Rewrite `hchain` in terms of `m` and `p(x|t)`.
      -- (`m (x ⊓ t) = p(x ⊓ t|⊤)` and `m t = p(t|⊤)`.)
      simpa [m, baseMeasure, hpxt, mul_comm, mul_left_comm, mul_assoc] using hchain
    have hratio : m (x ⊓ t) / m t = B.p x t := by
      calc
        m (x ⊓ t) / m t = (B.p x t * m t) / m t := by simp [hmxt]
        _ = B.p x t := by simpa using (mul_div_cancel_right₀ (B.p x t) hm_t_ne)
    exact hratio.symm

/-! ## Range of Probability

From `Pr(x|t) = m(x ∧ t) / m(t)` and `x ∧ t ≤ t`:
- `Pr(⊥|t) = 0` (since m(⊥) = 0)
- `Pr(t|t) = 1` (since m(t)/m(t) = 1)
- `0 ≤ Pr(x|t) ≤ 1` (since m(x ∧ t) ≤ m(t))
-/

/-- **General sum rule** (Boolean algebra form).

For any `x, y` (not necessarily disjoint):

`p(x ⊔ y | t) + p(x ⊓ y | t) = p(x | t) + p(y | t)`.

This is the classical inclusion-exclusion identity specialized to a bivaluation
in a Boolean algebra, obtained by decomposing `x` into `(x ⊓ yᶜ) ⊔ (x ⊓ y)` and
using disjoint additivity.
-/
theorem sumRule_general
    {α : Type*} [BooleanAlgebra α]
    (B : Bivaluation α) :
    ∀ x y t : α,
      B.p (x ⊔ y) t + B.p (x ⊓ y) t = B.p x t + B.p y t := by
  intro x y t
  -- Reduce everything into the context via p_context.
  let a : α := x ⊓ t
  let b : α := y ⊓ t
  have ha_le : a ≤ t := by simp [a]
  have hb_le : b ≤ t := by simp [b]

  have hx : B.p x t = B.p a t := by simpa [a] using (B.p_context x t)
  have hy : B.p y t = B.p b t := by simpa [b] using (B.p_context y t)

  have hsup : B.p (x ⊔ y) t = B.p (a ⊔ b) t := by
    calc
      B.p (x ⊔ y) t = B.p ((x ⊔ y) ⊓ t) t := B.p_context (x ⊔ y) t
      _ = B.p ((x ⊓ t) ⊔ (y ⊓ t)) t := by
            -- Use distributivity: (x ⊔ y) ⊓ t = (x ⊓ t) ⊔ (y ⊓ t)
            have h : (x ⊔ y) ⊓ t = (x ⊓ t) ⊔ (y ⊓ t) := by
              simpa [inf_comm, inf_left_comm, inf_assoc] using (inf_sup_right x y t)
            simp [h]
      _ = B.p (a ⊔ b) t := by simp [a, b]

  have hinf : B.p (x ⊓ y) t = B.p (a ⊓ b) t := by
    calc
      B.p (x ⊓ y) t = B.p ((x ⊓ y) ⊓ t) t := B.p_context (x ⊓ y) t
      _ = B.p ((x ⊓ t) ⊓ (y ⊓ t)) t := by
            simp [inf_left_comm, inf_comm]
      _ = B.p (a ⊓ b) t := by simp [a, b]

  -- Core inclusion-exclusion for a,b ≤ t using disjoint additivity.
  have hcore : B.p (a ⊔ b) t + B.p (a ⊓ b) t = B.p a t + B.p b t := by
    -- Decompose a = (a ⊓ bᶜ) ⊔ (a ⊓ b).
    have hdecomp_a : (a ⊓ bᶜ) ⊔ (a ⊓ b) = a := by
      calc
        (a ⊓ bᶜ) ⊔ (a ⊓ b) = a ⊓ (bᶜ ⊔ b) := by
          symm
          simpa using (inf_sup_left a bᶜ b)
        _ = a ⊓ ⊤ := by simp
        _ = a := by simp

    have hdisj_a : Disjoint (a ⊓ bᶜ) (a ⊓ b) := by
      rw [disjoint_iff]
      calc (a ⊓ bᶜ) ⊓ (a ⊓ b)
          = a ⊓ (bᶜ ⊓ b) := by
              simp [inf_left_comm, inf_comm]
        _ = ⊥ := by simp

    have hle_a : (a ⊓ bᶜ) ⊔ (a ⊓ b) ≤ t := by
      have h1 : a ⊓ bᶜ ≤ a := inf_le_left
      have h2 : a ⊓ b ≤ a := inf_le_left
      have : (a ⊓ bᶜ) ⊔ (a ⊓ b) ≤ a := sup_le h1 h2
      exact le_trans this ha_le

    have hadd_a : B.p a t = B.p (a ⊓ bᶜ) t + B.p (a ⊓ b) t := by
      have := B.p_sum_disjoint (a ⊓ bᶜ) (a ⊓ b) t hdisj_a hle_a
      -- rewrite the left side using the decomposition
      rw [hdecomp_a] at this
      exact this

    -- Also decompose (a ⊔ b) = (a ⊓ bᶜ) ⊔ b.
    have hdisj_sup : Disjoint (a ⊓ bᶜ) b := by
      rw [disjoint_iff]
      calc (a ⊓ bᶜ) ⊓ b
          = a ⊓ (bᶜ ⊓ b) := by
              simp [inf_left_comm, inf_comm]
        _ = ⊥ := by simp

    have hle_sup : (a ⊓ bᶜ) ⊔ b ≤ t := by
      refine sup_le ?_ hb_le
      exact le_trans inf_le_left ha_le

    have hjoin_sup : (a ⊓ bᶜ) ⊔ b = a ⊔ b := by
      apply le_antisymm
      · exact sup_le (le_trans inf_le_left le_sup_left) le_sup_right
      · refine sup_le ?_ le_sup_right
        have hab : a ⊓ b ≤ b := inf_le_right
        have hjoin_le : (a ⊓ bᶜ) ⊔ (a ⊓ b) ≤ (a ⊓ bᶜ) ⊔ b :=
          sup_le le_sup_left (le_trans hab le_sup_right)
        have ha_le' : a ≤ (a ⊓ bᶜ) ⊔ b := by
          calc
            a = (a ⊓ bᶜ) ⊔ (a ⊓ b) := hdecomp_a.symm
            _ ≤ (a ⊓ bᶜ) ⊔ b := hjoin_le
        exact ha_le'

    have hadd_sup : B.p (a ⊔ b) t = B.p (a ⊓ bᶜ) t + B.p b t := by
      have := B.p_sum_disjoint (a ⊓ bᶜ) b t hdisj_sup hle_sup
      simpa [hjoin_sup] using this

    linarith [hadd_a, hadd_sup]

  linarith [hsup, hinf, hx, hy, hcore]

/-- Probability is bounded in [0, 1]. -/
theorem prob_range
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α)
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1) :
    ∀ x t : α, ⊥ < t → x ≤ t → 0 ≤ B.p x t ∧ B.p x t ≤ 1 := by
  intro x t ht hxt
  constructor
  · by_cases hx : ⊥ < x
    · exact le_of_lt (B.p_pos x t hx hxt)
    · -- ¬(⊥ < x) means x = ⊥ (since ⊥ ≤ x always holds)
      have : x = ⊥ := by
        simp only [bot_lt_iff_ne_bot, ne_eq, not_not] at hx
        exact hx
      rw [this, B.p_bot t ht]
  · calc B.p x t ≤ B.p t t := B.p_mono_left x t t hxt (le_refl t)
      _ = 1 := hNormalized t ht

/-! ## Additional Corollaries

These are standard probability identities that follow from the derived rules above.
Not in K&S's paper directly, but useful to have formalized.
-/

/-- **Law of Total Probability** (two-partition case).

If `a` and `b` partition `t` (i.e., `a ⊔ b = t` and `a ⊓ b = ⊥`), then:
`Pr(x|t) = Pr(x|a) · Pr(a|t) + Pr(x|b) · Pr(b|t)`

This is a direct consequence of the product rule and disjoint additivity.
-/
theorem lawOfTotalProbability
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α) [CA : ChainingAssociativity α B]
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (x a b t : α)
    (hPartition : a ⊔ b = t) (hDisjoint : a ⊓ b = ⊥)
    (ha_pos : ⊥ < a) (hb_pos : ⊥ < b)
    (hxa_pos : ⊥ < x ⊓ a) (hxb_pos : ⊥ < x ⊓ b) :
    B.p x t = B.p x a * B.p a t + B.p x b * B.p b t := by
  -- By p_context: p(x|t) = p(x ⊓ t | t)
  have hxt : B.p x t = B.p (x ⊓ t) t := B.p_context x t
  -- Since a ⊔ b = t, we have x ⊓ t = x ⊓ (a ⊔ b) = (x ⊓ a) ⊔ (x ⊓ b)
  have hdecomp : x ⊓ t = (x ⊓ a) ⊔ (x ⊓ b) := by
    calc x ⊓ t = x ⊓ (a ⊔ b) := by rw [hPartition]
      _ = (x ⊓ a) ⊔ (x ⊓ b) := inf_sup_left x a b
  -- (x ⊓ a) and (x ⊓ b) are disjoint since a ⊓ b = ⊥
  have hDisjXAB : Disjoint (x ⊓ a) (x ⊓ b) := by
    rw [disjoint_iff]
    -- (x ⊓ a) ⊓ (x ⊓ b) = x ⊓ (a ⊓ b) by lattice identities
    have hlat : (x ⊓ a) ⊓ (x ⊓ b) = x ⊓ (a ⊓ b) := by
      calc (x ⊓ a) ⊓ (x ⊓ b) = x ⊓ (a ⊓ (x ⊓ b)) := inf_assoc x a (x ⊓ b)
        _ = x ⊓ (x ⊓ (a ⊓ b)) := by rw [inf_left_comm a x b]
        _ = (x ⊓ x) ⊓ (a ⊓ b) := (inf_assoc x x (a ⊓ b)).symm
        _ = x ⊓ (a ⊓ b) := by rw [inf_idem]
    calc (x ⊓ a) ⊓ (x ⊓ b) = x ⊓ (a ⊓ b) := hlat
      _ = x ⊓ ⊥ := by rw [hDisjoint]
      _ = ⊥ := inf_bot_eq x
  -- Apply disjoint sum rule
  have ha_le : a ≤ t := by rw [← hPartition]; exact le_sup_left
  have hb_le : b ≤ t := by rw [← hPartition]; exact le_sup_right
  have hxa_le : x ⊓ a ≤ t := le_trans inf_le_right ha_le
  have hxb_le : x ⊓ b ≤ t := le_trans inf_le_right hb_le
  have hle : (x ⊓ a) ⊔ (x ⊓ b) ≤ t := sup_le hxa_le hxb_le
  have hSum : B.p ((x ⊓ a) ⊔ (x ⊓ b)) t = B.p (x ⊓ a) t + B.p (x ⊓ b) t :=
    B.p_sum_disjoint (x ⊓ a) (x ⊓ b) t hDisjXAB hle
  -- Apply product rule to each term
  have hProdA : B.p (x ⊓ a) t = B.p x a * B.p a t :=
    productRule B hNormalized x a t hxa_pos ha_le ha_pos
  have hProdB : B.p (x ⊓ b) t = B.p x b * B.p b t :=
    productRule B hNormalized x b t hxb_pos hb_le hb_pos
  -- Combine
  calc B.p x t = B.p (x ⊓ t) t := hxt
    _ = B.p ((x ⊓ a) ⊔ (x ⊓ b)) t := by rw [hdecomp]
    _ = B.p (x ⊓ a) t + B.p (x ⊓ b) t := hSum
    _ = B.p x a * B.p a t + B.p x b * B.p b t := by rw [hProdA, hProdB]

/-- **Chain Rule for Three Events**.

For a chain `a ≤ b ≤ c ≤ d`:
`Pr(a|d) = Pr(a|b) · Pr(b|c) · Pr(c|d)`

This extends the binary chain rule to three intermediate steps.
-/
theorem chainRule_three
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α) [CA : ChainingAssociativity α B]
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (a b c d : α) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (ha_pos : ⊥ < a) :
    B.p a d = B.p a b * B.p b c * B.p c d := by
  have hb_pos : ⊥ < b := lt_of_lt_of_le ha_pos hab
  have hc_pos : ⊥ < c := lt_of_lt_of_le hb_pos hbc
  -- First apply chain rule to (a, c, d)
  have hac : a ≤ c := le_trans hab hbc
  have h1 : B.p a d = B.p a c * B.p c d := chainProductRule B hNormalized a c d hac hcd ha_pos
  -- Then apply chain rule to (a, b, c)
  have h2 : B.p a c = B.p a b * B.p b c := chainProductRule B hNormalized a b c hab hbc ha_pos
  -- Combine
  calc B.p a d = B.p a c * B.p c d := h1
    _ = (B.p a b * B.p b c) * B.p c d := by rw [h2]
    _ = B.p a b * B.p b c * B.p c d := by ring

/-- **Conditional Independence** (definition).

Events `x` and `y` are conditionally independent given `t` if:
`Pr(x ⊓ y | t) = Pr(x | t) · Pr(y | t)`
-/
def ConditionallyIndependent
    {α : Type*} [Lattice α] [BoundedOrder α]
    (B : Bivaluation α) (x y t : α) : Prop :=
  B.p (x ⊓ y) t = B.p x t * B.p y t

/-- **Multiplication Rule** (general form).

`Pr(x ⊓ y ⊓ z | t) = Pr(x | y ⊓ z) · Pr(y | z) · Pr(z | t)`

when `z ≤ t` and appropriate positivity conditions hold.
-/
theorem multiplicationRule_three
    {α : Type*} [DistribLattice α] [BoundedOrder α]
    (B : Bivaluation α) [CA : ChainingAssociativity α B]
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (x y z t : α) (hzt : z ≤ t)
    (hxyz_pos : ⊥ < x ⊓ y ⊓ z) (_hyz_pos : ⊥ < y ⊓ z) (_hz_pos : ⊥ < z) :
    B.p (x ⊓ y ⊓ z) t = B.p x (y ⊓ z) * B.p y z * B.p z t := by
  -- Chain: x ⊓ y ⊓ z ≤ y ⊓ z ≤ z ≤ t
  have h1 : x ⊓ y ⊓ z ≤ y ⊓ z := by
    calc x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := inf_assoc x y z
      _ ≤ y ⊓ z := inf_le_right
  have h2 : y ⊓ z ≤ z := inf_le_right
  -- Apply three-step chain rule
  have hchain := chainRule_three B hNormalized (x ⊓ y ⊓ z) (y ⊓ z) z t h1 h2 hzt hxyz_pos
  -- By p_context: p(x | y ⊓ z) = p(x ⊓ (y ⊓ z) | y ⊓ z) = p(x ⊓ y ⊓ z | y ⊓ z)
  have hctx : B.p x (y ⊓ z) = B.p (x ⊓ y ⊓ z) (y ⊓ z) := by
    have h := B.p_context x (y ⊓ z)
    -- p_context gives p(x | y ⊓ z) = p(x ⊓ (y ⊓ z) | y ⊓ z)
    -- Need to show x ⊓ (y ⊓ z) = x ⊓ y ⊓ z (which is (x ⊓ y) ⊓ z by Lean's parsing)
    rw [(inf_assoc x y z).symm] at h
    exact h
  -- Combine
  calc B.p (x ⊓ y ⊓ z) t
      = B.p (x ⊓ y ⊓ z) (y ⊓ z) * B.p (y ⊓ z) z * B.p z t := hchain
    _ = B.p x (y ⊓ z) * B.p (y ⊓ z) z * B.p z t := by rw [← hctx]
    _ = B.p x (y ⊓ z) * B.p y z * B.p z t := by
        -- p(y ⊓ z | z) = p(y | z) by p_context
        have h : B.p (y ⊓ z) z = B.p y z := (B.p_context y z).symm
        rw [h]

/-- **Complement Rule**.

In a Boolean algebra: `Pr(xᶜ | t) = 1 - Pr(x | t)` when `x ≤ t`.
-/
theorem complementRule
    {α : Type*} [BooleanAlgebra α]
    (B : Bivaluation α)
    (hNormalized : ∀ t : α, ⊥ < t → B.p t t = 1)
    (x t : α) (_hxt : x ≤ t) (ht_pos : ⊥ < t) :
    B.p (xᶜ ⊓ t) t = 1 - B.p x t := by
  -- x and xᶜ partition ⊤, so (x ⊓ t) and (xᶜ ⊓ t) partition t
  have hDisj : Disjoint (x ⊓ t) (xᶜ ⊓ t) := by
    rw [disjoint_iff]
    -- (x ⊓ t) ⊓ (xᶜ ⊓ t) = (x ⊓ xᶜ) ⊓ t by lattice identities
    have hlat : (x ⊓ t) ⊓ (xᶜ ⊓ t) = (x ⊓ xᶜ) ⊓ t := by
      calc (x ⊓ t) ⊓ (xᶜ ⊓ t) = x ⊓ (t ⊓ (xᶜ ⊓ t)) := inf_assoc x t (xᶜ ⊓ t)
        _ = x ⊓ (xᶜ ⊓ (t ⊓ t)) := by rw [inf_left_comm t xᶜ t]
        _ = x ⊓ (xᶜ ⊓ t) := by rw [inf_idem]
        _ = (x ⊓ xᶜ) ⊓ t := (inf_assoc x xᶜ t).symm
    calc (x ⊓ t) ⊓ (xᶜ ⊓ t) = (x ⊓ xᶜ) ⊓ t := hlat
      _ = ⊥ ⊓ t := by simp only [inf_compl_eq_bot]
      _ = ⊥ := bot_inf_eq t
  have hJoin : (x ⊓ t) ⊔ (xᶜ ⊓ t) = t := by
    calc (x ⊓ t) ⊔ (xᶜ ⊓ t) = (x ⊔ xᶜ) ⊓ t := by
          symm; exact inf_sup_right x xᶜ t
      _ = ⊤ ⊓ t := by simp only [sup_compl_eq_top]
      _ = t := top_inf_eq t
  -- By disjoint additivity
  have hle : (x ⊓ t) ⊔ (xᶜ ⊓ t) ≤ t := by rw [hJoin]
  have hSum : B.p ((x ⊓ t) ⊔ (xᶜ ⊓ t)) t = B.p (x ⊓ t) t + B.p (xᶜ ⊓ t) t :=
    B.p_sum_disjoint (x ⊓ t) (xᶜ ⊓ t) t hDisj hle
  -- p(t | t) = 1
  have hNorm : B.p t t = 1 := hNormalized t ht_pos
  -- p(x | t) = p(x ⊓ t | t) by p_context
  have hCtx : B.p x t = B.p (x ⊓ t) t := B.p_context x t
  -- Combine: 1 = p(x ⊓ t | t) + p(xᶜ ⊓ t | t)
  have h : B.p t t = B.p (x ⊓ t) t + B.p (xᶜ ⊓ t) t := by
    calc B.p t t = B.p ((x ⊓ t) ⊔ (xᶜ ⊓ t)) t := by rw [hJoin]
      _ = B.p (x ⊓ t) t + B.p (xᶜ ⊓ t) t := hSum
  rw [hNorm] at h
  linarith

end KnuthSkilling.Probability.ConditionalProbability
