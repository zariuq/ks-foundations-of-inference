/-
# Public theorem entry point

The wrappers below retain their source conclusions and explicit premises.
Additive representations are order embeddings; a real order isomorphism is
additional data required by the inverse-based product route. Calibration
compares supplied additive maps at a positive anchor, not at an arbitrary zero.

`faddeev_iff_shannonKhinchin` is the existence corollary of the entropy-preserving
record equivalence `InformationTheory.faddeevShannonKhinchinEquiv`.
`ks_representation_theorem` packages a supplied normalized representation.
The three existence routes below discharge their respective representation
premises. The Grid route selects the maintained strict-separation globalization;
`zero_anchor_globalization_impossible` rules out mapping a positive anchor to
zero; `RepresentationResult.calibrate` instead fixes its value at one.

Probability normalization, singular KL and admissible variational inference
are described in `Overview`; they are distinct interpretation layers.
-/

-- Information theory (Shannon entropy axiomatics).
import InformationTheory.ShannonEntropy.Equivalence

-- Additive representation theorem + interfaces.
import KnuthSkilling.Additive.Main
import KnuthSkilling.Additive.Representation

-- Multiplicative / Appendix B.
import KnuthSkilling.Multiplicative.Main

-- Probability derivation (representation theorem packaging).
import KnuthSkilling.Probability.ProbabilityDerivation

-- The three additive-representation routes.
import KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding
import KnuthSkilling.Additive.Proofs.DirectCuts.Main
import KnuthSkilling.Additive.Proofs.GridInduction.Globalization

namespace KnuthSkilling.Api

open KSSemigroupBase KnuthSkillingMonoidBase
open KnuthSkilling.Multiplicative KnuthSkilling.Literature
open KnuthSkilling.Additive.Axioms.AnomalousPairs

/-! ## Headline 1 — Shannon entropy axiom equivalence -/

/-- **Faddeev ⟺ Shannon–Khinchin** (re-statement of
`InformationTheory.faddeev_iff_shannonKhinchin`). -/
theorem faddeev_iff_shannonKhinchin :
    Nonempty InformationTheory.FaddeevEntropy ↔ Nonempty InformationTheory.ShannonKhinchinEntropy :=
  InformationTheory.faddeev_iff_shannonKhinchin

/-! ## Headline 2 — Additive representation theorem -/

/-- **K&S additive representation theorem** (re-statement of
`KnuthSkilling.Probability.ks_representation_theorem`): a normalized representation produces a
strictly monotone additive `Θ : α → ℝ` with `Θ ident = 0`. -/
theorem ks_representation_theorem {α : Type*}
    [KnuthSkillingMonoidBase α]
    [KnuthSkilling.Additive.HasNormalizedRepresentation α] :
    ∃ (Θ : α → ℝ),
      StrictMono Θ ∧
        Θ (KnuthSkillingMonoidBase.ident (α := α)) = 0 ∧
          (∀ x y : α, Θ (KSSemigroupBase.op x y) = Θ x + Θ y) :=
  KnuthSkilling.Probability.ks_representation_theorem (α := α)

/-! ## Headline 3 — Appendix B: Ψ is exponential -/

/-- **Appendix B exponential form** (re-statement of `KnuthSkilling.Multiplicative.Psi_is_exp`). -/
theorem Psi_is_exp {tensor : PosReal → PosReal → PosReal}
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ (C A : ℝ), 0 < C ∧
      ∀ x : ℝ, KnuthSkilling.Multiplicative.Derived.Psi hRep x = C * Real.exp (A * x) :=
  KnuthSkilling.Multiplicative.Psi_is_exp (tensor := tensor) hRep hDistrib

/-! ## Headline 4 — Commutativity from representation -/

/-- **Commutativity from any additive order representation** (re-statement of
`KnuthSkilling.Additive.op_comm_of_hasRepresentationTheorem`). -/
theorem op_comm_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [KnuthSkilling.Additive.HasRepresentationTheorem α] :
    ∀ x y : α, KSSemigroupBase.op x y = KSSemigroupBase.op y x :=
  KnuthSkilling.Additive.op_comm_of_hasRepresentationTheorem α

/-! ## The three additive-representation routes

Each produces an order-preserving additive `Θ : α → ℝ` with `Θ ident = 0` from a different
hypothesis. All three are proven and depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). -/

/-- **Route 1 (Hölder / Alimov).** From `[NoAnomalousPairs α]` (re-statement of
`…HolderEmbedding.representation_from_noAnomalousPairs`). -/
theorem representation_from_noAnomalousPairs {α : Type*}
    [KnuthSkillingMonoidBase α] [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y :=
  KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding.representation_from_noAnomalousPairs
    (α := α)

/-- **Route 2 (Dedekind cuts).** From `[KSSeparationStrict α]` (re-statement of
`…DirectCuts.associativity_representation_cuts`). -/
theorem associativity_representation_cuts (α : Type*)
    [KnuthSkillingAlgebraBase α] [KSSeparationStrict α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y :=
  KnuthSkilling.Additive.Proofs.DirectCuts.associativity_representation_cuts α

/-- **Route 3 (grid / induction).** From `[KnuthSkillingAlgebraBase α] [KSSeparationStrict α]`, via
the globalization instance `representationGlobalization_of_KSSeparationStrict`. This is the route
the grid chain establishes. -/
theorem grid_representation_of_KSSeparationStrict (α : Type*)
    [KnuthSkillingAlgebraBase α] [KSSeparationStrict α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y :=
  by
    let : KnuthSkilling.Additive.RepresentationGlobalization α :=
      KnuthSkilling.Additive.representationGlobalization_of_KSSeparationStrict
    exact KnuthSkilling.Additive.RepresentationGlobalization.exists_Theta (α := α)

end KnuthSkilling.Api
