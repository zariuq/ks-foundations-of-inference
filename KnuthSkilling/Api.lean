/-
# Knuth–Skilling Foundations of Inference — Public Core API

This is the single top-level entry point for the *headline results* of the
Knuth–Skilling formalization. It is **purely additive**: it imports the modules where the
results are actually proven and re-states each headline theorem verbatim (its proof here is
just an application of the original), so that an external reader can find every crown-jewel
statement, the key axioms/definitions, and all three representation routes in one place.

Nothing here changes any statement or moves any proof. For the underlying developments see the
files cited at each entry, and the narrative map in `KnuthSkilling/Overview.lean`.

## Headline theorems (re-stated below)

1. `KnuthSkilling.Api.faddeev_iff_shannonKhinchin`
     — Shannon entropy: Faddeev's axioms ⟺ Shannon–Khinchin axioms.
     Source: `InformationTheory.faddeev_iff_shannonKhinchin`
     (`InformationTheory/ShannonEntropy/Equivalence.lean`).
2. `KnuthSkilling.Api.ks_representation_theorem`
     — Additive representation: a normalized representation yields a strictly monotone additive
       `Θ : α → ℝ` with `Θ ident = 0`.
     Source: `KnuthSkilling.Probability.ks_representation_theorem`
     (`KnuthSkilling/Probability/ProbabilityDerivation.lean`).
3. `KnuthSkilling.Api.Psi_is_exp`
     — Appendix B: the product equation forces `Ψ` to be an exponential.
     Source: `KnuthSkilling.Multiplicative.Psi_is_exp`
     (`KnuthSkilling/Multiplicative/Main.lean`).
4. `KnuthSkilling.Api.op_comm_of_hasRepresentationTheorem`
     — Commutativity follows from any additive order representation.
     Source: `KnuthSkilling.Additive.op_comm_of_hasRepresentationTheorem`
     (`KnuthSkilling/Additive/Main.lean`).

## Key axioms / definitions (re-exported)

- `KSSemigroupBase`, `KnuthSkillingMonoidBase`, `KnuthSkillingAlgebraBase` — the base structures
  (`KnuthSkilling/Core/Basic.lean`).
- `KSSeparation`, `KSSeparationStrict` — the sandwich separation axioms
  (`KnuthSkilling/Core/Algebra.lean`).
- `HasRepresentationTheorem`, `HasNormalizedRepresentation`, `RepresentationResult` — the
  representation interfaces (`KnuthSkilling/Additive/Representation.lean`).

## The three additive-representation routes (all proven, all axiom-clean)

- **Hölder / Alimov** (`Api.representation_from_noAnomalousPairs`): `[NoAnomalousPairs α]` ⟹ Θ.
  Source: `…/OrderedSemigroupEmbedding/HolderEmbedding.lean`.
- **Dedekind cuts** (`Api.associativity_representation_cuts`):
  `[KnuthSkillingAlgebraBase α] [KSSeparation α] [KSSeparationStrict α]` ⟹ Θ.
  Source: `…/DirectCuts/Main.lean`.
- **Grid / induction** (`Api.grid_representation_of_KSSeparationStrict`):
  `[KSSeparationStrict α]` ⟹ Θ, via `representationGlobalization_of_KSSeparationStrict`.
  Source: `…/GridInduction/Globalization.lean`.
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
    (∃ (_E : InformationTheory.FaddeevEntropy), True) ↔
      (∃ (_E : InformationTheory.ShannonKhinchinEntropy), True) :=
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

/-- **Route 2 (Dedekind cuts).** From `[KSSeparation α] [KSSeparationStrict α]` (re-statement of
`…DirectCuts.associativity_representation_cuts`). -/
theorem associativity_representation_cuts (α : Type*)
    [KnuthSkillingAlgebraBase α] [KSSeparation α] [KSSeparationStrict α] :
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
  KnuthSkilling.Additive.RepresentationGlobalization.exists_Theta (α := α)

end KnuthSkilling.Api
