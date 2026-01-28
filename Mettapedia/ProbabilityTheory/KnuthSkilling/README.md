# Knuth-Skilling Foundations of Inference

Lean 4 formalization of Knuth & Skilling's "Foundations of Inference" (2012).

## Overview

The **Knuth-Skilling representation theorem** shows that any algebraic structure
satisfying natural axioms (associativity, monotonicity, and a separation
property) embeds into `(ℝ, +)`. This provides a foundational justification for
probability theory without assuming additivity, continuity, or differentiability.

**Key insight**: K&S works on **distributive lattices**, not just Boolean algebras.
This means no negation/complements are required—a genuine generalization of
classical probability.

## Axiom Choices

Two main regularity axioms suffice for the representation theorem:

- **NoAnomalousPairs (NAP)**: From ordered semigroup theory (Alimov 1950, Fuchs 1963)
- **KSSeparation**: A sandwich property relating iterates (added by necessity in the process of formalization)

Both imply commutativity and Archimedean property. NAP is identity-free; KSSeparation requires identity. Under `IdentIsMinimum`, they are equivalent.

## Three Proof Paths

1. **Hölder/Alimov embedding** (`Additive/Proofs/OrderedSemigroupEmbedding/`):
   Uses NAP. Shortest proof via [Eric Paul's OrderedSemigroups](https://github.com/ericluap/OrderedSemigroups).

2. **Dedekind cuts** (`Additive/Proofs/DirectCuts/`):
   Uses KSSeparation. Classical construction.

3. **Grid induction** (`Additive/Proofs/GridInduction/`):
   Uses KSSeparation. Follows K&S paper structure.

## Main Result (Representation Theorem; Appendix A in the paper)

```lean
theorem associativity_representation
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧   -- Order embedding
      Θ ident = 0 ∧                        -- Identity maps to 0
      ∀ x y : α, Θ (op x y) = Θ x + Θ y    -- Operation maps to addition
```

In practice, the globalization class `RepresentationGlobalization` is provided automatically from the
induction pipeline once `KSSeparationStrict` is available; and `KSSeparationStrict` is derived from
`KSSeparation` under a mild “density above `ident`” hypothesis (e.g. `[DenselyOrdered α]`).

## Axiom System

### Our Approach: Base + Separation

We use a minimal base with separation as the key regularity condition:

**Base axioms (`KnuthSkillingAlgebraBase`)**:
- Linear order on α
- Associative operation `op : α → α → α`
- Identity element `ident`
- Strict monotonicity (both sides)
- Positivity (`ident ≤ x` for all x)

**Plus separation (`KSSeparation`)**:
- For any `a > ident` and `x < y`, there exist `m, n` such that `x^m < a^n ≤ y^m`

**What we DERIVE (not assume!)**:
- **Commutativity**: `op x y = op y x` — proven in `Additive/Axioms/SandwichSeparation.lean`
- **Archimedean property**: no infinitesimals — proven in `Additive/Axioms/SandwichSeparation.lean`

### Comparison with Other Expositions

Some treatments assume commutativity and Archimedean up front. Our approach is
more economical: separation implies both.

### Why Separation is Necessary

`KSSeparation` is **not derivable** from the base axioms alone. Counterexamples:
- `Counterexamples/SemidirectNoSeparation.lean`: Archimedean ordered associative monoid
  that is noncommutative and fails separation
- `Counterexamples/ProductFailsSeparation.lean`: Commutative ordered monoid with
  infinitesimals (ℕ×ℕ lexicographic) that fails separation

```lean
-- KSSeparation: For any a > ident and x < y, there exist m, n such that x^m < a^n ≤ y^m
class KSSeparation (α : Type*) [KnuthSkillingAlgebraBase α] : Prop where
  separation :
    ∀ {a x y : α},
      KnuthSkillingAlgebraBase.ident < a →
      KnuthSkillingAlgebraBase.ident < x →
      KnuthSkillingAlgebraBase.ident < y →
      x < y →
      ∃ n m : ℕ, 0 < m ∧
        KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
        KnuthSkillingAlgebra.iterate_op a n ≤ KnuthSkillingAlgebra.iterate_op y m
```

## Directory Structure

```
KnuthSkilling/
├── README.md                    # This file
├── FoundationsOfInference.lean  # Reviewer entrypoint (imports Core + Appendices A/B/C)
├── Core/                        # Core axiom hierarchy
│   ├── Basic.lean               # PlausibilitySpace, Valuation, KSSemigroupBase
│   ├── Algebra.lean             # iterate_op, KSSeparation, NoAnomalousPairs
│   └── ScaleCompleteness.lean   # σ-additivity bridge
├── Additive/                    # Appendix A: additive representation
│   ├── Main.lean                # Public API: HasRepresentationTheorem
│   ├── Axioms/                  # Axiom definitions
│   │   ├── AnomalousPairs.lean  # NoAnomalousPairs (NAP)
│   │   └── SandwichSeparation.lean  # KSSeparation ⇒ Commutativity + Archimedean
│   └── Proofs/                  # Three proof paths
│       ├── OrderedSemigroupEmbedding/  # Hölder path (NAP)
│       ├── DirectCuts/          # Dedekind cuts (KSSeparation)
│       └── GridInduction/       # K&S paper's induction (KSSeparation)
├── Multiplicative/              # Appendix B: product operation
│   ├── Main.lean                # Public entry point
│   └── Proofs/                  # Proof alternatives
├── Variational/                 # Appendix C: Cauchy/log equation
│   └── Main.lean                # Variational theorem
├── Probability/                 # Derived probability calculus
│   ├── ProbabilityCalculus.lean # Canonical interface for end-results
│   └── ProbabilityDerivation.lean
├── Information/                 # K&S Section 6/8: entropy/KL
│   └── Main.lean
├── ShoreJohnson/                # Shore-Johnson (1980) formalization
│   └── Main.lean                # SJ entrypoint (first-class, import explicitly)
├── Examples/                    # Concrete examples
│   ├── CoinDie.lean             # Full pipeline: coin/die → ℝ
│   └── PreciseVsImpreciseGrounded.lean  # K&S → credal sets, decision theory
├── Counterexamples/             # Why axioms matter
└── Literature/                  # Reference: Aczél, Hölder, Cox
```

## Key Files

| File | Description |
|------|-------------|
| `FoundationsOfInference.lean` | Main entrypoint (imports Core + Appendices A/B/C) |
| `Core/Basic.lean` | Core definitions: `KSSemigroupBase`, `KnuthSkillingMonoidBase` |
| `Additive/Axioms/AnomalousPairs.lean` | NoAnomalousPairs (NAP) definition |
| `Additive/Axioms/SandwichSeparation.lean` | KSSeparation ⇒ Commutativity + Archimedean |
| `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean` | Appendix A via Hölder (NAP) |
| `Additive/Proofs/DirectCuts/Main.lean` | Appendix A via Dedekind cuts (KSSeparation) |
| `Additive/Main.lean` | Appendix A: `HasRepresentationTheorem` |
| `Multiplicative/Main.lean` | Appendix B: product theorem |
| `Variational/Main.lean` | Appendix C: variational/Cauchy theorem |
| `Probability/ProbabilityCalculus.lean` | Sum rule, product rule, Bayes |
| `Examples/CoinDie.lean` | **Full pipeline example**: coin/die → ℝ |
| `Examples/PreciseVsImpreciseGrounded.lean` | **Decision theory**: K&S → credal sets → EU vs maximin |

## The Hypercube Connection

The K&S foundations fit into the **Probability Hypercube** (inspired by Stay-Wells).

The hypercube organizes probability theories by axes:
- **Commutativity**: commutative (classical) vs non-commutative (quantum)
- **Distributivity**: Boolean, distributive lattice, orthomodular
- **Precision**: precise (point-valued) vs imprecise (interval-valued)
- **Ordering**: linear (K&S) vs partial
- **Additivity**: σ-additive (Kolmogorov) vs derived (Cox, K&S)

K&S sits at: (commutative, distributive, precise, linear, derived-additive).

See `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Connection.lean` for the full development.

Note: the hypercube-related K&S analysis files now live under:
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Connection.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Neighbors.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Proofs.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Theory.lean`

For the hypercube's "weakness preorder" + quantale-semantics layer (inspired by Goertzel and Bennett), see:
- `Mettapedia/ProbabilityTheory/Hypercube/WeaknessOrder.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/QuantaleSemantics.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/ThetaSemantics.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/DensityAxisStory.lean`

## Build

```bash
cd lean-projects/mettapedia
export LAKE_JOBS=3
nice -n 19 lake build Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
```

## Status

Complete. Roughly human-checked. Zero `sorry`, zero `axiom`.

## Examples

- `Examples/CoinDie.lean`: Full pipeline coin/die → ℝ
- `Examples/PreciseVsImpreciseGrounded.lean`: K&S → credal sets → decision theory
- `Examples/ImpreciseOn7Element.lean`: Imprecise probability on 7-element lattice
- `Bridges/Model.lean`: Event lattice → plausibility scale connection

## Countermodels (why the extra axioms matter)

- `Additive/Counterexamples/SemidirectNoSeparation.lean`: an Archimedean ordered associative monoid
  which is noncommutative and fails `KSSeparation` (so "Archimedean semigroup ⇒ commutative" is
  false).
- `Additive/Counterexamples/ProductFailsSeparation.lean`: a commutative ordered monoid with
  infinitesimals (lexicographic product), failing the sandwich separation axiom `KSSeparation`
  even though addition is commutative (and in particular it is not Archimedean, so it is not a
  `KnuthSkillingAlgebra`).
- `Additive/Counterexamples/KSSeparationNotDerivable.lean`: proves NAP must be postulated, not derived.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Hölder, "Die Axiome der Quantität und die Lehre vom Mass" (1901) — ordered group embeddings
- Alimov (1950) — ordered semigroup embeddings
- Klain & Rota, "Introduction to Geometric Probability" — valuations on distributive lattices
- Aczél, "Lectures on Functional Equations" — rational homogeneity
- Stay & Wells, "Generating Hypercubes of Type Systems"

## Papers

See `papers/ks-lean-overview.pdf` for a Lean code walkthrough with line numbers.
