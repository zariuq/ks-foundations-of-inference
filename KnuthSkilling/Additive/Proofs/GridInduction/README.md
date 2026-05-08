# K&S Representation Theorem (Grid Induction Path)

> **Note**: This directory documents the **grid-induction proof path**, which uses
> `KSSeparationStrict` (requires identity). For the **canonical assumption hierarchy**
> using `NoAnomalousPairs` (identity-free, 1950s literature), see
> `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean`.

This directory contains the grid/induction proof of the Knuth-Skilling representation
theorem from Appendix A of "Foundations of Inference".

## Main Theorem

The representation theorem establishes that any K&S algebra admits an order
embedding into `(R, +)`:

```lean
theorem associativity_representation
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧   -- Order embedding
      Θ ident = 0 ∧                        -- Identity maps to 0
      ∀ x y : α, Θ (op x y) = Θ x + Θ y    -- Additivity
```

## Proof Architecture

The proof proceeds by induction on "atom families":

### Alternative Proof (Direct Cuts)

There is also a compact Dedekind-cuts proof of the same representation theorem, packaged as:

- `../DirectCuts/Main.lean` (`associativity_representation_cuts`)
- `../DirectCuts/DirectCuts.lean` (the full cut construction of `Θ_cuts`)

This path is meant as a readability/compactness showcase and a cross-check against the grid/induction pipeline.

### Quick Reviewer Entry Point

If you want to understand the pipeline without reading the large induction files first, start at:

- `ProofSketch.lean` (compact dependency chain + pointers)
- `Main.lean` (public API theorem statements)
- `Globalization.lean` (the globalization construction; "triple family trick")

### 1. Base Case (k=1)
For a single atom `a > ident`, define `Θ(a^n) = n` and extend by density.

### 2. Induction Step (k → k+1)
Given a k-atom family with representation, extend to k+1 atoms:

1. **A/B/C Partition**: For new atom `d`, partition old grid values relative to
   `d^u` targets into sets A (below), B (equal), C (above)

2. **Case B Non-Empty**: The new atom is rationally related to existing atoms.
   Its value is determined algebraically.

3. **Case B Empty**: Use the **δ-choice procedure**:
   - Find `δ = sup{statistics from A} = inf{statistics from C}`
   - Prove δ satisfies the `DeltaSpec` (bounds A, B, C correctly)
   - Prove δ is unique via `DeltaSpec_unique`

### 3. Globalization ("Triple Family Trick")
Define a global `Θ : α → ℝ` independent of auxiliary choices:
- For any `x ≠ ident`, build a 2-atom family `{ref, x}` to get `Θ(x)`
- Well-definedness: Use 3-atom families to show independence of reference atom
- Additivity: Use path independence across different extension orderings

## Directory Structure

```
RepresentationTheorem/
├── README.md                # This file
├── ProofSketch.lean          # Reviewer entry point (dependency chain + pointers)
├── Main.lean                # Public API: representation theorem + corollaries
├── Globalization.lean       # Globalization construction (`RepresentationGlobalization`)
├── Alternative/             # Alternative proof path (Dedekind cuts)
│   ├── Main.lean            # Public API: `associativity_representation_cuts`
│   └── DirectCuts.lean      # Cut-based Θ construction (`Θ_cuts`)
├── Core/                    # Induction machinery (see Core/README.md)
│   ├── All.lean             # Aggregates all Core exports
│   ├── Prelude.lean         # Basic setup, imports
│   ├── MultiGrid.lean       # k-dimensional grids, μ function, A/B/C sets
│   ├── SeparationImpliesCommutative.lean  # Bridge: global comm from KSSeparation
│   └── Induction/           # The B-empty extension step
│       ├── Construction.lean    # Witness types, DeltaSpec
│       ├── DeltaShift.lean      # δ-shift consistency
│       ├── ThetaPrime.lean      # chooseδ procedure
│       ├── Goertzel.lean        # Separation-driven simplifications + extension theorem
│       ├── KSSeparationBridge.lean  # Bridge: KSSeparation supplies commutativity
│       └── HypercubeGap.lean    # Hypercube-theoretic gap analysis
├── Counterexamples/         # Non-commutative counterexamples
├── Explorations/            # Non-counterexample notes (interval approach, failed model attempts)
├── CredalSets.lean          # Credal set interpretation
├── DesirableGambles.lean    # Desirable gambles connection
```

## Key Components

### Main.lean
- `RepresentationGlobalization`: Class packaging the globalization step
- `representationGlobalization_of_KSSeparationStrict`: Instance construction
- `associativity_representation`: The main theorem
- `op_comm_of_associativity`: Commutativity as corollary

### Core/MultiGrid.lean
- `AtomFamily α k`: A family of k distinct atoms
- `Multi k = Fin k → ℕ`: Multi-indices for grid points
- `mu F r`: The grid point `a₀^r₀ ⊕ a₁^r₁ ⊕ ... ⊕ aₖ₋₁^rₖ₋₁`
- `kGrid F`: The set of all `mu F r` values
- `MultiGridRep F`: A representation restricted to grid F

### Core/Induction/
- `DeltaSpec`: Specification that δ must satisfy (A-bound, B-consistency, C-bound)
- `chooseδ`: The δ-choice procedure using sup/inf
- `extend_grid_rep_with_atom_of_KSSeparationStrict`: **The main extension lemma**

## Axiom Classes

```lean
-- Base axioms: ordered associative monoid (no inverses, no commutativity assumed)
class KnuthSkillingAlgebraBase (α : Type*) extends LinearOrder α where
  op : α → α → α
  ident : α
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  op_ident_right : ∀ a, op a ident = a
  op_ident_left : ∀ a, op ident a = a
  op_strictMono_left : ∀ a, StrictMono (op a)
  op_strictMono_right : ∀ a, StrictMono (fun b => op b a)
  ident_le : ∀ a, ident ≤ a

-- KnuthSkillingAlgebra is an alias for the base (no Archimedean axiom)
-- Archimedean is DERIVED from KSSeparation, not assumed.
abbrev KnuthSkillingAlgebra := KnuthSkillingAlgebraBase

-- The Archimedean property (derived from KSSeparation, NOT an axiom):
-- theorem op_archimedean_of_separation [KSSeparation α] (a x : α) (ha : ident < a) :
--   ∃ n : ℕ, x < Nat.iterate (op a) n a

-- Separation: the "rational density" strengthening used throughout Appendix A
class KSSeparation (α : Type*) [KnuthSkillingAlgebraBase α] : Prop where
  separation :
    ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
      ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m

-- Strict separation: strengthens the upper bound to be strict (`a^n < y^m`)
class KSSeparationStrict (α : Type*) [KnuthSkillingAlgebraBase α] extends KSSeparation α : Prop where
  separation_strict :
    ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
      ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n < iterate_op y m
```

## The Hypercube Connection

The A/B/C partition in the K&S proof corresponds to **modal types** in the
Stay-Wells hypercube framework:

| K&S Concept | Hypercube Interpretation |
|-------------|-------------------------|
| Set A (below) | `⟨C_<⟩_{d,u} Below` - modal type "reachable below" |
| Set B (equal) | `⟨C_=⟩_{d,u} Equal` - modal type "exactly equal" |
| Set C (above) | `⟨C_>⟩_{d,u} Above` - modal type "reachable above" |
| δ-choice | Finding the **equational center** between A and C |
| Globalization | Moving to the **full hypercube vertex** |

See `HypercubeGap.lean` for the formalized connection.

## Build & Test

```bash
export LAKE_JOBS=1
lake build +KnuthSkilling.Additive.Proofs.GridInduction.Main
```

To build the cuts-based alternative:

```bash
export LAKE_JOBS=1
lake build +KnuthSkilling.Additive.Proofs.DirectCuts.Main
```

## Status

**Core build target** (2026-05 standalone repo):
- `lake build +KnuthSkilling.Additive.Proofs.GridInduction.Main`
- `lake build +KnuthSkilling.Additive.Proofs.DirectCuts.Main`

See the repository root README for repo-wide status notes, including the
explicit exploratory/scratch files that are not part of the reviewer-facing
entrypoint.

## Historical Notes

The refactored `Core/` hierarchy was created to:
1. Separate concerns cleanly
2. Enable incremental verification
3. Document the mathematical structure explicitly
4. Facilitate future extensions
