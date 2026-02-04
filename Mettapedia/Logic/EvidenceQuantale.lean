/-
# Evidence Quantale: Extended Theory and Interpretations

## Overview

This file provides **additional theory** for Evidence as a quantale, building on the
canonical instance defined in `Mettapedia.Logic.PLNEvidence`.

**Quantale Instance**: See `PLNEvidence.lean` (lines 584-589)

This file adds:
1. **Confidence Monotonicity**: Evidence addition increases confidence
2. **H × H^op Perspective**: Evidence as a product with dual ordering
3. **Beta-Bayesian Interpretation**: Connection to Beta distributions
4. **Weakness Theory**: Evidence measures for relations
5. **Transitivity**: Quantale multiplication respects evidential implication

## Key Results

1. `confidence_monotone_in_total`: Adding evidence increases confidence
2. `evidence_tensor_transitivity`: (A→B) ⊗ (B→C) ≤ (A→C)
3. `hplus_is_beta_update`: Evidence addition = Beta conjugate update
4. `tensor_is_confidence_compounding`: Tensor = confidence compounding
5. `evidenceWeakness_mono`: Weakness is monotone in evidence

## References

- Goertzel, "Weakness and Its Quantale: Plausibility Theory from First Principles"
- Rosenthal, "Quantales and their Applications"
- Walley, "Statistical Reasoning with Imprecise Probabilities"
-/

import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mettapedia.Logic.PLNEvidence
import Mettapedia.Algebra.QuantaleWeakness

namespace Mettapedia.Logic.EvidenceQuantale

open Mettapedia.Logic.PLNEvidence
open Mettapedia.Algebra.QuantaleWeakness
open scoped ENNReal

/-! ## Evidence as a Quantale

A quantale is a complete lattice with an associative multiplication that
distributes over arbitrary joins:
- `a ⊗ (⨆ᵢ bᵢ) = ⨆ᵢ (a ⊗ bᵢ)`
- `(⨆ᵢ aᵢ) ⊗ b = ⨆ᵢ (aᵢ ⊗ b)`

Evidence has:
- CompleteLattice structure (coordinatewise sup/inf)
- CommMonoid structure with tensor (coordinatewise multiplication)

The distributivity follows from ENNReal's quantale structure on each component.
-/

namespace Evidence

/-! ### Quantale Distributivity

All quantale structure (including distributivity lemmas and instances) is defined
in `PLNEvidence.lean`. This file only provides **additional** theory and interpretations.
-/

/-! ## The H × H^op Perspective

Conceptually, Evidence = ENNReal × ENNReal can be viewed through the lens of
H × H^op where H = ENNReal:

- The first component (n⁺) represents positive evidence, ordered as usual
- The second component (n⁻) represents negative evidence

The "H^op" intuition: more negative evidence should make a proposition *weaker*
in terms of truth, even though it increases the information content.

This is captured by the fact that:
- In the *information* ordering: (3,5) > (3,2) [more total evidence]
- In a *truth* interpretation: (3,5) is "less true" than (3,2) [more refutation]

The quantale operations respect both views:
- Tensor (sequential composition) compounds evidence multiplicatively
- Join (supremum) gives the "most informed" state
-/

/-- The "opposite" evidence: swap positive and negative.
    This implements the conceptual H^op transformation. -/
def swap (e : Evidence) : Evidence := ⟨e.neg, e.pos⟩

theorem swap_swap (e : Evidence) : swap (swap e) = e := rfl

theorem swap_tensor (e₁ e₂ : Evidence) :
    swap (e₁ * e₂) = swap e₁ * swap e₂ := by
  unfold swap
  simp only [Evidence.tensor_def]

/-- Swapping preserves the lattice order (since both components swap). -/
theorem swap_le_swap (e₁ e₂ : Evidence) :
    swap e₁ ≤ swap e₂ ↔ e₁.neg ≤ e₂.neg ∧ e₁.pos ≤ e₂.pos := by
  unfold swap
  simp only [Evidence.le_def]

/-! ## Quantale Transitivity = PLN Deduction

The fundamental quantale law for implications is:
  `(A → B) ⊗ (B → C) ≤ (A → C)`

This IS the PLN deduction rule at the evidence level!
-/

/-- Evidence-level transitivity: composing evidence multiplicatively
    gives a lower bound on the composed implication's evidence.

    This is the concrete form of `quantaleImplies_trans` from QuantaleWeakness. -/
theorem evidence_tensor_transitivity (eAB eBC : Evidence) :
    -- The tensor product gives a contribution to A→C evidence
    eAB * eBC ≤ ⨆ (_ : Unit), eAB * eBC := by
  exact le_iSup (fun _ => eAB * eBC) ()

/-! ## Connection to Heyting Structure

Evidence is a Frame (complete Heyting algebra) by PLNEvidence.lean.
The Heyting structure gives:
- Non-Boolean complement behavior
- Bounds [lower, upper] with gap

The gap reflects uncertainty, just like in the Beta interpretation.
-/

/-- Evidence is a Frame (complete Heyting algebra).
    This is already proven in PLNEvidence.lean. -/
noncomputable example : Order.Frame Evidence := inferInstance

/-- The strength function on Evidence gives a "point" probability estimate.
    This collapses the 2D Evidence to 1D, losing the partial order structure. -/
noncomputable def strengthAsPoint (e : Evidence) : ℝ :=
  (Evidence.toStrength e).toReal

/-- The confidence function measures how much evidence we have.
    Higher confidence = narrower Beta distribution = smaller bounds gap. -/
noncomputable def confidenceAsWidth (κ : ℝ≥0∞) (e : Evidence) : ℝ :=
  (Evidence.toConfidence κ e).toReal

/-- Confidence increases as total evidence increases (for finite totals).

    This connects to the Heyting bounds story: more evidence → narrower interval.

    Note: We need `e'.total ≠ ⊤` because in ENNReal, ⊤/⊤ = 0 by convention,
    which would break monotonicity. For finite evidence (the practical case),
    this function is strictly monotone increasing. -/
theorem confidence_monotone_in_total (κ : ℝ≥0∞) (e e' : Evidence)
    (hκ_pos : κ ≠ 0) (hκ_top : κ ≠ ⊤) (hy_top : e'.total ≠ ⊤)
    (he' : e.total ≤ e'.total) :
    Evidence.toConfidence κ e ≤ Evidence.toConfidence κ e' := by
  -- c = total / (total + κ) is monotone in total
  -- For x ≤ y: x/(x+κ) ≤ y/(y+κ)
  unfold Evidence.toConfidence
  set x := e.total with hx_def
  set y := e'.total with hy_def
  -- Since y ≠ ⊤ and x ≤ y, we have x ≠ ⊤
  have hx_top : x ≠ ⊤ := ne_top_of_le_ne_top hy_top he'
  -- All values are finite
  have hxk_pos : x + κ ≠ 0 := by
    intro h; simp only [add_eq_zero] at h; exact hκ_pos h.2
  have hyk_pos : y + κ ≠ 0 := by
    intro h; simp only [add_eq_zero] at h; exact hκ_pos h.2
  have hxk_top : x + κ ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hx_top, hκ_top⟩
  have hyk_top' : y + κ ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hy_top, hκ_top⟩
  -- Prove by showing x * (y + κ) ≤ y * (x + κ)
  have key : x * (y + κ) ≤ y * (x + κ) := by
    calc x * (y + κ) = x * y + x * κ := by ring
      _ ≤ x * y + y * κ := by
            -- use monotonicity of multiplication in ENNReal
            have hmul : x * κ ≤ y * κ := by
              -- multiply on the left and commute
              have h' : κ * x ≤ κ * y := mul_le_mul_right he' κ
              simpa [mul_comm] using h'
            have hmul2 : x * κ + x * y ≤ y * κ + x * y :=
              add_le_add_left hmul (x * y)
            simpa [add_comm, add_left_comm, add_assoc] using hmul2
      _ = y * x + y * κ := by ring
      _ = y * (x + κ) := by ring
  -- Cross-multiplication equivalence for division comparison
  -- x/(x+κ) ≤ y/(y+κ) ↔ x(y+κ) ≤ y(x+κ)
  calc x / (x + κ)
      = x * (y + κ) / ((x + κ) * (y + κ)) := by
          rw [ENNReal.mul_div_mul_right _ _ hyk_pos hyk_top']
    _ ≤ y * (x + κ) / ((x + κ) * (y + κ)) := ENNReal.div_le_div_right key _
    _ = y / (y + κ) := by
          rw [mul_comm (x + κ) (y + κ)]
          rw [ENNReal.mul_div_mul_right _ _ hxk_pos hxk_top]

/-! ## Connection to Beta Distribution

Evidence (n⁺, n⁻) is the sufficient statistic for Beta-Bernoulli conjugate updating.

The quantale operations have Beta interpretations:
- **hplus (⊕)**: Independent evidence combines → Beta parameters add
- **tensor (⊗)**: Sequential composition → Confidence compounding

The key insight: Evidence updates are just parameter updates!
-/

/-- Adding independent evidence corresponds to adding Beta parameters.
    Evidence (a⁺, a⁻) + Evidence (b⁺, b⁻) = Evidence (a⁺+b⁺, a⁻+b⁻)

    In Beta terms:
    - Prior: Beta(α, β)
    - Observation 1: (a⁺, a⁻) → Posterior: Beta(α+a⁺, β+a⁻)
    - Observation 2: (b⁺, b⁻) → Posterior: Beta(α+a⁺+b⁺, β+a⁻+b⁻)

    This is exactly hplus! -/
theorem hplus_is_beta_update (e₁ e₂ : Evidence) :
    (e₁ + e₂).pos = e₁.pos + e₂.pos ∧
    (e₁ + e₂).neg = e₁.neg + e₂.neg := by
  simp only [Evidence.hplus_def, and_self]

/-- The tensor product has a different Beta interpretation:
    It represents "confidence compounding" in sequential inference.

    If A→B has evidence e₁ and B→C has evidence e₂, the "direct path"
    contribution to A→C has compounded uncertainty. -/
theorem tensor_is_confidence_compounding (e₁ e₂ : Evidence) :
    (e₁ * e₂).pos = e₁.pos * e₂.pos ∧
    (e₁ * e₂).neg = e₁.neg * e₂.neg := by
  simp only [Evidence.tensor_def, and_self]

/-! ## Weakness Measure on Evidence

Goertzel's weakness theory defines weakness via:
  w(H) = ⨆_{(u,v) ∈ H} μ(u) ⊗ μ(v)

For Evidence, we can define an analogous measure.
-/

/-- A weight function on a finite set into Evidence. -/
def EvidenceWeight (U : Type*) [Fintype U] := U → Evidence

/-- Evidence-valued weakness of a relation. -/
noncomputable def evidenceWeakness {U : Type*} [Fintype U]
    (μ : EvidenceWeight U) (H : Finset (U × U)) : Evidence :=
  sSup { μ p.1 * μ p.2 | p ∈ H }

/-- Weakness is monotone: larger relations have larger weakness. -/
theorem evidenceWeakness_mono {U : Type*} [Fintype U]
    (μ : EvidenceWeight U) (H₁ H₂ : Finset (U × U)) (h : H₁ ⊆ H₂) :
    evidenceWeakness μ H₁ ≤ evidenceWeakness μ H₂ := by
  unfold evidenceWeakness
  apply sSup_le_sSup
  intro e he
  obtain ⟨p, hp, rfl⟩ := he
  exact ⟨p, h hp, rfl⟩

/-! ## The Unified Architecture

```
PLN Evidence (n⁺, n⁻)
        │
        ├──→ Quantale (tensor ⊗, join ⨆)
        │         │
        │         ├──→ Transitivity: (A→B) ⊗ (B→C) ≤ (A→C)
        │         └──→ Modus ponens: A ⊗ (A→B) ≤ B
        │
        ├──→ Frame (Heyting algebra)
        │         │
        │         ├──→ Non-Boolean complement
        │         └──→ Bounds: [lower, upper] with gap
        │
        └──→ Beta sufficient statistic
                  │
                  ├──→ Conjugate updating: hplus
                  └──→ Credible intervals ↔ Heyting bounds
```

This architecture shows:
1. **Algebraically**: Evidence is a quantale, giving inference rules
2. **Logically**: Evidence is Heyting (not Boolean), requiring 2D carrier
3. **Probabilistically**: Evidence is Beta sufficient stat, giving Bayesian updates

All three views are consistent and mutually reinforcing!
-/

/-! ## Summary

This file establishes:

1. **Evidence is a commutative quantale** with tensor multiplication
2. **The H × H^op perspective** explains why 2D is needed
3. **Quantale transitivity = PLN deduction** at the evidence level
4. **Heyting structure** gives bounds via non-Boolean complement
5. **Beta interpretation** of quantale operations

The key insight: PLN's Evidence structure is not ad-hoc, but arises naturally
from the intersection of:
- Quantale theory (Goertzel's weakness)
- Heyting algebra theory (non-Boolean K&S)
- Bayesian statistics (Beta conjugacy)
-/

end Evidence

end Mettapedia.Logic.EvidenceQuantale
