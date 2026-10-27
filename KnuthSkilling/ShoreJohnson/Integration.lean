import KnuthSkilling.ShoreJohnson.GradientSeparability

/-!
# Minimizer transport along an atom-sum certificate

An `AtomSumCertificate` supplies a derivative identity and an exact value identity
up to a prior-dependent constant. This module transports minimizer observations
along that supplied value identity. It does not construct an antiderivative or
prove the value identity from the operator laws.
-/

namespace KnuthSkilling.ShoreJohnson.Integration

open KnuthSkilling.ShoreJohnson.Objective
open KnuthSkilling.ShoreJohnson.GradientSeparability
open KnuthSkilling.Information.InformationEntropy

/-- **Integration assumptions**: a candidate atom `d` whose derivative matches the
gradient kernel `g`, together with a constant shift term independent of `q`. -/
structure AtomSumCertificate (F : ObjectiveFunctional) (gr : GradientRepresentation F) where
  d : ℝ → ℝ → ℝ
  d_deriv :
    ∀ q p : ℝ, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (gr.g q p) q
  const : ∀ {n : ℕ}, ProbDist n → ℝ
  F_eq :
    ∀ {n : ℕ} (p q : ProbDist n),
      F.D q p = (∑ i : Fin n, d (q.p i) (p.p i)) + const p

/-- From the integration assumptions we obtain objective equivalence to an atom-sum objective. -/
theorem objEquiv_of_atomSumCertificate
    (F : ObjectiveFunctional) (gr : GradientRepresentation F)
    (h : AtomSumCertificate F gr) :
    ObjEquiv F (ofAtom h.d) := by
  intro n p C
  ext q
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hle' :
        (∑ i : Fin n, h.d (q.p i) (p.p i)) + h.const p ≤
          (∑ i : Fin n, h.d (q'.p i) (p.p i)) + h.const p := by
      simpa [h.F_eq (p := p) (q := q), h.F_eq (p := p) (q := q')] using hle
    have hle'' :
        (∑ i : Fin n, h.d (q.p i) (p.p i)) ≤
          (∑ i : Fin n, h.d (q'.p i) (p.p i)) :=
      (add_le_add_iff_right (h.const p)).1 hle'
    simpa [ofAtom] using hle''
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hle' :
        (∑ i : Fin n, h.d (q.p i) (p.p i)) + h.const p ≤
          (∑ i : Fin n, h.d (q'.p i) (p.p i)) + h.const p :=
      by simpa [ofAtom] using hle
    have hle'' :
        F.D q p ≤ F.D q' p := by
      simpa [h.F_eq (p := p) (q := q), h.F_eq (p := p) (q := q')] using hle'
    exact hle''

/-- Integration step packaged as existence of a sum-form objective equivalent to `F`. -/
theorem exists_sumForm_of_atomSumCertificate
    (F : ObjectiveFunctional) (gr : GradientRepresentation F)
    (h : AtomSumCertificate F gr) :
    ∃ d : ℝ → ℝ → ℝ, ObjEquiv F (ofAtom d) := by
  exact ⟨h.d, objEquiv_of_atomSumCertificate F gr h⟩

end KnuthSkilling.ShoreJohnson.Integration
