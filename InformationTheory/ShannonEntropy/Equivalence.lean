import InformationTheory.ShannonEntropy.Faddeev
import InformationTheory.ShannonEntropy.ShannonKhinchin

/-!
# Entropy-preserving equivalence of axiom records

Conversions retain the supplied entropy function at every arity. Full continuity,
maximality and expansibility in the Shannon–Khinchin record are derived from the
Faddeev uniqueness theorem. The reverse conversion restricts full continuity.
The inverse laws use proof irrelevance for the axiom fields, not a choice of a
new entropy function. Inhabitedness is a separate corollary; clause counts alone
do not establish independence or minimality of either axiom system.
-/
namespace InformationTheory

def FaddeevEntropy.toShannonKhinchin (E : FaddeevEntropy) : ShannonKhinchinEntropy where
  H := E.H
  continuity := faddeev_full_continuity E
  symmetry := E.symmetry
  maximality := faddeev_maximality E
  expansibility := faddeev_expansibility E
  strong_additivity := E.recursivity
  normalization := E.normalization

def ShannonKhinchinEntropy.toFaddeev (E : ShannonKhinchinEntropy) : FaddeevEntropy where
  H := E.H
  continuous_binary := shannonKhinchin_continuous_binary E
  symmetry := E.symmetry
  recursivity := E.strong_additivity
  normalization := E.normalization

@[simp] theorem FaddeevEntropy.toShannonKhinchin_H (E : FaddeevEntropy) {n : ℕ} (p : ProbVec n) :
    E.toShannonKhinchin.H p = E.H p := rfl
@[simp] theorem ShannonKhinchinEntropy.toFaddeev_H (E : ShannonKhinchinEntropy) {n : ℕ} (p : ProbVec n) :
    E.toFaddeev.H p = E.H p := rfl

/-- Actual supplied axiom records correspond, retaining their entropy functions. -/
def faddeevShannonKhinchinEquiv : FaddeevEntropy ≃ ShannonKhinchinEntropy where
  toFun := FaddeevEntropy.toShannonKhinchin
  invFun := ShannonKhinchinEntropy.toFaddeev
  left_inv E := by cases E; rfl
  right_inv E := by cases E; rfl

theorem faddeev_implies_shannonKhinchin (E : FaddeevEntropy) :
    ∃ E' : ShannonKhinchinEntropy, ∀ (n : ℕ) (p : ProbVec n), E'.H p = E.H p :=
  ⟨E.toShannonKhinchin, fun _ _ => rfl⟩
theorem shannonKhinchin_implies_faddeev (E : ShannonKhinchinEntropy) :
    ∃ E' : FaddeevEntropy, ∀ (n : ℕ) (p : ProbVec n), E'.H p = E.H p :=
  ⟨E.toFaddeev, fun _ _ => rfl⟩

/-- Existence alone is weaker than the function-preserving equivalence above. -/
theorem faddeev_iff_shannonKhinchin :
    Nonempty FaddeevEntropy ↔ Nonempty ShannonKhinchinEntropy :=
  faddeevShannonKhinchinEquiv.nonempty_congr
end InformationTheory
