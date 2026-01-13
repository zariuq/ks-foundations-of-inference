import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.Prelude
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.MultiGrid
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.Induction
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.OneDimensional
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.GrowthRateTheory
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.SeparationImpliesCommutative

/-!
Dependency-ordered import bundle for the full Appendix A core development.

The implementation is split into:
- `...Core.Prelude` (API + Phase 1)
- `...Core.MultiGrid` (Phases 2–3 up to the accuracy lemma)
- `...Core.Induction` (Phase 3 induction/extension machinery)
- `...Core.OneDimensional` (Representable → Commutative, COMPLETE)
- `...Core.GrowthRateTheory` (Growth rate comparisons without logarithms, COMPLETE)
- `...Core.SeparationImpliesCommutative` (KSSeparation → Commutative, COMPLETE)
-/
