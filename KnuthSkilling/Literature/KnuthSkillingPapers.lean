import KnuthSkilling
import KnuthSkilling.Additive.Main

/-!
# Knuth–Skilling papers: formalization entry points

This file is a *map* from the “core K&S PDFs” to the Lean development already living under
`KnuthSkilling/`.

Local PDFs:
- Knuth & Skilling (2012), “Foundations of Inference”:
  `literature/KS_codex/Knuth_Skilling_2012_Foundations_of_Inference.pdf`.
- Skilling & Knuth (2019), “Symmetrical foundation for measure, probability and quantum theory”:
  `literature/KS_codex/Skilling_Knuth_2019_Symmetrical_Foundation.pdf`.

Lean entry points (project-relative paths):
- `KnuthSkilling/Core/Basic.lean` (high-level K&S structures)
- `KnuthSkilling/Core/Algebra.lean` (core algebra)
- `KnuthSkilling/Additive/Axioms/SandwichSeparation.lean` (sandwich separation: separation ⇒ commutativity)
- `_archive/ProbabilityTheory/KnuthSkilling/Separation/Derivation.lean`
  (WIP derivation of `KSSeparation`)
- `KnuthSkilling/Additive/Proofs/GridInduction/` (Appendix A grid/induction development)
- `KnuthSkilling/Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean` (Hölder embedding path)
- `ProbabilityTheory/AssociativityTheorem.lean` (context + alternative view)

Nothing in this file is “new mathematics”; it is a documentation-oriented import bridge so the
literature codex can refer to K&S-by-PDF without duplicating the main formalization.
-/

namespace KnuthSkilling.Literature

end KnuthSkilling.Literature
