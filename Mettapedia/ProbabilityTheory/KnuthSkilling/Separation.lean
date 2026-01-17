/-
# Separation Machinery (Index Module)

This module groups the separation-related developments:

- `Separation/SandwichSeparation.lean`: the iterate/power "sandwich" axiom (`KSSeparation`) on the
  core base structure, proving commutativity and Archimedean-style consequences.
- `Separation/AnomalousPairs.lean`: the "no anomalous pairs" condition from ordered semigroup theory.
- `Separation/HolderEmbedding.lean`: Hölder embedding approach to the representation theorem
  (uses Eric Luap's OrderedSemigroups library).

**Archived**:
- `Separation/_archive/Derivation.lean`: experimental attempt to derive `KSSeparation` from structured
  hypotheses (superseded by the Hölder approach).
- `Separation/_archive/AlimovEmbedding.lean`: earlier partial Alimov embedding attempt (superseded
  by HolderEmbedding.lean which uses Eric Luap's proven theorems).
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.SandwichSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding
