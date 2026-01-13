/-
# Separation Machinery (Index Module)

This module groups the two separation-related developments:

- `Separation/SandwichSeparation.lean`: the iterate/power “sandwich” axiom (`KSSeparation`) on the
  core base structure, proving commutativity and Archimedean-style consequences.
- `Separation/Derivation.lean`: experimental attempt to derive `KSSeparation` from structured
  hypotheses (isolates the remaining hard step as `LargeRegimeSeparationSpec`).
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.SandwichSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.Derivation
