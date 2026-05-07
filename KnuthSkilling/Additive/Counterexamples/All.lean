import KnuthSkilling.Additive.Counterexamples.BenV2Theorem1
import KnuthSkilling.Additive.Counterexamples.KSSeparationNotDerivable
import KnuthSkilling.Additive.Counterexamples.NegativeWithoutIdentity
import KnuthSkilling.Additive.Counterexamples.ProductFailsSeparation
import KnuthSkilling.Additive.Counterexamples.SemidirectNoSeparation

/-!
# Knuth–Skilling: Additive Counterexamples (Audit Target)

This module imports the additive counterexamples that are maintained as buildable audit artifacts
for the Knuth–Skilling representation theorem development.

Build this file to compile the entire counterexample suite in one go:

```bash
ulimit -Sv 6291456
cd lean-projects/mettapedia
export LAKE_JOBS=1
nice -n 19 lake build +KnuthSkilling.Additive.Counterexamples.All
```

Exploration notes and incomplete model attempts live elsewhere in the tree and are not imported by
this audit target.
-/
