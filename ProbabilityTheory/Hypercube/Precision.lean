/-!
# Precision of a family of probability observations

The label distinguishes agreement of all admissible probability readouts from
an unresolved choice among them. Its model-dependent interpretation is supplied
by each consumer; the label alone asserts no probability law.
-/
namespace ProbabilityTheory.Hypercube
inductive PrecisionAxis where
  | precise
  | imprecise
  deriving DecidableEq, Repr
end ProbabilityTheory.Hypercube
