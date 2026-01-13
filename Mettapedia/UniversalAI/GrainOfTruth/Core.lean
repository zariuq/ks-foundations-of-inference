import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.ReflectiveOracles.Basic

/-!
# Grain of Truth: Core Types

This file contains the small, dependency-light core definitions shared by the
`GrainOfTruth` development:

* `EnvironmentIndex`
* `ReflectiveEnvironmentClass`
* `PriorOverClass`

It exists to avoid circular imports between high-level “chapter structure” files
and the more technical measure-theory or learning-theory files.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal

/-- A stochastic policy is an `Agent` (assigns probabilities to actions). -/
abbrev StochasticPolicy := Agent

/-- Index into the class of reflective-oracle-computable environments.
    Each index corresponds to a probabilistic TM with oracle access. -/
abbrev EnvironmentIndex := ℕ

/-- The reflective environment class `M^O_refl`, parameterized by a reflective oracle `O`. -/
structure ReflectiveEnvironmentClass (O : Oracle) where
  /-- Enumeration of all environment indices in the class. -/
  members : ℕ → EnvironmentIndex
  /-- The class is countable and covers all oracle-computable environments. -/
  covers_computable : ∀ idx : EnvironmentIndex, ∃ n, members n = idx

/-- A prior distribution over the environment class.
    Must be lower semicomputable and have total mass ≤ 1. -/
structure PriorOverClass (O : Oracle) (M : ReflectiveEnvironmentClass O) where
  /-- Prior weight for environment index `i`. -/
  weight : EnvironmentIndex → ℝ≥0∞
  /-- Total weight is at most 1 (a semimeasure). -/
  tsum_le_one : (∑' i, weight i) ≤ 1
  /-- Each weight is positive (for grain of truth). -/
  positive : ∀ i, 0 < weight i

end Mettapedia.UniversalAI.GrainOfTruth

