import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph

/-!
# Discrete Semantics for Bayesian Networks (WIP)

This file starts the "Bayesian networks meet PLN" bridge in the **finite/discrete** setting.

What we provide here (no probabilistic heavy-lifting yet):

* A discrete CPT interface: each node has a `PMF` conditional on its parents.
* The induced factor graph (one factor per node) whose unnormalized joint is the BN product form.

What is intentionally left for later (may require real work / sorries):

* Proving the BN product form is normalized (`partitionFunction = 1`) from acyclicity.
* Proving Markov / d-separation soundness using Mathlib's conditional independence API.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators ENNReal

namespace BayesianNetwork

open DirectedGraph ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (bn : BayesianNetwork V)

/-! ## Discrete CPTs -/

/-- Parent assignments as dependent functions on a *set of parents*. We avoid bundling into
`ParentConfig` to keep typeclass requirements light. -/
def ParentAssignment (v : V) : Type _ :=
  ∀ u : V, u ∈ bn.parents v → bn.stateSpace u

/-- A discrete conditional probability table: for each node `v` and parent assignment, a `PMF`
on `stateSpace v`. -/
structure DiscreteCPT where
  cpt : ∀ v : V, bn.ParentAssignment v → PMF (bn.stateSpace v)

namespace DiscreteCPT

variable {bn}

/-- The parent assignment induced by a full configuration `x`. -/
def parentAssignOfConfig (_cpt : bn.DiscreteCPT) (x : bn.JointSpace) (v : V) :
    bn.ParentAssignment v :=
  fun u _ => x u

/-- The conditional probability of the `v`-coordinate of a full configuration `x`,
given its parents under the CPT. -/
def nodeProb (cpt : bn.DiscreteCPT) (x : bn.JointSpace) (v : V) : ℝ≥0∞ :=
  cpt.cpt v (cpt.parentAssignOfConfig x v) (x v)

/-- The BN product-form weight of a full configuration. -/
noncomputable def jointWeight (cpt : bn.DiscreteCPT) (x : bn.JointSpace) : ℝ≥0∞ :=
  ∏ v : V, cpt.nodeProb x v

/-! ## Induced Factor Graph -/

section FactorGraph

variable [DecidableRel bn.graph.edges]

-- A finset version of the parents set.
private def parentsFinset (v : V) : Finset V :=
  (Finset.univ.filter fun u : V => bn.graph.edges u v)

private lemma mem_parentsFinset_iff (u v : V) :
    u ∈ parentsFinset (bn := bn) v ↔ bn.graph.edges u v := by
  classical
  simp [parentsFinset]

private lemma mem_parentsFinset_iff' (u v : V) :
    u ∈ parentsFinset (bn := bn) v ↔ u ∈ bn.parents v := by
  classical
  simpa [BayesianNetwork.parents, DirectedGraph.parents] using (mem_parentsFinset_iff (bn := bn) u v)

/-- The discrete factor graph induced by a BN + CPT:
one factor per node with scope `{v} ∪ parents(v)` and potential equal to the CPT probability. -/
noncomputable def toFactorGraph (cpt : bn.DiscreteCPT) : FactorGraph V where
  stateSpace := bn.stateSpace
  factors := V
  scope := fun v => insert v (parentsFinset (bn := bn) v)
  potential := fun v x =>
    -- Build the parent assignment from the factor-scope configuration.
    let pa : bn.ParentAssignment v := fun u hu =>
      x u (by
        -- `u ∈ parents(v)` implies `u ∈ scope(v)`.
        have : u ∈ parentsFinset (bn := bn) v := (mem_parentsFinset_iff' (bn := bn) u v).2 hu
        exact Finset.mem_insert_of_mem this)
    -- The value at the node itself is in the inserted scope.
    cpt.cpt v pa (x v (by simp))

theorem toFactorGraph_unnormalizedJoint_eq (cpt : bn.DiscreteCPT)
    (x : (toFactorGraph (bn := bn) cpt).FullConfig) :
    (toFactorGraph (bn := bn) cpt).unnormalizedJoint x = cpt.jointWeight x := by
  classical
  -- Both sides are products over nodes/factors; unfold and simplify the scope restriction.
  unfold FactorGraph.unnormalizedJoint DiscreteCPT.jointWeight DiscreteCPT.nodeProb
  simp [FactorGraph.restrictToScope, toFactorGraph, parentsFinset, parentAssignOfConfig]

end FactorGraph

end DiscreteCPT

end BayesianNetwork

end Mettapedia.ProbabilityTheory.BayesianNetworks
