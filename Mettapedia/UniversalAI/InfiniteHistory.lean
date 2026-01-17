import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite-history interaction core

This file defines a minimal measure-theoretic core for infinite histories using
Ionescu-Tulcea. The goal is to make "value = integral over trajectories" the
primitive notion, and derive finite-horizon or recursive views as lemmas later.

Positive example: if `reward : Prod Action Percept -> Real` is bounded and
`w : Nat -> Real` is
absolutely summable, then `fun traj => tsum (fun n => w n * reward (traj n))`
is bounded and integrable, so `value` is well-defined.

Negative example: if `reward` is unbounded or `w n = 1` (not summable), then the
trajectory utility need not be integrable, so `value` is not defined without
extra assumptions.
-/

namespace Mettapedia.UniversalAI.InfiniteHistory

universe u v uX

variable {Action : Type u} {Percept : Type v}
  [MeasurableSpace Action] [MeasurableSpace Percept]

abbrev TrajectoryOf (X : Nat -> Type uX) : Type uX :=
  (n : Nat) -> X n
abbrev PrefixOf (X : Nat -> Type uX) (n : Nat) : Type uX :=
  (i : Finset.Iic n) -> X i

abbrev StepFamily (Action : Type u) (Percept : Type v) : Nat -> Type (max u v) :=
  fun _ => Prod Action Percept
abbrev Trajectory (Action : Type u) (Percept : Type v) : Type (max u v) :=
  TrajectoryOf (StepFamily Action Percept)
abbrev Prefix (Action : Type u) (Percept : Type v) (n : Nat) : Type (max u v) :=
  PrefixOf (StepFamily Action Percept) n

instance prefixMeasurableSpace (Action : Type u) (Percept : Type v)
    [MeasurableSpace Action] [MeasurableSpace Percept] (n : Nat) :
    MeasurableSpace (Prefix Action Percept n) := by
  dsimp [Prefix]
  infer_instance

instance trajectoryMeasurableSpace (Action : Type u) (Percept : Type v)
    [MeasurableSpace Action] [MeasurableSpace Percept] :
    MeasurableSpace (Trajectory Action Percept) := by
  dsimp [Trajectory]
  infer_instance

instance prefixOfMeasurableSpace (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)] (n : Nat) : MeasurableSpace (PrefixOf X n) := by
  dsimp [PrefixOf]
  infer_instance

instance trajectoryOfMeasurableSpace (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)] : MeasurableSpace (TrajectoryOf X) := by
  dsimp [TrajectoryOf]
  infer_instance

/-- Combine a policy kernel and environment kernel into a step kernel. -/
noncomputable def stepKernel
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept) :
    (n : Nat) ->
      ProbabilityTheory.Kernel (Prefix Action Percept n) (StepFamily Action Percept (n + 1)) :=
  fun n => ProbabilityTheory.Kernel.compProd (pi n) (mu n)

instance stepKernel_isMarkov
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)] :
    (n : Nat) -> ProbabilityTheory.IsMarkovKernel
      (stepKernel (Action:=Action) (Percept:=Percept) pi mu n) := by
  intro n
  dsimp [stepKernel]
  infer_instance

noncomputable def trajKernelOf (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) :
    ProbabilityTheory.Kernel (PrefixOf X a) (TrajectoryOf X) :=
  ProbabilityTheory.Kernel.traj (κ := κ) a

noncomputable def trajMeasureOf (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (PrefixOf X a)) :
    MeasureTheory.Measure (TrajectoryOf X) :=
  MeasureTheory.Measure.bind mu0 (trajKernelOf (X := X) (κ := κ) a)

@[simp] theorem trajKernelOf_eq (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) :
    trajKernelOf (X := X) (κ := κ) a = ProbabilityTheory.Kernel.traj (κ := κ) a := rfl

@[simp] theorem trajMeasureOf_eq (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (PrefixOf X a)) :
    trajMeasureOf (X := X) (κ := κ) a mu0 =
      MeasureTheory.Measure.bind mu0 (ProbabilityTheory.Kernel.traj (κ := κ) a) := rfl

instance trajKernelOf_isMarkov (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) : ProbabilityTheory.IsMarkovKernel (trajKernelOf (X := X) (κ := κ) a) := by
  dsimp [trajKernelOf]
  infer_instance

instance trajMeasureOf_isProbability (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (PrefixOf X a))
    [MeasureTheory.IsProbabilityMeasure mu0] :
    MeasureTheory.IsProbabilityMeasure (trajMeasureOf (X := X) (κ := κ) a mu0) := by
  dsimp [trajMeasureOf]
  infer_instance

/-- Kernel on trajectories given a policy/environment kernel family. -/
noncomputable def trajKernel
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) :
    ProbabilityTheory.Kernel (Prefix Action Percept a) (Trajectory Action Percept) :=
  trajKernelOf (X := StepFamily Action Percept)
    (κ := stepKernel (Action:=Action) (Percept:=Percept) pi mu) a

/-- Measure on trajectories obtained by binding an initial prefix measure. -/
noncomputable def trajMeasure
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (Prefix Action Percept a)) :
    MeasureTheory.Measure (Trajectory Action Percept) :=
  trajMeasureOf (X := StepFamily Action Percept)
    (κ := stepKernel (Action:=Action) (Percept:=Percept) pi mu) a mu0

/-- Value of a utility under a trajectory measure. -/
noncomputable def value
    (P : MeasureTheory.Measure (Trajectory Action Percept))
    (U : Trajectory Action Percept -> Real) : Real :=
  MeasureTheory.integral P U

/-- Value induced by a policy/environment and an initial prefix measure. -/
noncomputable def valueFrom
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (Prefix Action Percept a))
    (U : Trajectory Action Percept -> Real) : Real :=
  value (Action:=Action) (Percept:=Percept)
    (trajMeasure (Action:=Action) (Percept:=Percept) pi mu a mu0) U

/-- Value from a concrete prefix using the trajectory kernel. -/
noncomputable def valueFromPrefix
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) (pref : Prefix Action Percept a)
    (U : Trajectory Action Percept -> Real) : Real :=
  MeasureTheory.integral ((trajKernel (Action:=Action) (Percept:=Percept) pi mu a) pref) U

end Mettapedia.UniversalAI.InfiniteHistory
