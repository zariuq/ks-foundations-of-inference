import KnuthSkilling.ShoreJohnson.Proof
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Finite Shore–Johnson inference laws

Inference is a relation: an impossible problem need not have an answer. Uniqueness
means at most one answer on the positive-reference, closed convex domain. Existence
is separate, and is proved for finite KL minimization on nonempty affine constraints.

SJ2 here is permutation invariance, SJ3 is two-block subset independence, and SJ4
is product-system independence. The paper numbers the last two III and IV in the
opposite order. These finite laws do not by themselves characterize relative entropy:
prior preservation is a separate law in the discrete correction.

References:
* Shore and Johnson (1980), https://doi.org/10.1109/TIT.1980.1056144
* Johnson and Shore (1983), https://zenodo.org/records/1281600
-/

namespace KnuthSkilling.ShoreJohnson.Inference

open Classical Finset BigOperators

open KnuthSkilling.Information.InformationEntropy
open KnuthSkilling.ShoreJohnson.Proof

/-! ## Basic operations on finite distributions -/

namespace ProbDist

variable {n : ℕ}

theorem dimension_pos (P : ProbDist n) : 0 < n := by
  cases n with
  | zero => simpa using P.sum_one
  | succ n => exact Nat.succ_pos n

/-- Permute a finite distribution by relabeling indices. -/
noncomputable def permute (σ : Equiv.Perm (Fin n)) (P : ProbDist n) : ProbDist n where
  p := fun i => P.p (σ⁻¹ i)
  nonneg := fun i => P.nonneg _
  sum_one := by
    classical
    -- Reindex the finite sum by the permutation.
    calc
      (∑ i : Fin n, P.p (σ⁻¹ i)) = ∑ i : Fin n, P.p i := by
        simpa using (Equiv.sum_comp (σ⁻¹) (fun i : Fin n => P.p i))
      _ = 1 := P.sum_one

theorem permute_apply (σ : Equiv.Perm (Fin n)) (P : ProbDist n) (i : Fin n) :
    (permute σ P).p i = P.p (σ⁻¹ i) := rfl

@[simp] theorem permute_inv_permute (σ : Equiv.Perm (Fin n)) (P : ProbDist n) :
    permute σ⁻¹ (permute σ P) = P := by
  ext i
  simp [permute]

@[simp] theorem permute_permute_inv (σ : Equiv.Perm (Fin n)) (P : ProbDist n) :
    permute σ (permute σ⁻¹ P) = P := by
  ext i
  simp [permute]

end ProbDist

namespace ProbDist

variable {n m : ℕ}

/-- Disjoint-union / two-block mixture of distributions on `Fin n` and `Fin m`.

This is the “subset independence” analogue of the product distribution `⊗`: it builds a
distribution on `Fin (n+m)` by weighting the left block by `w` and the right block by `1-w`.
-/
noncomputable def twoBlock (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) : ProbDist (n + m) where
  p := fun i =>
    match (finSumFinEquiv (m := n) (n := m)).symm i with
    | Sum.inl i₁ => w * P₁.p i₁
    | Sum.inr i₂ => (1 - w) * P₂.p i₂
  nonneg := by
    intro i
    cases h : (finSumFinEquiv (m := n) (n := m)).symm i with
    | inl i₁ =>
        simpa [h] using mul_nonneg hw0 (P₁.nonneg i₁)
    | inr i₂ =>
        have hw' : 0 ≤ 1 - w := sub_nonneg.mpr hw1
        simpa [h] using mul_nonneg hw' (P₂.nonneg i₂)
  sum_one := by
    let e := (finSumFinEquiv (m := n) (n := m)).symm
    let g : Fin n ⊕ Fin m → ℝ := fun s =>
      match s with | .inl i => w * P₁.p i | .inr j => (1-w) * P₂.p j
    change (∑ i, g (e i)) = 1
    rw [Equiv.sum_comp e g, Fintype.sum_sum_type]
    change (∑ i, w * P₁.p i) + (∑ j, (1-w) * P₂.p j) = 1
    rw [← Finset.mul_sum, ← Finset.mul_sum, P₁.sum_one, P₂.sum_one]
    ring

end ProbDist

/-! ## Product marginals -/

namespace ProbDistProd

variable {n m : ℕ}

@[ext] theorem ext (P Q : ProbDistProd n m) (h : ∀ i, P.p i = Q.p i) : P = Q := by
  cases P
  cases Q
  cases funext h
  rfl

/-- Left marginal of a distribution on `Fin n × Fin m`. -/
noncomputable def marginalLeft (P : ProbDistProd n m) : ProbDist n where
  p := fun i => ∑ j : Fin m, P.p (i, j)
  nonneg := by
    intro i
    exact Finset.sum_nonneg (fun j _ => P.nonneg (i, j))
  sum_one := by
    classical
    -- `∑ i (∑ j P(i,j)) = ∑ (i,j) P(i,j) = 1`.
    simpa [Fintype.sum_prod_type] using P.sum_one

/-- Right marginal of a distribution on `Fin n × Fin m`. -/
noncomputable def marginalRight (P : ProbDistProd n m) : ProbDist m where
  p := fun j => ∑ i : Fin n, P.p (i, j)
  nonneg := by
    intro j
    exact Finset.sum_nonneg (fun i _ => P.nonneg (i, j))
  sum_one := by
    rw [Finset.sum_comm]
    simpa [Fintype.sum_prod_type] using P.sum_one

@[simp] theorem marginalLeft_product (P : ProbDist n) (Q : ProbDist m) :
    marginalLeft (P ⊗ Q) = P := by
  ext i
  change (∑ j, P.p i * Q.p j) = P.p i
  rw [← Finset.mul_sum, Q.sum_one, mul_one]

@[simp] theorem marginalRight_product (P : ProbDist n) (Q : ProbDist m) :
    marginalRight (P ⊗ Q) = Q := by
  ext j
  change (∑ i, P.p i * Q.p j) = Q.p j
  rw [← Finset.sum_mul, P.sum_one, one_mul]

end ProbDistProd

/-! ## Constraint sets and basic constructors -/

/-- A constraint set is just a set of admissible posteriors. -/
abbrev ConstraintSet (n : ℕ) := Set (ProbDist n)

/-- A constraint set on a product space `Fin n × Fin m`. -/
abbrev ConstraintSetProd (n m : ℕ) := Set (ProbDistProd n m)

namespace ConstraintSet

variable {n : ℕ}

/-- Relabel constraints by permuting the state labels. -/
def permute (σ : Equiv.Perm (Fin n)) (C : ConstraintSet n) : ConstraintSet n :=
  {Q | ProbDist.permute σ⁻¹ Q ∈ C}

@[simp] theorem mem_permute (σ : Equiv.Perm (Fin n)) (C : ConstraintSet n) (q : ProbDist n) :
    ProbDist.permute σ q ∈ permute σ C ↔ q ∈ C := by simp [permute]

end ConstraintSet

namespace ConstraintSet

variable {n m : ℕ}

/-- Two-block constraint constructor: admissible posteriors are built by mixing admissible block
posteriors with a fixed block-mass `w`. -/
def twoBlock (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (C₁ : ConstraintSet n) (C₂ : ConstraintSet m) :
    ConstraintSet (n + m) :=
  {Q | ∃ q₁ ∈ C₁, ∃ q₂ ∈ C₂, Q = ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 q₁ q₂}

end ConstraintSet

namespace ConstraintSetProd

variable {n m : ℕ}

/-- Product constraint: constrain the left and right marginals independently. -/
def product (C₁ : ConstraintSet n) (C₂ : ConstraintSet m) : ConstraintSetProd n m :=
  {Q | ProbDistProd.marginalLeft Q ∈ C₁ ∧ ProbDistProd.marginalRight Q ∈ C₂}

end ConstraintSetProd

/-! ## Shore–Johnson inference methods and axioms -/

/-- An inference method: relation between a prior, admissible posteriors, and an inferred posterior.

We use a relation (not a function) so that **uniqueness** can be stated as an axiom (SJ1). -/
structure InferenceMethod where
  Infer : ∀ {n : ℕ}, ProbDist n → ConstraintSet n → ProbDist n → Prop
  InferProd : ∀ {n m : ℕ}, ProbDistProd n m → ConstraintSetProd n m → ProbDistProd n m → Prop

/-- Finite KL's regular problem domain. Empty regions are allowed here: uniqueness is
an at-most-one law, and existence requires a separate feasibility premise. -/
def Admissible {n : ℕ} (p : ProbDist n) (C : ConstraintSet n) : Prop :=
  (∀ i, 0 < p.p i) ∧ Convex ℝ ((fun q : ProbDist n => q.p) '' C) ∧
    IsClosed ((fun q : ProbDist n => q.p) '' C)

/-- The corresponding domain on a product state space. -/
def AdmissibleProd {n m : ℕ} (p : ProbDistProd n m) (C : ConstraintSetProd n m) : Prop :=
  (∀ i, 0 < p.p i) ∧ Convex ℝ ((fun q : ProbDistProd n m => q.p) '' C) ∧
    IsClosed ((fun q : ProbDistProd n m => q.p) '' C)

/-- An actual inference witness, independent of uniqueness. -/
def Solvable {n : ℕ} (I : InferenceMethod) (p : ProbDist n) (C : ConstraintSet n) : Prop :=
  ∃ q, I.Infer p C q

/-- The former totality requirement contradicts feasibility, already on one state.
This records the rejected interface without making it an available axiom bundle. -/
theorem unrestricted_totality_feasibility_impossible (I : InferenceMethod)
    (total : ∀ {n : ℕ} (p : ProbDist n) (C : ConstraintSet n), ∃! q, I.Infer p C q)
    (feasible : ∀ {n : ℕ} {p : ProbDist n} {C : ConstraintSet n} {q},
      I.Infer p C q → q ∈ C) : False := by
  obtain ⟨q, hq, _⟩ := total (ProbDist.pointMass (0 : Fin 1)) ∅
  exact feasible hq

/-- Shore–Johnson axioms (discrete).

This is intentionally an interface: it does not commit to any specific constraint language, only to
the *structural* invariance/independence requirements.
-/
structure ShoreJohnsonAxioms (I : InferenceMethod) : Prop where
  /-- SJ1: at most one answer on the admitted finite problem domain. -/
  unique :
    ∀ {n : ℕ} (p : ProbDist n) (C : ConstraintSet n), Admissible p C →
      ∀ q r, I.Infer p C q → I.Infer p C r → q = r

  /-- SJ1 (Uniqueness) on product spaces. -/
  uniqueProd :
    ∀ {n m : ℕ} (p : ProbDistProd n m) (C : ConstraintSetProd n m), AdmissibleProd p C →
      ∀ q r, I.InferProd p C q → I.InferProd p C r → q = r

  /-- Feasibility: inferred posteriors lie in the constraint set. -/
  feasible :
    ∀ {n : ℕ} {p : ProbDist n} {C : ConstraintSet n} {q : ProbDist n}, I.Infer p C q → q ∈ C

  /-- Feasibility on product spaces. -/
  feasibleProd :
    ∀ {n m : ℕ} {p : ProbDistProd n m} {C : ConstraintSetProd n m} {q : ProbDistProd n m},
      I.InferProd p C q → q ∈ C

  /-- SJ2 (Permutation invariance): relabeling the state space commutes with inference. -/
  perm_invariant :
    ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbDist n) (C : ConstraintSet n) (q : ProbDist n),
      I.Infer p C q → I.Infer (ProbDist.permute σ p) (ConstraintSet.permute σ C) (ProbDist.permute σ q)

  /-- SJ4 / Axiom III (System independence): independent constraints on each factor imply a product posterior. -/
  system_independent :
    ∀ {n m : ℕ} (p₁ : ProbDist n) (p₂ : ProbDist m)
      (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDistProd n m),
      Admissible p₁ C₁ → Admissible p₂ C₂ →
      I.Infer p₁ C₁ q₁ →
      I.Infer p₂ C₂ q₂ →
      I.InferProd (p₁ ⊗ p₂) (ConstraintSetProd.product C₁ C₂) q →
      q = (q₁ ⊗ q₂)

  /-- SJ3 / Axiom IV (Subset independence), two-block disjoint-union form.

If the “information” decomposes by disjoint subsets (here: `Fin n` and `Fin m` inside
`Fin (n+m)`), and we additionally fix the block masses via the mixture weight `w`, then inference
commutes with building the combined distribution.

This statement is intentionally **constraint-language agnostic**: constraints are modeled as
sets of admissible posteriors, and `ConstraintSet.twoBlock` is the canonical constructor for
“separate constraints on each block + fixed block mass”.
-/
  subset_independent_twoBlock :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
      (p₁ : ProbDist n) (p₂ : ProbDist m)
      (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m)),
      Admissible p₁ C₁ → Admissible p₂ C₂ →
      I.Infer p₁ C₁ q₁ →
      I.Infer p₂ C₂ q₂ →
      I.Infer (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 p₁ p₂)
        (ConstraintSet.twoBlock (n := n) (m := m) w hw0 hw1 C₁ C₂) q →
      q = ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 q₁ q₂

/-- The discrete correction's null-information law; it is separate from SJ1--SJ4. -/
def PriorPreservation (I : InferenceMethod) : Prop :=
  ∀ {n : ℕ} (p : ProbDist n), (∀ i, 0 < p.p i) → I.Infer p Set.univ p

theorem not_infer_empty {I : InferenceMethod} (h : ShoreJohnsonAxioms I)
    {n : ℕ} (p q : ProbDist n) : ¬ I.Infer p ∅ q := fun hi => h.feasible hi

theorem unique_of_solvable {I : InferenceMethod} (h : ShoreJohnsonAxioms I)
    {n : ℕ} (p : ProbDist n) (C : ConstraintSet n)
    (ha : Admissible p C) (hs : Solvable I p C) : ∃! q, I.Infer p C q := by
  obtain ⟨q, hq⟩ := hs
  exact ⟨q, hq, fun r hr => h.unique p C ha r q hr hq⟩

end KnuthSkilling.ShoreJohnson.Inference
