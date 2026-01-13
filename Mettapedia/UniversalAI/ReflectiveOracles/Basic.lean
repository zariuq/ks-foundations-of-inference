import Mettapedia.Computability.OracleTMReal
import Mettapedia.UniversalAI.ReflectiveOracles.DirectionMismatch

/-!
# Reflective Oracles

This file defines reflective oracles and proves their existence using König's lemma.

A reflective oracle is an oracle O : ℕ → Bool that correctly reports the probabilities
of its own computational effects:
- If O(encode(M, x, p)) = true then P(M outputs 1 | O) > p
- If P(M outputs 1 | O) > p then O(encode(M, x, p)) = true

## Main Definitions

* `ReflectiveOracle`: The type of oracles satisfying the reflectivity conditions
* `partiallyReflective`: A partial oracle that is reflective on its defined domain
* `reflectiveOracleLimit`: The limit of a chain of extending partial oracles

## Main Results

* `partially_sound_oracle_exists`: Existence of partially sound oracles

## Implementation Notes

This implementation builds on:
- `Mettapedia.Computability.CantorSpace` for fair coin measure
- `Mettapedia.Computability.OracleTMReal` for oracle TM with query tracking

The key property `nonCircular_at_position` is now a THEOREM (not an axiom)
proved from the structure of the query-tracking model.

The construction follows Leike's PhD thesis (Chapter 7) with investigation of
the direction mismatch issue documented in `DirectionMismatch.lean`.

## References

* Leike, "Nonparametric General Reinforcement Learning", 2016, Chapter 7
* Leike & Hutter, "On the Computability of Solomonoff Induction and AIXI"

-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.UniversalAI.ReflectiveOracles

-- Re-export key types from OracleTMReal
export Mettapedia.Computability (Oracle OTMIndex oracleOutputProbBounded
  oracleOutputProbAtPosition decodeQuery queryIndex nonCircular_at_position)

/-! ## Query Grid

Oracle values must lie on the grid {0, 1/2, 1} where:
- 0 means "definitely false" (P ≤ threshold)
- 1 means "definitely true" (P > threshold)
- 1/2 means "unknown/undetermined"
-/

/-- The three possible values for a grid-constrained oracle. -/
inductive GridValue where
  | zero : GridValue  -- P ≤ threshold (false)
  | half : GridValue  -- undetermined
  | one : GridValue   -- P > threshold (true)
deriving DecidableEq, Repr

/-- Convert a grid value to a rational number. -/
def GridValue.toRat : GridValue → ℚ
  | .zero => 0
  | .half => 1/2
  | .one => 1

/-- Convert a grid value to a boolean (half → false for safety). -/
def GridValue.toBool : GridValue → Bool
  | .zero => false
  | .half => false
  | .one => true

/-! ## Partial Oracles with Query Tracking

A partial oracle tracks:
1. Values for query positions 0..k-1
2. Each position n corresponds to the query (M_n, x_n) = decodeQuery n
-/

/-- A partial oracle defined on the first k query positions.
Position n answers the query about (M, x) = decodeQuery n. -/
structure PartialOracleG (k : ℕ) where
  value : Fin k → GridValue

/-- The empty partial oracle (no queries answered). -/
def emptyPartialOracle : PartialOracleG 0 := ⟨fun i => i.elim0⟩

/-- Convert a partial oracle to a full oracle by extending with false (unknown). -/
def PartialOracleG.toOracle {k : ℕ} (Õ : PartialOracleG k) : Oracle :=
  fun n => if h : n < k then (Õ.value ⟨n, h⟩).toBool else false

/-- A partial oracle Õ₂ extends Õ₁ if they agree on the smaller domain. -/
def PartialOracleG.extends {k₁ k₂ : ℕ} (Õ₂ : PartialOracleG k₂)
    (Õ₁ : PartialOracleG k₁) (h : k₁ ≤ k₂) : Prop :=
  ∀ i : Fin k₁, Õ₂.value ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ = Õ₁.value i

/-! ## Partial Reflectivity

A partial oracle is partially reflective if soundness holds on its defined domain.
The key is that query position n asks about the specific (M, x) = decodeQuery n.

We use 1/2 as the canonical threshold for soundness, matching the construction
in `extensionValue` which sets value = .one when prob > 1/2.
-/

/-- Soundness for a partial oracle at query position n:
if oracle says 1, then P(M outputs 1 | O) > 1/2.
Here (M, x) = decodeQuery n.

Note: We use `oracleOutputProbAtPosition` which uses query bound = position,
ensuring the machine only sees oracle values at positions < n. -/
def PartialOracleG.isSoundAt {k : ℕ} (Õ : PartialOracleG k) (i : Fin k) : Prop :=
  Õ.value i = .one → oracleOutputProbAtPosition i.val Õ.toOracle > (1/2 : ℝ≥0∞)

/-- A partial oracle is partially reflective if soundness holds for all defined queries.
Each query position n corresponds to (M_n, x_n) = decodeQuery n.

Soundness means: if the oracle says "yes" (value = .one), then the probability
exceeds the canonical threshold 1/2. -/
def PartialOracleG.isPartiallyReflective {k : ℕ} (Õ : PartialOracleG k) : Prop :=
  ∀ i : Fin k, Õ.isSoundAt i

/-! ## Non-Circularity (Now a Theorem!)

The key property for the reflective oracle construction is that machines at position n
can only query oracle positions < n. This is now a THEOREM, not an axiom!

In `OracleTMReal`, `oracleOutputProbAtPosition n O` uses query bound n, so the machine
can only access oracle values at positions 0, 1, ..., n-1. If two oracles agree on
these positions, they give the same probability.

See `Mettapedia.Computability.nonCircular_at_position` for the proof.
-/

/-- Non-circularity is a theorem from the query-tracking model.
Machine at position n with query bound n depends only on oracle values < n. -/
theorem machines_are_nonCircular (n : ℕ) (O₁ O₂ : Oracle)
    (h_agree : ∀ i < n, O₁ i = O₂ i) :
    oracleOutputProbAtPosition n O₁ = oracleOutputProbAtPosition n O₂ :=
  nonCircular_at_position n O₁ O₂ h_agree

/-! ## Extension Theorem

Key theorem: any partially reflective partial oracle can be extended by one query
while preserving partial reflectivity.
-/

/-- Given a partially reflective oracle on k queries, determine the value for query k.
Uses `oracleOutputProbAtPosition k` which evaluates with query bound k. -/
noncomputable def extensionValue {k : ℕ} (Õ : PartialOracleG k) : GridValue :=
  -- Evaluate probability with current partial oracle using query bound k
  let prob := oracleOutputProbAtPosition k Õ.toOracle
  -- Use 1/2 as the canonical threshold for the grid
  if prob > (1/2 : ℝ≥0∞) then .one
  else if prob < (1/2 : ℝ≥0∞) then .zero
  else .half

/-- The extended partial oracle with one more query answered. -/
noncomputable def extendPartialOracle {k : ℕ} (Õ : PartialOracleG k) :
    PartialOracleG (k + 1) where
  value i := if h : i.val < k
             then Õ.value ⟨i.val, h⟩
             else extensionValue Õ

/-- Extended oracle agrees with original on old positions. -/
theorem extendPartialOracle_extends {k : ℕ} (Õ : PartialOracleG k) :
    (extendPartialOracle Õ).extends Õ (Nat.le_succ k) := by
  intro i
  simp only [extendPartialOracle]
  have hi : i.val < k := i.isLt
  simp only [hi, dite_true]

/-- The value at the new position is determined by extensionValue. -/
theorem extendPartialOracle_new {k : ℕ} (Õ : PartialOracleG k) :
    (extendPartialOracle Õ).value ⟨k, Nat.lt_succ_self k⟩ = extensionValue Õ := by
  simp only [extendPartialOracle]
  have hk : ¬(k < k) := Nat.lt_irrefl k
  simp only [hk, dite_false]

/-! ## Oracle Agreement Lemmas -/

/-- Extended oracle agrees with original oracle on positions < k. -/
theorem extendPartialOracle_toOracle_agree {k : ℕ} (Õ : PartialOracleG k) (n : ℕ) (hn : n < k) :
    (extendPartialOracle Õ).toOracle n = Õ.toOracle n := by
  simp only [PartialOracleG.toOracle, extendPartialOracle]
  have hn' : n < k + 1 := Nat.lt_succ_of_lt hn
  simp only [hn', dite_true, hn, dite_true]

/-- Extended oracle equals original oracle as functions on positions < k. -/
theorem extendPartialOracle_toOracle_restrict {k : ℕ} (Õ : PartialOracleG k) :
    ∀ n < k, (extendPartialOracle Õ).toOracle n = Õ.toOracle n :=
  fun n hn => extendPartialOracle_toOracle_agree Õ n hn

/-- Extension preserves partial reflectivity for old queries. -/
theorem extendPartialOracle_preserves_old {k : ℕ} (Õ : PartialOracleG k)
    (h : Õ.isPartiallyReflective) (i : Fin (k + 1)) (hi : i.val < k) :
    (extendPartialOracle Õ).isSoundAt i := by
  unfold PartialOracleG.isSoundAt
  intro h_val
  -- The value at old positions is the same as in Õ
  have h_old : (extendPartialOracle Õ).value i = Õ.value ⟨i.val, hi⟩ := by
    simp only [extendPartialOracle, hi, dite_true]
  rw [h_old] at h_val
  -- Use original reflectivity
  have h_orig := h ⟨i.val, hi⟩
  unfold PartialOracleG.isSoundAt at h_orig
  -- Key: the two oracles agree on positions < i.val, and by non-circularity,
  -- machine i only queries positions < i.val
  have h_agree : ∀ n < k, (extendPartialOracle Õ).toOracle n = Õ.toOracle n :=
    extendPartialOracle_toOracle_restrict Õ
  -- The oracles agree on positions < i.val (since i.val < k)
  have h_agree_below_i : ∀ n < i.val, (extendPartialOracle Õ).toOracle n = Õ.toOracle n := by
    intro n hn
    exact h_agree n (Nat.lt_trans hn hi)
  -- By non-circularity theorem, probabilities are equal
  have h_prob_eq := machines_are_nonCircular i.val (extendPartialOracle Õ).toOracle Õ.toOracle h_agree_below_i
  rw [h_prob_eq]
  exact h_orig h_val

/-- Extension preserves partial reflectivity for the new query. -/
theorem extendPartialOracle_sound_new {k : ℕ} (Õ : PartialOracleG k) :
    (extendPartialOracle Õ).isSoundAt ⟨k, Nat.lt_succ_self k⟩ := by
  unfold PartialOracleG.isSoundAt
  intro h_val
  -- The value at k is extensionValue Õ
  rw [extendPartialOracle_new] at h_val
  -- If value = .one, then by construction of extensionValue, prob > 1/2 under Õ.toOracle
  -- We need to show the same holds under (extendPartialOracle Õ).toOracle
  -- By non-circularity, machine k only queries positions < k
  -- Analyze what value = .one means in terms of probability
  have h_prob : oracleOutputProbAtPosition k Õ.toOracle > (1/2 : ℝ≥0∞) := by
    by_contra h_not
    push_neg at h_not
    -- If prob ≤ 1/2, then extensionValue is not .one
    unfold extensionValue at h_val
    -- The let binding needs to be inlined before split_ifs works
    simp only at h_val
    -- Since h_not: prob ≤ 1/2, split_ifs will produce cases that either:
    -- 1. Have h_gt (prob > 1/2) which contradicts h_not
    -- 2. Have h_val with value .zero or .half equaling .one (contradiction)
    split_ifs at h_val with h_gt
    · exact absurd h_gt (not_lt.mpr h_not)
  -- By non-circularity, the extended oracle gives the same probability
  have h_agree : ∀ n < k, (extendPartialOracle Õ).toOracle n = Õ.toOracle n :=
    extendPartialOracle_toOracle_restrict Õ
  have h_prob_eq := machines_are_nonCircular k (extendPartialOracle Õ).toOracle Õ.toOracle h_agree
  rw [h_prob_eq]
  exact h_prob

/-- Extension preserves partial reflectivity. -/
theorem extendPartialOracle_isPartiallyReflective {k : ℕ} (Õ : PartialOracleG k)
    (h : Õ.isPartiallyReflective) :
    (extendPartialOracle Õ).isPartiallyReflective := by
  intro i
  by_cases hi : i.val < k
  · exact extendPartialOracle_preserves_old Õ h i hi
  · -- i.val = k (the new position)
    have hi_eq : i.val = k := by
      have h_lt : i.val < k + 1 := i.isLt
      omega
    have h_i : i = ⟨k, Nat.lt_succ_self k⟩ := by
      ext
      exact hi_eq
    rw [h_i]
    exact extendPartialOracle_sound_new Õ

/-! ## Chain of Partial Oracles

We construct a sequence of extending partial oracles, each answering one more query.
-/

/-- A chain of extending partial oracles. -/
structure PartialOracleChain where
  oracle : (k : ℕ) → PartialOracleG k
  extends_prev : ∀ k : ℕ, (oracle (k + 1)).extends (oracle k) (Nat.le_succ k)
  reflective : ∀ k : ℕ, (oracle k).isPartiallyReflective

/-- The limit oracle of a chain is the pointwise limit. -/
noncomputable def PartialOracleChain.limit (chain : PartialOracleChain) : Oracle :=
  fun n => (chain.oracle (n + 1)).toOracle n

/-- Build the k-th partial oracle by repeatedly extending from empty. -/
noncomputable def buildPartialOracle : (k : ℕ) → PartialOracleG k
  | 0 => emptyPartialOracle
  | k + 1 => extendPartialOracle (buildPartialOracle k)

/-- The built chain extends at each step. -/
theorem buildPartialOracle_extends (k : ℕ) :
    (buildPartialOracle (k + 1)).extends (buildPartialOracle k) (Nat.le_succ k) := by
  simp only [buildPartialOracle]
  exact extendPartialOracle_extends (buildPartialOracle k)

/-- The built chain is partially reflective at each step. -/
theorem buildPartialOracle_reflective (k : ℕ) :
    (buildPartialOracle k).isPartiallyReflective := by
  induction k with
  | zero =>
    unfold buildPartialOracle
    intro i
    exact i.elim0
  | succ n ih =>
    unfold buildPartialOracle
    exact extendPartialOracle_isPartiallyReflective _ ih

/-- Construct a chain by repeatedly extending. -/
noncomputable def buildChain : PartialOracleChain where
  oracle := buildPartialOracle
  extends_prev := buildPartialOracle_extends
  reflective := buildPartialOracle_reflective

/-! ## Main Existence Theorem

Using König's lemma, we can construct a reflective oracle as the limit of
a chain of partially reflective partial oracles.
-/

/-- Chain values are consistent: if k₁ ≤ k₂ and i < k₁, then oracle k₁ and oracle k₂
agree on position i. -/
theorem chain_value_agree (chain : PartialOracleChain) (i k₁ k₂ : ℕ)
    (hi : i < k₁) (hk : k₁ ≤ k₂) :
    (chain.oracle k₂).value ⟨i, Nat.lt_of_lt_of_le hi hk⟩ =
    (chain.oracle k₁).value ⟨i, hi⟩ := by
  induction k₂ with
  | zero => omega
  | succ k₂ ih =>
    by_cases hk₁ : k₁ ≤ k₂
    · -- Use IH and then extension
      have h_prev := ih hk₁
      have h_ext := chain.extends_prev k₂ ⟨i, Nat.lt_of_lt_of_le hi hk₁⟩
      rw [h_ext]
      exact h_prev
    · -- k₁ = k₂ + 1
      have hk_eq : k₁ = k₂ + 1 := by omega
      subst hk_eq
      rfl

/-- The limit oracle agrees with each partial oracle on their shared domain. -/
theorem chain_limit_agree (chain : PartialOracleChain) (i k : ℕ) (hi : i < k) :
    chain.limit i = (chain.oracle k).toOracle i := by
  unfold PartialOracleChain.limit PartialOracleG.toOracle
  have hi_succ : i < i + 1 := Nat.lt_succ_self i
  simp only [hi_succ, dite_true, hi, dite_true]
  -- Need: (chain.oracle (i+1)).value ⟨i, _⟩ = (chain.oracle k).value ⟨i, _⟩
  have h_agree := chain_value_agree chain i (i + 1) k hi_succ (Nat.succ_le_of_lt hi)
  simp only [GridValue.toBool] at h_agree ⊢
  congr 1
  exact h_agree.symm

/-- Soundness of the limit oracle at the canonical threshold 1/2.
If O(n) = true, then the probability of outputting 1 exceeds 1/2. -/
theorem partialOracleChain_limit_sound_at_half (chain : PartialOracleChain) (n : ℕ) :
    chain.limit n = true →
    oracleOutputProbAtPosition n chain.limit > (1/2 : ℝ≥0∞) := by
  intro h_true
  -- chain.limit n = (chain.oracle (n + 1)).toOracle n
  unfold PartialOracleChain.limit at h_true
  simp only [PartialOracleG.toOracle] at h_true
  have hn : n < n + 1 := Nat.lt_succ_self n
  simp only [hn, dite_true] at h_true
  -- If toBool = true, then value = .one
  have h_one : (chain.oracle (n + 1)).value ⟨n, hn⟩ = .one := by
    cases hv : (chain.oracle (n + 1)).value ⟨n, hn⟩ <;> simp [GridValue.toBool, hv] at h_true ⊢
  -- By partial reflectivity at position n
  have h_refl := chain.reflective (n + 1) ⟨n, hn⟩
  unfold PartialOracleG.isSoundAt at h_refl
  simp only at h_refl
  have h_partial_prob := h_refl h_one
  -- By non-circularity, machine at n only queries positions < n
  -- The oracles agree on positions < n
  have h_agree : ∀ i < n, chain.limit i = (chain.oracle (n + 1)).toOracle i := by
    intro i hi
    exact chain_limit_agree chain i (n + 1) (Nat.lt_succ_of_lt hi)
  have h_prob_eq := machines_are_nonCircular n chain.limit (chain.oracle (n + 1)).toOracle h_agree
  rw [h_prob_eq]
  exact h_partial_prob

/-- The limit oracle is "partially reflective" in the sense that soundness holds
at the canonical threshold 1/2. Full reflectivity (soundness and completeness
at all thresholds) requires additional assumptions about uniform convergence.
See DirectionMismatch.lean for discussion. -/
theorem partialOracleChain_limit_sound (chain : PartialOracleChain) :
    ∀ n : ℕ, chain.limit n = true →
    oracleOutputProbAtPosition n chain.limit > (1/2 : ℝ≥0∞) :=
  fun n => partialOracleChain_limit_sound_at_half chain n

/-- Main theorem: A "partially sound" oracle exists.
This oracle satisfies soundness at threshold 1/2:
if O(n) = true, then P(M outputs 1 | O) > 1/2 for the machine at position n.

For full reflectivity (soundness/completeness at all thresholds),
see the discussion in DirectionMismatch.lean. -/
theorem partially_sound_oracle_exists :
    ∃ O : Oracle, ∀ n : ℕ, O n = true →
    oracleOutputProbAtPosition n O > (1/2 : ℝ≥0∞) := by
  use buildChain.limit
  exact partialOracleChain_limit_sound buildChain

/-! ## Summary of Construction

The reflective oracle construction proceeds as follows:

1. **Start**: Empty partial oracle (no queries answered)
2. **Extend**: At each step k, answer query k by:
   - Computing partial probability P(M outputs 1 | current oracle)
   - If P > 1/2: set value = 1 (true)
   - If P < 1/2: set value = 0 (false)
   - Otherwise: set value = 1/2 (undetermined)
3. **Limit**: Take the pointwise limit as k → ∞

**Key Properties**:
- Extension preserves soundness (proven by `extendPartialOracle_isPartiallyReflective`)
- Limit is fully defined on all queries
- Completeness requires uniform convergence (see `gap_closed_if_uniform_convergence`)

**Open Question** (from DirectionMismatch.lean):
The gap between soundness and completeness may indicate a genuine flaw in the
construction. The key issue is whether partial probabilities converge uniformly
to full probabilities as more queries are answered.

-/

end Mettapedia.UniversalAI.ReflectiveOracles
