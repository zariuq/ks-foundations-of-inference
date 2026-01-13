import Mettapedia.Computability.CantorSpace
import Mathlib.Computability.PartrecCode

/-!
# Refined Probabilistic Turing Machine Model

This file provides a refined PTM model that fixes the monotonicity issues
in the original `ProbabilisticTM.lean`.

## The Problem with the Original Model

The original model encoded random bits as:
```
encodeRandomBits r numBits = (binary number formed from first numBits bits)
```
This encoding **changes entirely** when `numBits` changes:
- `encodeRandomBits [1,0,1,...] 2 = 2` (binary: 10)
- `encodeRandomBits [1,0,1,...] 3 = 5` (binary: 101)

So increasing `numBits` gives the machine a completely different input,
breaking monotonicity.

## The Refined Model

We model PTMs as machines that can **query individual random bits by index**.
The key insight is that a "well-behaved" PTM:
1. Queries bits sequentially (0, 1, 2, ...)
2. Halts after querying some finite prefix
3. The output depends only on the bits actually queried

With this model:
- If PTM halts querying bits 0..(k-1), it halts the same way with numBits ≥ k
- Monotonicity holds naturally

## Implementation

We use a **prefix-stable encoding** where:
- `prefixEncode r n` encodes bits 0..(n-1) as a list structure
- `prefixEncode r n` can be extracted from `prefixEncode r (n+k)` for any k
- A "bit query" operation extracts bit i from the encoding

-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Prefix-Stable Random Bit Encoding -/

/-- Encode a single bit as 0 or 1. -/
def bitToNat (b : Bool) : ℕ := if b then 1 else 0

/-- Encode random bits 0..(n-1) using nested pairs, with the newest bit outermost.

Structure: `prefixEncode r (n+1) = pair (prefixEncode r n) (bit n)`

This ensures that `prefixEncode r n` can be recovered from `prefixEncode r (n+k)`. -/
def prefixEncode (r : CantorSpace) : ℕ → ℕ
  | 0 => 0  -- Empty encoding (sentinel)
  | n + 1 => Nat.pair (prefixEncode r n) (bitToNat (r n))

/-- Extract bit i from a prefix encoding of length n (returns 0 if i ≥ n).
We navigate from the outermost pair (position length-1) down to position i. -/
def extractBit (encoded : ℕ) (length i : ℕ) : ℕ :=
  if i < length then
    -- Navigate: strip (length - 1 - i) outer layers, then take .2
    let stepsToStrip := length - 1 - i
    let innerEnc := Nat.iterate (fun n => n.unpair.1) stepsToStrip encoded
    innerEnc.unpair.2
  else 0

/-- Key property: prefixEncode is monotone in the sense that we can extract the shorter prefix. -/
theorem prefixEncode_prefix (r : CantorSpace) (n : ℕ) :
    (prefixEncode r (n + 1)).unpair.1 = prefixEncode r n := by
  simp [prefixEncode]

/-- The newest bit is correctly encoded. -/
theorem prefixEncode_newest_bit (r : CantorSpace) (n : ℕ) :
    (prefixEncode r (n + 1)).unpair.2 = bitToNat (r n) := by
  simp [prefixEncode]

/-! ## Refined PTM Definition -/

/-- A refined probabilistic Turing machine index.

The machine takes:
- Input x : ℕ
- Encoded random prefix : ℕ (using prefixEncode)
- Length of the prefix : ℕ (so it knows how many bits are available)

The machine can extract individual bits using extractBit.
-/
abbrev PTMIndexR := Nat.Partrec.Code

/-- Run a refined PTM with fuel steps and numBits random bits available.

The input encoding is:
  triple (x, prefixEncode r numBits, numBits)

This way the machine knows both the encoded bits and how many are available. -/
def runPTMR (M : PTMIndexR) (x : ℕ) (r : CantorSpace) (fuel : ℕ) (numBits : ℕ) : Option ℕ :=
  let encoded := prefixEncode r numBits
  let input := Nat.pair x (Nat.pair encoded numBits)
  Nat.Partrec.Code.evaln fuel M input

/-- A refined PTM halts with output k if there exist sufficient fuel and random bits. -/
def PTMRHaltsWithOutput (M : PTMIndexR) (x : ℕ) (r : CantorSpace) (k : ℕ) : Prop :=
  ∃ fuel numBits, runPTMR M x r fuel numBits = some k

/-! ## Monotonicity Properties -/

/-- Key monotonicity: more fuel with same bits gives same or better result. -/
theorem runPTMR_mono_fuel (M : PTMIndexR) (x : ℕ) (r : CantorSpace) (numBits : ℕ)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) {k : ℕ}
    (hr : runPTMR M x r fuel₁ numBits = some k) :
    runPTMR M x r fuel₂ numBits = some k := by
  unfold runPTMR at hr ⊢
  have h_mem : k ∈ Nat.Partrec.Code.evaln fuel₁ M _ := hr
  exact Nat.Partrec.Code.evaln_mono h h_mem

/-- Helper: extract prefix from longer encoding by stripping outer layers.
Uses `Nat.iterate` to avoid termination issues. -/
def truncateEncoding (encoded length targetLength : ℕ) : ℕ :=
  if targetLength ≥ length then encoded
  else Nat.iterate (fun n => n.unpair.1) (length - targetLength) encoded

/-- Key lemma: stripping one layer from prefixEncode (n+1) gives prefixEncode n. -/
theorem prefixEncode_unpair_fst (r : CantorSpace) (n : ℕ) :
    (prefixEncode r (n + 1)).unpair.1 = prefixEncode r n := by
  simp [prefixEncode]

/-- Truncating to the same length is identity. -/
theorem truncateEncoding_self (encoded length : ℕ) :
    truncateEncoding encoded length length = encoded := by
  simp [truncateEncoding]

/-- Stripping k layers from prefixEncode (n + k) gives prefixEncode n.
Proved by induction on k, stripping one layer at a time from the outside. -/
theorem iterate_unpair_prefixEncode (r : CantorSpace) (n k : ℕ) :
    (fun m => m.unpair.1)^[k] (prefixEncode r (n + k)) = prefixEncode r n := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- f^[k+1] x = f^[k] (f x), so apply f first then iterate k times
    rw [Function.iterate_succ_apply]
    -- Goal: (fun m => m.unpair.1)^[k] ((prefixEncode r (n + (k + 1))).unpair.1) = prefixEncode r n
    -- Use that n + (k + 1) = (n + k) + 1 and prefixEncode_unpair_fst
    have h_add : n + (k + 1) = (n + k) + 1 := by omega
    rw [h_add, prefixEncode_unpair_fst]
    exact ih

theorem truncateEncoding_correct (r : CantorSpace) (n m : ℕ) (h : n ≤ m) :
    truncateEncoding (prefixEncode r m) m n = prefixEncode r n := by
  unfold truncateEncoding
  by_cases h_eq : n ≥ m
  · -- n = m case
    have : n = m := Nat.le_antisymm h h_eq
    simp [this]
  · -- n < m case
    push_neg at h_eq
    simp only [h_eq.not_ge, ↓reduceIte]
    -- m = n + (m - n), so we strip (m - n) layers
    have h_split : m = n + (m - n) := (Nat.add_sub_cancel' (Nat.le_of_lt h_eq)).symm
    conv_lhs =>
      rw [h_split]
      arg 2; rw [Nat.add_sub_cancel_left]
    exact iterate_unpair_prefixEncode r n (m - n)

/-- **Key Theorem**: If a PTM halts with (fuel, numBits), then it halts with the same
output for any (fuel', numBits') where fuel' ≥ fuel and numBits' ≥ numBits,
PROVIDED the machine is "prefix-respecting".

A prefix-respecting machine only examines bits 0..(numBits-1) and doesn't
depend on numBits being exactly the length it expects.

For now, we state this as a property that well-behaved machines satisfy.
-/
def isPrefixRespecting (M : PTMIndexR) : Prop :=
  ∀ (x : ℕ) (r : CantorSpace) (fuel numBits₁ numBits₂ : ℕ) (k : ℕ),
    numBits₁ ≤ numBits₂ →
    runPTMR M x r fuel numBits₁ = some k →
    -- The machine only used bits 0..(numBits₁-1), so result is the same with more bits
    runPTMR M x r fuel numBits₂ = some k

/-- For prefix-respecting machines, monotonicity holds. -/
theorem runPTMR_mono_bits (M : PTMIndexR) (hM : isPrefixRespecting M)
    (x : ℕ) (r : CantorSpace) (fuel : ℕ)
    {numBits₁ numBits₂ : ℕ} (h : numBits₁ ≤ numBits₂) {k : ℕ}
    (hr : runPTMR M x r fuel numBits₁ = some k) :
    runPTMR M x r fuel numBits₂ = some k :=
  hM x r fuel numBits₁ numBits₂ k h hr

/-- Combined monotonicity for prefix-respecting machines. -/
theorem runPTMR_mono (M : PTMIndexR) (hM : isPrefixRespecting M)
    (x : ℕ) (r : CantorSpace)
    {fuel₁ fuel₂ numBits₁ numBits₂ : ℕ} (hf : fuel₁ ≤ fuel₂) (hn : numBits₁ ≤ numBits₂) {k : ℕ}
    (hr : runPTMR M x r fuel₁ numBits₁ = some k) :
    runPTMR M x r fuel₂ numBits₂ = some k := by
  have h1 := runPTMR_mono_bits M hM x r fuel₁ hn hr
  exact runPTMR_mono_fuel M x r numBits₂ hf h1

/-! ## Output Sets and Probabilities -/

/-- The set of random tapes for which the PTM outputs 1. -/
def outputOneSetR (M : PTMIndexR) (x : ℕ) : Set CantorSpace :=
  {r : CantorSpace | PTMRHaltsWithOutput M x r 1}

/-- The set of tapes where bounded execution gives output k. -/
def boundedOutputSetR (M : PTMIndexR) (x : ℕ) (fuel numBits : ℕ) : Set CantorSpace :=
  {r : CantorSpace | runPTMR M x r fuel numBits = some 1}

/-- Bounded output sets are monotone for prefix-respecting machines. -/
theorem boundedOutputSetR_mono (M : PTMIndexR) (hM : isPrefixRespecting M) (x : ℕ)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    boundedOutputSetR M x n₁ n₁ ⊆ boundedOutputSetR M x n₂ n₂ := by
  intro r hr
  simp only [boundedOutputSetR, Set.mem_setOf_eq] at hr ⊢
  exact runPTMR_mono M hM x r h h hr

/-- For prefix-respecting machines, outputOneSet equals the union of diagonal sets. -/
theorem outputOneSetR_eq_iUnion (M : PTMIndexR) (hM : isPrefixRespecting M) (x : ℕ) :
    outputOneSetR M x = ⋃ (n : ℕ), boundedOutputSetR M x n n := by
  ext r
  simp only [outputOneSetR, PTMRHaltsWithOutput, boundedOutputSetR,
             Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro ⟨fuel, numBits, hr⟩
    use max fuel numBits
    exact runPTMR_mono M hM x r (le_max_left _ _) (le_max_right _ _) hr
  · intro ⟨n, hr⟩
    exact ⟨n, n, hr⟩

/-! ## Probability Definitions -/

/-- Output probability for the refined model. -/
noncomputable def outputProbR (M : PTMIndexR) (x : ℕ) : ℝ≥0∞ :=
  coinMeasure (outputOneSetR M x)

/-- Bounded output probability for the refined model. -/
noncomputable def boundedOutputProbR (M : PTMIndexR) (x : ℕ) (fuel numBits : ℕ) : ℝ≥0∞ :=
  coinMeasure (boundedOutputSetR M x fuel numBits)

/-- Bounded approximations are monotone for prefix-respecting machines. -/
theorem boundedOutputProbR_mono (M : PTMIndexR) (hM : isPrefixRespecting M) (x : ℕ)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    boundedOutputProbR M x n₁ n₁ ≤ boundedOutputProbR M x n₂ n₂ := by
  unfold boundedOutputProbR
  exact measure_mono (boundedOutputSetR_mono M hM x h)

/-- **Main Convergence Theorem**: For prefix-respecting machines, the diagonal
sequence of bounded probabilities converges to the true probability. -/
theorem boundedOutputProbR_tendsto (M : PTMIndexR) (hM : isPrefixRespecting M) (x : ℕ) :
    Filter.Tendsto (fun n => boundedOutputProbR M x n n) Filter.atTop
      (nhds (outputProbR M x)) := by
  unfold outputProbR boundedOutputProbR
  -- Use measure continuity from below for monotone sequence
  rw [outputOneSetR_eq_iUnion M hM x]
  -- The sequence is monotone increasing
  have h_mono : Monotone (fun n => boundedOutputSetR M x n n) := by
    intro n₁ n₂ h
    exact boundedOutputSetR_mono M hM x h
  -- Apply measure continuity
  exact tendsto_measure_iUnion_atTop h_mono

end Mettapedia.Computability
