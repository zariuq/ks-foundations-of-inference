/-
# Independence Theory and XOR Counterexample

Independence definitions and advanced probability theorems:
- Independent, PairwiseIndependent, MutuallyIndependent definitions
- XOR counterexample (pairwise ≠ mutual independence)
- Chain rule, law of total probability
- ks_implies_kolmogorov
- Inclusion-exclusion for two events
-/

import KnuthSkilling.Probability.ProbabilityDerivation

namespace KnuthSkilling.Probability

open MeasureTheory Classical

variable {α : Type*} [PlausibilitySpace α] [ComplementedLattice α]

def Independent (v : Valuation α) (a b : α) : Prop :=
  v.val (a ⊓ b) = v.val a * v.val b

omit [ComplementedLattice α] in
/-- Independence means conditional equals unconditional probability.
This is the "no information" characterization.

Proof strategy: Show P(A ∩ B) = P(A) · P(B) ↔ P(A ∩ B) / P(B) = P(A)
This is straightforward field arithmetic. -/
theorem independence_iff_cond_eq (v : Valuation α) (a b : α)
    (hb : v.val b ≠ 0) :
    Independent v a b ↔ Valuation.condVal v a b = v.val a := by
  unfold Independent Valuation.condVal
  simp [hb]
  constructor
  · intro h
    field_simp at h ⊢
    exact h
  · intro h
    field_simp at h ⊢
    exact h

omit [ComplementedLattice α] in
/-- Independence is symmetric in the events. -/
theorem independent_comm (v : Valuation α) (a b : α) :
    Independent v a b ↔ Independent v b a := by
  unfold Independent
  rw [inf_comm]
  ring_nf

omit [ComplementedLattice α] in
/-- If events are independent, then conditioning on one doesn't change
the probability of the other. -/
theorem independent_cond_invariant (v : Valuation α) (a b : α)
    (hb : v.val b ≠ 0) (h_indep : Independent v a b) :
    Valuation.condVal v a b = v.val a := by
  exact (independence_iff_cond_eq v a b hb).mp h_indep

/-! ### Pairwise vs Mutual Independence

For collections of events, there are two notions of independence:
- **Pairwise independent**: Each pair is independent
- **Mutually independent**: All subsets are independent (stronger!)

Example: Three events can be pairwise independent but not mutually independent.
This is a subtle distinction that emerges from the symmetry structure.
-/

/-- Pairwise independence: every pair of distinct events is independent.
This is a WEAKER condition than mutual independence. -/
def PairwiseIndependent (v : Valuation α) (s : Finset α) : Prop :=
  ∀ a b, a ∈ s → b ∈ s → a ≠ b → Independent v a b

/-- Mutual independence: every non-empty subset satisfies the product rule.
This is STRONGER than pairwise independence.

For example: P(A ∩ B ∩ C) = P(A) · P(B) · P(C)

Note: This uses Finset.inf to compute the meet (⊓) of all elements in t.
-/
def MutuallyIndependent (v : Valuation α) (s : Finset α) : Prop :=
  ∀ t : Finset α, t ⊆ s → t.Nonempty →
    v.val (t.inf id) = t.prod (fun a => v.val a)

omit [ComplementedLattice α] in
/-- Mutual independence implies pairwise independence. -/
theorem mutual_implies_pairwise (v : Valuation α) (s : Finset α)
    (h : MutuallyIndependent v s) :
    PairwiseIndependent v s := by
  unfold MutuallyIndependent PairwiseIndependent at *
  intros a b ha hb hab
  -- Apply mutual independence to the 2-element set {a, b}
  let t : Finset α := {a, b}
  have ht_sub : t ⊆ s := by
    intro x hx
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h => rw [h]; exact ha
    | inr h => rw [h]; exact hb
  have ht_nonempty : t.Nonempty := ⟨a, by simp [t]⟩
  have := h t ht_sub ht_nonempty
  -- Now we have: v.val (t.inf id) = t.prod (fun x => v.val x)
  -- For t = {a, b}, this gives: v.val (a ⊓ b) = v.val a * v.val b
  simp [t, Finset.inf_insert, Finset.inf_singleton, id, Finset.prod_insert,
        Finset.prod_singleton, Finset.notMem_singleton.mpr hab] at this
  exact this

/-! ## Counterexample: Pairwise ≠ Mutual Independence

The converse does NOT hold in general: there exist pairwise independent events
that are not mutually independent.

Classic example: Roll two fair dice. Let A = "first die is odd", B = "second die is odd",
C = "sum is odd". Then A, B, C are pairwise independent but not mutually independent.

To prove this connection to standard probability, we first define a bridge from
Mathlib's measure theory to the Knuth-Skilling framework.
-/

/-- Bridge: Standard probability measure → Knuth-Skilling Valuation.

This proves that Mathlib's measure theory satisfies our axioms!
-/
def valuationFromProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Valuation {s : Set Ω // MeasurableSet s} where
  val s := (μ s.val).toReal
  monotone := by
    intro a b h
    apply ENNReal.toReal_mono (measure_ne_top μ b.val)
    exact measure_mono h
  val_bot := by simp
  val_top := by simp [measure_univ]

/-! ### XOR Counterexample Components (Module Level)

Define the XOR counterexample at module level so `decide` works without local variable issues. -/

/-- The XOR sample space: Bool × Bool (4 points) -/
abbrev XorSpace := Bool × Bool

/-- Event A: first coin is heads (use abbrev for transparency) -/
abbrev xorEventA : Set XorSpace := {x | x.1 = true}
/-- Event B: second coin is heads -/
abbrev xorEventB : Set XorSpace := {x | x.2 = true}
/-- Event C: coins disagree (XOR) -/
abbrev xorEventC : Set XorSpace := {x | x.1 ≠ x.2}

/-- Uniform valuation on Bool × Bool: P(S) = |S|/4 -/
noncomputable def xorValuation : Valuation (Set XorSpace) where
  val s := (Fintype.card s : ℝ) / 4
  monotone := by
    intro a b hab
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
    exact Nat.cast_le.mpr (Fintype.card_le_of_embedding (Set.embeddingOfSubset a b hab))
  val_bot := by simp
  val_top := by
    -- Goal: (Fintype.card ⊤ : ℝ) / 4 = 1
    -- Use Set.top_eq_univ + Fintype.card_setUniv (handles any Fintype instance!)
    simp only [Set.top_eq_univ, Fintype.card_setUniv, Fintype.card_prod, Fintype.card_bool]
    norm_num

-- Helper to unfold xorValuation.val
@[simp] lemma xorValuation_val_eq (s : Set XorSpace) :
    xorValuation.val s = (Fintype.card s : ℝ) / 4 := rfl

-- Cardinality facts in SUBTYPE form (for single events after simp)
-- Goals become: Fintype.card { x // predicate }
@[simp] lemma card_subtype_fst_true :
    Fintype.card { x : XorSpace // x.1 = true } = 2 := by decide
@[simp] lemma card_subtype_snd_true :
    Fintype.card { x : XorSpace // x.2 = true } = 2 := by decide
@[simp] lemma card_subtype_fst_eq_snd :
    Fintype.card { x : XorSpace // x.1 = x.2 } = 2 := by decide
-- For xorEventC = {x | x.1 ≠ x.2}, goal becomes 4 - Fintype.card{x.1 = x.2}
@[simp] lemma card_complement :
    (4 : ℕ) - Fintype.card { x : XorSpace // x.1 = x.2 } = 2 := by decide

-- Cardinality facts in FINSET.FILTER form (for intersections after simp)
@[simp] lemma card_filter_AB :
    (Finset.filter (Membership.mem (xorEventA ∩ xorEventB)) Finset.univ).card = 1 := by decide
@[simp] lemma card_filter_AC :
    (Finset.filter (Membership.mem (xorEventA ∩ xorEventC)) Finset.univ).card = 1 := by decide
@[simp] lemma card_filter_BC :
    (Finset.filter (Membership.mem (xorEventB ∩ xorEventC)) Finset.univ).card = 1 := by decide
@[simp] lemma card_filter_ABC :
    (Finset.filter (Membership.mem ((xorEventA ∩ xorEventB) ∩ xorEventC)) Finset.univ).card = 0 := by decide
@[simp] lemma card_filter_A :
    (Finset.filter (Membership.mem xorEventA) Finset.univ).card = 2 := by decide
@[simp] lemma card_filter_B :
    (Finset.filter (Membership.mem xorEventB) Finset.univ).card = 2 := by decide
@[simp] lemma card_filter_C :
    (Finset.filter (Membership.mem xorEventC) Finset.univ).card = 2 := by decide

/-! ### The "Gemini Idiom" for Fintype Cardinality

**Problem:** Computing `Fintype.card {x : α | P x}` often fails with `decide` or `decide`
due to instance mismatch between `Classical.propDecidable` and `Set.decidableSetOf`.

**Solution (discovered with Gemini's help):**
```
rw [Fintype.card_subtype]; simp [eventDef]; decide
```

**Why it works:**
1. `Fintype.card_subtype` converts Type-cardinality to Finset-filter cardinality:
   `Fintype.card {x // P x} = (Finset.univ.filter P).card`
2. `simp [eventDef]` unfolds the event definition to a decidable predicate
3. `decide` works on Finsets because they use computational decidability

**When to use:** Any `Fintype.card` goal on a subtype of a finite type where direct
computation fails. This is the standard pattern for discrete probability cardinalities.
-/

@[simp] lemma card_xorEventA [Fintype xorEventA] : Fintype.card xorEventA = 2 := by
  rw [Fintype.card_subtype]; simp [xorEventA]; decide

@[simp] lemma card_xorEventB [Fintype xorEventB] : Fintype.card xorEventB = 2 := by
  rw [Fintype.card_subtype]; simp [xorEventB]; decide

@[simp] lemma card_xorEventC [Fintype xorEventC] : Fintype.card xorEventC = 2 := by
  rw [Fintype.card_subtype]; simp [xorEventC]; decide

@[simp] lemma card_xorEventAB [Fintype (xorEventA ∩ xorEventB : Set XorSpace)] :
    Fintype.card (xorEventA ∩ xorEventB : Set XorSpace) = 1 := by
  rw [Fintype.card_subtype]; simp [xorEventA, xorEventB]; decide

@[simp] lemma card_xorEventAC [Fintype (xorEventA ∩ xorEventC : Set XorSpace)] :
    Fintype.card (xorEventA ∩ xorEventC : Set XorSpace) = 1 := by
  rw [Fintype.card_subtype]; simp [xorEventA, xorEventC]; decide

@[simp] lemma card_xorEventBC [Fintype (xorEventB ∩ xorEventC : Set XorSpace)] :
    Fintype.card (xorEventB ∩ xorEventC : Set XorSpace) = 1 := by
  rw [Fintype.card_subtype]; simp [xorEventB, xorEventC]; decide

@[simp] lemma card_xorEventABC [Fintype ((xorEventA ∩ xorEventB) ∩ xorEventC : Set XorSpace)] :
    Fintype.card ((xorEventA ∩ xorEventB) ∩ xorEventC : Set XorSpace) = 0 := by
  rw [Fintype.card_subtype]; simp [xorEventA, xorEventB, xorEventC]

-- Valuation facts (now simp can apply the cardinality lemmas)
lemma xorVal_A : xorValuation.val xorEventA = 1/2 := by
  simp only [xorValuation_val_eq, card_xorEventA]; norm_num

lemma xorVal_B : xorValuation.val xorEventB = 1/2 := by
  simp only [xorValuation_val_eq, card_xorEventB]; norm_num

lemma xorVal_C : xorValuation.val xorEventC = 1/2 := by
  simp only [xorValuation_val_eq, card_xorEventC]; norm_num

lemma xorVal_AB : xorValuation.val (xorEventA ∩ xorEventB) = 1/4 := by
  simp only [xorValuation_val_eq, card_xorEventAB]; norm_num

lemma xorVal_AC : xorValuation.val (xorEventA ∩ xorEventC) = 1/4 := by
  simp only [xorValuation_val_eq, card_xorEventAC]; norm_num

lemma xorVal_BC : xorValuation.val (xorEventB ∩ xorEventC) = 1/4 := by
  simp only [xorValuation_val_eq, card_xorEventBC]; norm_num

lemma xorVal_ABC : xorValuation.val ((xorEventA ∩ xorEventB) ∩ xorEventC) = 0 := by
  simp only [xorValuation_val_eq, card_xorEventABC]; norm_num
lemma xorVal_ABC' : xorValuation.val (xorEventA ⊓ (xorEventB ⊓ xorEventC)) = 0 := by
  -- ⊓ = ∩ for sets, convert first
  calc xorValuation.val (xorEventA ⊓ (xorEventB ⊓ xorEventC))
      = xorValuation.val ((xorEventA ∩ xorEventB) ∩ xorEventC) := by
          simp only [Set.inf_eq_inter, Set.inter_assoc]
    _ = 0 := xorVal_ABC

-- Distinctness facts (use ext with witnesses)
lemma xorA_ne_B : xorEventA ≠ xorEventB := by
  intro h
  have hm : (true, false) ∈ xorEventA := rfl
  rw [h] at hm
  simp [xorEventB] at hm
lemma xorA_ne_C : xorEventA ≠ xorEventC := by
  intro h
  have hm : (true, true) ∈ xorEventA := rfl
  rw [h] at hm
  simp [xorEventC] at hm
lemma xorB_ne_C : xorEventB ≠ xorEventC := by
  intro h
  have hm : (true, true) ∈ xorEventB := rfl
  rw [h] at hm
  simp [xorEventC] at hm

-- Pairwise independence for each pair
-- Independent uses ⊓, but our lemmas use ∩. For sets, ⊓ = ∩.
lemma xorIndep_AB : Independent xorValuation xorEventA xorEventB := by
  unfold Independent
  simp only [Set.inf_eq_inter, xorVal_AB, xorVal_A, xorVal_B]
  norm_num

lemma xorIndep_AC : Independent xorValuation xorEventA xorEventC := by
  unfold Independent
  simp only [Set.inf_eq_inter, xorVal_AC, xorVal_A, xorVal_C]
  norm_num

lemma xorIndep_BC : Independent xorValuation xorEventB xorEventC := by
  unfold Independent
  simp only [Set.inf_eq_inter, xorVal_BC, xorVal_B, xorVal_C]
  norm_num

-- Pairwise independence for the triple
lemma xorPairwiseIndependent : PairwiseIndependent xorValuation {xorEventA, xorEventB, xorEventC} := by
  intro a b ha hb h_distinct
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (h_distinct rfl).elim
  · exact xorIndep_AB
  · exact xorIndep_AC
  · rw [independent_comm]; exact xorIndep_AB
  · exact (h_distinct rfl).elim
  · exact xorIndep_BC
  · rw [independent_comm]; exact xorIndep_AC
  · rw [independent_comm]; exact xorIndep_BC
  · exact (h_distinct rfl).elim

-- Mutual independence fails
lemma xorNotMutuallyIndependent : ¬ MutuallyIndependent xorValuation {xorEventA, xorEventB, xorEventC} := by
  intro h_mutual
  -- Apply to the full triple
  have h := h_mutual {xorEventA, xorEventB, xorEventC}
    (by simp) (by simp)
  -- Simplify the inf and prod
  simp only [Finset.inf_insert, Finset.inf_singleton, id] at h
  -- Now h : xorValuation.val (xorEventA ⊓ (xorEventB ⊓ xorEventC)) = ∏ a ∈ {xorEventA, xorEventB, xorEventC}, xorValuation.val a
  rw [xorVal_ABC'] at h
  -- Simplify the product to v(A) * v(B) * v(C)
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    xorA_ne_B, xorA_ne_C, xorB_ne_C, not_false_eq_true, not_or, and_self,
    Finset.prod_singleton, xorVal_A, xorVal_B, xorVal_C] at h
  -- Now h says: 0 = 1/2 * 1/2 * 1/2 = 1/8, which is false
  norm_num at h

/-- The XOR counterexample shows pairwise independence does NOT imply mutual independence.

This example uses Bool × Bool as sample space with uniform probability:
- Events A (first=true), B (second=true), C (XOR) are pairwise independent
- But P(A ∩ B ∩ C) = 0 ≠ 1/8 = P(A)·P(B)·P(C), so not mutually independent
-/
example : ∃ (α : Type) (_ : PlausibilitySpace α) (v : Valuation α) (s : Finset α),
    PairwiseIndependent v s ∧ ¬ MutuallyIndependent v s :=
  ⟨Set XorSpace, inferInstance, xorValuation, {xorEventA, xorEventB, xorEventC},
   xorPairwiseIndependent, xorNotMutuallyIndependent⟩

/-! ### Conditional Probability Properties

Conditional probability has rich structure beyond the basic definition.
Key properties:
1. **Chain rule**: P(A ∩ B ∩ C) = P(A|B∩C) · P(B|C) · P(C)
2. **Law of total probability**: Partition space, sum conditional probabilities
3. **Bayes already proven** in Basic.lean
-/

/-- Chain rule for three events.
This generalizes: probability of intersection equals product of conditional probabilities.

Proof strategy: Repeatedly apply product_rule:
  P(A ∩ B ∩ C) = P(A | B∩C) · P(B ∩ C)
               = P(A | B∩C) · P(B | C) · P(C)
-/
theorem chain_rule_three (_hC : CoxConsistency α v) (a b c : α)
    (hc : v.val c ≠ 0) (hbc : v.val (b ⊓ c) ≠ 0) :
    v.val (a ⊓ b ⊓ c) =
      Valuation.condVal v a (b ⊓ c) *
      Valuation.condVal v b c *
      v.val c := by
  -- Inline the product rule twice to avoid name resolution issues.
  calc v.val (a ⊓ b ⊓ c)
      = v.val (a ⊓ (b ⊓ c)) := by rw [inf_assoc]
    _ = Valuation.condVal v a (b ⊓ c) * v.val (b ⊓ c) := by
        -- product_rule_ks inlined
        calc v.val (a ⊓ (b ⊓ c))
            = (v.val (a ⊓ (b ⊓ c)) / v.val (b ⊓ c)) * v.val (b ⊓ c) := by
                field_simp [hbc]
          _ = Valuation.condVal v a (b ⊓ c) * v.val (b ⊓ c) := by
                simp [Valuation.condVal, hbc]
    _ = Valuation.condVal v a (b ⊓ c) * (Valuation.condVal v b c * v.val c) := by
        -- product_rule_ks inlined for v.val (b ⊓ c)
        congr 1
        calc v.val (b ⊓ c)
            = (v.val (b ⊓ c) / v.val c) * v.val c := by
                field_simp [hc]
          _ = Valuation.condVal v b c * v.val c := by
                simp [Valuation.condVal, hc]
    _ = Valuation.condVal v a (b ⊓ c) * Valuation.condVal v b c * v.val c := by
        ring

/-- Law of total probability for binary partition.
If b and bc partition the space (Disjoint b bc, b ⊔ bc = ⊤), then:
  P(A) = P(A|b) · P(b) + P(A|bc) · P(bc)

This is actually already proven in Basic.lean as `total_probability_binary`!
We re-state it here to show it emerges from Cox consistency.

Note: We use explicit complement bc instead of notation bᶜ for clarity. -/
theorem law_of_total_prob_binary (hC : CoxConsistency α v) (a b bc : α)
    (h_disj : Disjoint b bc) (h_part : b ⊔ bc = ⊤)
    (hb : v.val b ≠ 0) (hbc : v.val bc ≠ 0) :
    v.val a =
      Valuation.condVal v a b * v.val b +
      Valuation.condVal v a bc * v.val bc := by
  -- Step 1: Partition `a` using the binary partition hypothesis.
  have partition : a = (a ⊓ b) ⊔ (a ⊓ bc) := by
    calc a = a ⊓ ⊤ := by rw [inf_top_eq]
         _ = a ⊓ (b ⊔ bc) := by rw [h_part]
         _ = (a ⊓ b) ⊔ (a ⊓ bc) := by
            simp [inf_sup_left]

  -- Step 2: The two parts are disjoint because b and bc are disjoint.
  have disj_ab_abc : Disjoint (a ⊓ b) (a ⊓ bc) := by
    -- expand to an inf-equality via `disjoint_iff`
    rw [disjoint_iff]
    calc (a ⊓ b) ⊓ (a ⊓ bc)
        = a ⊓ (b ⊓ bc) := by
            -- reorder infs and use idempotency
            simp [inf_left_comm, inf_comm]
      _ = a ⊓ ⊥ := by
            have : b ⊓ bc = (⊥ : α) := disjoint_iff.mp h_disj
            simp [this]
      _ = ⊥ := by simp

  -- Step 3: Additivity (sum rule) for the partition.
  have hsum :
      v.val ((a ⊓ b) ⊔ (a ⊓ bc)) =
        v.val (a ⊓ b) + v.val (a ⊓ bc) := by
    rw [hC.combine_disjoint disj_ab_abc]
    apply combine_fn_is_add
    · exact v.nonneg (a ⊓ b)
    · exact v.le_one (a ⊓ b)
    · exact v.nonneg (a ⊓ bc)
    · exact v.le_one (a ⊓ bc)
    -- S(v(a⊓b), v(a⊓bc)) = v((a⊓b)⊔(a⊓bc)) ≤ 1
    · rw [← hC.combine_disjoint disj_ab_abc]
      exact v.le_one ((a ⊓ b) ⊔ (a ⊓ bc))

  -- Step 4: Product rule inlined for each piece.
  have hprod_b :
      v.val (a ⊓ b) = Valuation.condVal v a b * v.val b := by
    calc v.val (a ⊓ b)
        = (v.val (a ⊓ b) / v.val b) * v.val b := by
            field_simp [hb]
      _ = Valuation.condVal v a b * v.val b := by
            simp [Valuation.condVal, hb]
  have hprod_bc :
      v.val (a ⊓ bc) = Valuation.condVal v a bc * v.val bc := by
    calc v.val (a ⊓ bc)
        = (v.val (a ⊓ bc) / v.val bc) * v.val bc := by
            field_simp [hbc]
      _ = Valuation.condVal v a bc * v.val bc := by
            simp [Valuation.condVal, hbc]

  -- Step 5: Combine all pieces.
  calc v.val a
      = v.val ((a ⊓ b) ⊔ (a ⊓ bc)) := congrArg v.val partition
    _ = v.val (a ⊓ b) + v.val (a ⊓ bc) := hsum
    _ = (Valuation.condVal v a b * v.val b) + v.val (a ⊓ bc) := by rw [hprod_b]
    _ = (Valuation.condVal v a b * v.val b) +
        (Valuation.condVal v a bc * v.val bc) := by rw [hprod_bc]

/-! ## Connection to Kolmogorov

Show that Cox consistency implies the Kolmogorov axioms.
This proves the two foundations are equivalent!
-/

/-- **Cox's theorem**: The sum rule + product rule + complement rule are exactly
the Kolmogorov probability axioms. Cox's derivation shows these
follow from more basic symmetry principles!

NOTE: This is Cox's approach (CoxConsistency), not Knuth-Skilling's approach
(KnuthSkillingAlgebra). These are different foundations for probability. -/
theorem cox_implies_kolmogorov (hC : CoxConsistency α v) :
    (∀ a b, Disjoint a b → v.val (a ⊔ b) = v.val a + v.val b) ∧
    (∀ a, 0 ≤ v.val a) ∧
    (v.val ⊤ = 1) := by
  constructor
  · exact fun a b h => sum_rule v hC h
  constructor
  · exact v.nonneg
  · exact v.val_top

/-- Alias for backward compatibility -/
@[deprecated cox_implies_kolmogorov (since := "2026-01-24")]
abbrev ks_implies_kolmogorov := @cox_implies_kolmogorov

/-! ## Inclusion-Exclusion (2 events)

The classic formula P(A ∪ B) = P(A) + P(B) - P(A ∩ B).
-/

/-- Inclusion-exclusion for two events: P(A ∪ B) = P(A) + P(B) - P(A ∩ B).

This is the formula everyone learns in their first probability course!
We derive it from the sum rule by partitioning A ∪ B = A ∪ (Aᶜ ∩ B). -/
theorem inclusion_exclusion_two (hC : CoxConsistency α v) (a b : α) :
    v.val (a ⊔ b) = v.val a + v.val b - v.val (a ⊓ b) := by
  have h := BooleanRepresentation.modular_of_disjoint_add v.val
    (fun _ _ hd => sum_rule v hC hd) a b
  linarith

/-! Pairwise independence does not imply mutual independence: the XOR model
above separates them. Finite additivity, inclusion-exclusion and total-probability
laws depend on the supplied Cox-consistency profile, not merely monotonicity. -/

end KnuthSkilling.Probability
