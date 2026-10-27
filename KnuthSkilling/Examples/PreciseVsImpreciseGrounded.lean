import KnuthSkilling.Bridges.Model
import KnuthSkilling.Probability.FiniteProbability
import ProbabilityTheory.Hypercube.Precision

/-!
# Grounded probabilities, observable precision and finite decisions

Atomic weights determine Boolean-event representations; normalization recovers
independently supplied probabilities. Precision concerns agreement of probability
answers, not equality of weight records. The credal example has genuine attained
utility minima. Expected-utility and maximin choice are supplied decision rules;
no preference representation theorem is assumed or claimed here.
-/

namespace KnuthSkilling.Examples.PreciseVsImpreciseGrounded
open Classical
open KnuthSkilling.Probability.BooleanRepresentation
open ProbabilityTheory.Hypercube

inductive State | safe | risky | catastrophic deriving DecidableEq
instance : Fintype State where
  elems := {.safe, .risky, .catastrophic}
  complete s := by cases s <;> simp
abbrev Event := Set State
inductive Action | normal | cautious deriving DecidableEq
open State Action

@[ext] structure KSGroundedProb where
  pSafe : ℝ
  pRisky : ℝ
  pCatastrophic : ℝ
  nonneg_safe : 0 ≤ pSafe
  nonneg_risky : 0 ≤ pRisky
  nonneg_cat : 0 ≤ pCatastrophic
  sum_one : pSafe + pRisky + pCatastrophic = 1

theorem sum_state (f : State → ℝ) : (∑ s, f s) = f safe + f risky + f catastrophic := by
  rw [show (Finset.univ : Finset State) = {safe, risky, catastrophic} from by
    ext s; cases s <;> simp]
  simp [add_assoc]

theorem sum_match_state (fa fb fc : ℝ) :
    (∑ s : State, match s with | .safe => fa | .risky => fb | .catastrophic => fc) =
    fa + fb + fc := sum_state _

noncomputable def lowRiskDist : KSGroundedProb :=
  ⟨179/200, 1/10, 1/200, by norm_num, by norm_num, by norm_num, by norm_num⟩
noncomputable def highRiskDist : KSGroundedProb :=
  ⟨17/20, 1/10, 1/20, by norm_num, by norm_num, by norm_num, by norm_num⟩

def KSGroundedProb.weights (P : KSGroundedProb) : State → ℝ
  | safe => P.pSafe | risky => P.pRisky | catastrophic => P.pCatastrophic

theorem KSGroundedProb.weights_nonneg (P : KSGroundedProb) (s : State) : 0 ≤ P.weights s := by
  cases s
  · exact P.nonneg_safe
  · exact P.nonneg_risky
  · exact P.nonneg_cat

@[simp] theorem KSGroundedProb.weights_sum (P : KSGroundedProb) : ∑ s, P.weights s = 1 := by
  simpa [weights, sum_match_state] using P.sum_one

noncomputable def KSGroundedProb.representation (P : KSGroundedProb) : KSBooleanRepresentation Event :=
  FiniteEvents.representation P.weights P.weights_nonneg

@[simp] theorem KSGroundedProb.representation_top (P : KSGroundedProb) :
    P.representation.Θ Set.univ = 1 := by simp [representation, FiniteEvents.representation]

theorem KSGroundedProb.probability_singleton (P : KSGroundedProb) (s : State) :
    P.representation.probability {s} = P.weights s := by
  simpa [representation] using FiniteEvents.probability_singleton
    P.weights P.weights_nonneg (by rw [P.weights_sum]; norm_num) s

noncomputable def lowRiskTheta : Event → ℝ := FiniteEvents.weight lowRiskDist.weights
noncomputable def highRiskTheta : Event → ℝ := FiniteEvents.weight highRiskDist.weights
noncomputable def lowRiskRep : KSBooleanRepresentation Event := lowRiskDist.representation
noncomputable def highRiskRep : KSBooleanRepresentation Event := highRiskDist.representation

theorem lowRiskTheta_nonneg : ∀ e, 0 ≤ lowRiskTheta e := lowRiskRep.Θ_nonneg
theorem highRiskTheta_nonneg : ∀ e, 0 ≤ highRiskTheta e := highRiskRep.Θ_nonneg
theorem lowRiskTheta_mono : ∀ a b, a ⊆ b → lowRiskTheta a ≤ lowRiskTheta b := lowRiskRep.Θ_mono
theorem highRiskTheta_mono : ∀ a b, a ⊆ b → highRiskTheta a ≤ highRiskTheta b := highRiskRep.Θ_mono
theorem lowRiskTheta_bot : lowRiskTheta ∅ = 0 := lowRiskRep.Θ_bot
theorem highRiskTheta_bot : highRiskTheta ∅ = 0 := highRiskRep.Θ_bot

theorem finset_sum_indicator_union_inter {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (s t : Set α) :
    (∑ x, if x ∈ s ∪ t then f x else 0) + (∑ x, if x ∈ s ∩ t then f x else 0) =
    (∑ x, if x ∈ s then f x else 0) + (∑ x, if x ∈ t then f x else 0) :=
  by
    convert FiniteEvents.weight_modular f s t using 2 <;>
      (apply Finset.sum_congr rfl; intro x _; split_ifs <;> rfl)

theorem lowRiskTheta_modular : ∀ a b,
    lowRiskTheta (a ∪ b) + lowRiskTheta (a ∩ b) = lowRiskTheta a + lowRiskTheta b := lowRiskRep.Θ_modular
theorem highRiskTheta_modular : ∀ a b,
    highRiskTheta (a ∪ b) + highRiskTheta (a ∩ b) = highRiskTheta a + highRiskTheta b := highRiskRep.Θ_modular

noncomputable def probDistFromKSRep (R : KSBooleanRepresentation Event) (h : R.Θ Set.univ ≠ 0) :
    KSGroundedProb where
  pSafe := R.probability {safe}
  pRisky := R.probability {risky}
  pCatastrophic := R.probability {catastrophic}
  nonneg_safe := R.probability_nonneg _
  nonneg_risky := R.probability_nonneg _
  nonneg_cat := R.probability_nonneg _
  sum_one := by simpa only [sum_state] using
    Probability.FiniteProbability.probability_sum_singletons_eq_one R h

@[simp] theorem extraction_representation (P : KSGroundedProb) :
    probDistFromKSRep P.representation (by rw [P.representation_top]; norm_num) = P := by
  ext <;> exact P.probability_singleton _

theorem lowRiskTheta_top_nonzero : lowRiskTheta Set.univ ≠ 0 := by
  change lowRiskDist.representation.Θ Set.univ ≠ 0; rw [lowRiskDist.representation_top]; norm_num
theorem highRiskTheta_top_nonzero : highRiskTheta Set.univ ≠ 0 := by
  change highRiskDist.representation.Θ Set.univ ≠ 0; rw [highRiskDist.representation_top]; norm_num

theorem lowRiskDist_grounded (h : lowRiskTheta Set.univ ≠ 0 := lowRiskTheta_top_nonzero) :
    (probDistFromKSRep lowRiskRep h).pSafe = 179/200 ∧
    (probDistFromKSRep lowRiskRep h).pRisky = 1/10 ∧
    (probDistFromKSRep lowRiskRep h).pCatastrophic = 1/200 := by
  simp [lowRiskRep, extraction_representation, lowRiskDist]
theorem highRiskDist_grounded (h : highRiskTheta Set.univ ≠ 0 := highRiskTheta_top_nonzero) :
    (probDistFromKSRep highRiskRep h).pSafe = 17/20 ∧
    (probDistFromKSRep highRiskRep h).pRisky = 1/10 ∧
    (probDistFromKSRep highRiskRep h).pCatastrophic = 1/20 := by
  simp [highRiskRep, extraction_representation, highRiskDist]

/-- All members have positive total weight, so every readout is a probability. -/
structure GroundedCredalSet (α : Type*) [BooleanAlgebra α] where
  representations : Set (KSBooleanRepresentation α)
  nonempty : representations.Nonempty
  positive_top : ∀ R ∈ representations, 0 < R.Θ ⊤

noncomputable def GroundedCredalSet.lowerProb {α : Type*} [BooleanAlgebra α]
    (C : GroundedCredalSet α) (a : α) : ℝ := sInf {R.probability a | R ∈ C.representations}
noncomputable def GroundedCredalSet.upperProb {α : Type*} [BooleanAlgebra α]
    (C : GroundedCredalSet α) (a : α) : ℝ := sSup {R.probability a | R ∈ C.representations}

abbrev CompletenessStatus := GroundedCredalSet
/-- Precision identifies answers, including weight records differing by units. -/
def GroundedCredalSet.isComplete {α : Type*} [BooleanAlgebra α] (C : CompletenessStatus α) : Prop :=
  ∀ R ∈ C.representations, ∀ S ∈ C.representations, R.probability = S.probability

noncomputable def hypercubePosition {α : Type*} [BooleanAlgebra α]
    (status : CompletenessStatus α) : PrecisionAxis :=
  if status.isComplete then .precise else .imprecise

theorem completeness_iff_precise {α : Type*} [BooleanAlgebra α] (status : CompletenessStatus α) :
    hypercubePosition status = .precise ↔ status.isComplete := by
  simp [hypercubePosition]

/-- Representation rescaling preserves every normalized event answer. -/
theorem probability_eq_of_scale {α : Type*} [BooleanAlgebra α]
    (R S : KSBooleanRepresentation α) (c : ℝ) (hc : 0 < c) (h : ∀ a, S.Θ a = c * R.Θ a) :
    S.probability = R.probability := by
  funext a
  by_cases hz : R.Θ ⊤ = 0
  · simp [KSBooleanRepresentation.probability, h, hz]
  · simp [KSBooleanRepresentation.probability, h, hz, ne_of_gt hc, mul_div_mul_left]

noncomputable def uncertaintyCredalSetReps : Set (KSBooleanRepresentation Event) :=
  {R | ∃ (_ : R.Θ Set.univ ≠ 0), R.probability {risky} = 1/10 ∧
    R.probability {catastrophic} ∈ Set.Icc (1/200) (1/20) ∧
    R.probability {safe} ∈ Set.Icc (17/20) (179/200)}

theorem lowRisk_mem : lowRiskRep ∈ uncertaintyCredalSetReps := by
  refine ⟨lowRiskTheta_top_nonzero, ?_⟩
  have h := lowRiskDist_grounded
  change lowRiskRep.probability {safe} = _ ∧ lowRiskRep.probability {risky} = _ ∧
    lowRiskRep.probability {catastrophic} = _ at h
  exact ⟨h.2.1, by rw [h.2.2]; norm_num, by rw [h.1]; norm_num⟩
theorem highRisk_mem : highRiskRep ∈ uncertaintyCredalSetReps := by
  refine ⟨highRiskTheta_top_nonzero, ?_⟩
  have h := highRiskDist_grounded
  change highRiskRep.probability {safe} = _ ∧ highRiskRep.probability {risky} = _ ∧
    highRiskRep.probability {catastrophic} = _ at h
  exact ⟨h.2.1, by rw [h.2.2]; norm_num, by rw [h.1]; norm_num⟩
theorem uncertaintyCredalSetReps_nonempty : uncertaintyCredalSetReps.Nonempty := ⟨_, lowRisk_mem⟩

noncomputable def uncertaintyGroundedCredalSet : GroundedCredalSet Event where
  representations := uncertaintyCredalSetReps
  nonempty := uncertaintyCredalSetReps_nonempty
  positive_top R h := lt_of_le_of_ne (R.Θ_nonneg _) (Ne.symm h.1)

theorem lowRiskDist_is_precise : ∃ status : CompletenessStatus Event,
    status.isComplete ∧ lowRiskRep ∈ status.representations ∧ hypercubePosition status = .precise := by
  let C : CompletenessStatus Event := ⟨{lowRiskRep}, ⟨_, rfl⟩, by
    intro R h; rcases h with rfl; exact lt_of_le_of_ne (lowRiskRep.Θ_nonneg _) lowRiskTheta_top_nonzero.symm⟩
  have h : C.isComplete := by intro R hR S hS; rcases hR with rfl; rcases hS with rfl; rfl
  exact ⟨C, h, rfl, (completeness_iff_precise C).mpr h⟩

theorem uncertaintyCredal_is_imprecise : ∃ status : CompletenessStatus Event,
    ¬status.isComplete ∧ uncertaintyCredalSetReps = status.representations ∧
      hypercubePosition status = .imprecise := by
  have h : ¬uncertaintyGroundedCredalSet.isComplete := by
    intro heq
    have hh := congrFun (heq _ lowRisk_mem _ highRisk_mem) {catastrophic}
    have hl := lowRiskDist_grounded.2.2
    have hr := highRiskDist_grounded.2.2
    change lowRiskRep.probability {catastrophic} = _ at hl
    change highRiskRep.probability {catastrophic} = _ at hr
    rw [hl, hr] at hh
    norm_num at hh
  exact ⟨uncertaintyGroundedCredalSet, h, rfl, by simp [hypercubePosition, h]⟩

theorem hypercube_positioning_theorem :
    (∃ status : CompletenessStatus Event, hypercubePosition status = .precise ∧ status.isComplete) ∧
    (∃ status : CompletenessStatus Event, hypercubePosition status = .imprecise ∧ ¬status.isComplete) :=
  ⟨let ⟨C, h, _, hp⟩ := lowRiskDist_is_precise; ⟨C, hp, h⟩,
   let ⟨C, h, _, hp⟩ := uncertaintyCredal_is_imprecise; ⟨C, hp, h⟩⟩

def utility : Action → State → ℝ
  | normal, safe => 100 | normal, risky => 50 | normal, catastrophic => -1000
  | cautious, safe => 80 | cautious, risky => 70 | cautious, catastrophic => 60

def expectedUtility (P : KSGroundedProb) (a : Action) : ℝ :=
  P.pSafe * utility a safe + P.pRisky * utility a risky + P.pCatastrophic * utility a catastrophic

/-- Bounds constrain normalized distributions, rather than independent coordinates. -/
structure KSCredalSet where
  pSafe_lo : ℝ
  pSafe_hi : ℝ
  pRisky_lo : ℝ
  pRisky_hi : ℝ
  pCat_lo : ℝ
  pCat_hi : ℝ
  safe_valid : pSafe_lo ≤ pSafe_hi
  risky_valid : pRisky_lo ≤ pRisky_hi
  cat_valid : pCat_lo ≤ pCat_hi
  all_nonneg : 0 ≤ pSafe_lo ∧ 0 ≤ pRisky_lo ∧ 0 ≤ pCat_lo
  nonempty : ∃ ps pr pc : ℝ, pSafe_lo ≤ ps ∧ ps ≤ pSafe_hi ∧
    pRisky_lo ≤ pr ∧ pr ≤ pRisky_hi ∧ pCat_lo ≤ pc ∧ pc ≤ pCat_hi ∧ ps + pr + pc = 1

def KSCredalSet.feasible (C : KSCredalSet) : Set KSGroundedProb :=
  {P | P.pSafe ∈ Set.Icc C.pSafe_lo C.pSafe_hi ∧
       P.pRisky ∈ Set.Icc C.pRisky_lo C.pRisky_hi ∧
       P.pCatastrophic ∈ Set.Icc C.pCat_lo C.pCat_hi}

theorem KSCredalSet.feasible_nonempty (C : KSCredalSet) : C.feasible.Nonempty := by
  obtain ⟨ps, pr, pc, hs, hs', hr, hr', hc, hc', he⟩ := C.nonempty
  exact ⟨⟨ps, pr, pc, C.all_nonneg.1.trans hs, C.all_nonneg.2.1.trans hr,
    C.all_nonneg.2.2.trans hc, he⟩, ⟨hs, hs'⟩, ⟨hr, hr'⟩, ⟨hc, hc'⟩⟩

theorem expectedUtility_bounded (P : KSGroundedProb) (a : Action) :
    -1000 ≤ expectedUtility P a ∧ expectedUtility P a ≤ 100 := by
  cases a <;> simp only [expectedUtility, utility] <;>
    constructor <;> nlinarith [P.sum_one, P.nonneg_safe, P.nonneg_risky, P.nonneg_cat]

noncomputable def worstCaseEU (C : KSCredalSet) (a : Action) : ℝ :=
  sInf ((fun P => expectedUtility P a) '' C.feasible)

theorem worstCase_le (C : KSCredalSet) (a : Action) (P : KSGroundedProb) (h : P ∈ C.feasible) :
    worstCaseEU C a ≤ expectedUtility P a := by
  exact csInf_le ⟨-1000, by rintro _ ⟨Q, _, rfl⟩; exact (expectedUtility_bounded Q a).1⟩ ⟨P, h, rfl⟩

theorem worstCase_eq (C : KSCredalSet) (a : Action) (P : KSGroundedProb) (hp : P ∈ C.feasible)
    (hmin : ∀ Q ∈ C.feasible, expectedUtility P a ≤ expectedUtility Q a) :
    worstCaseEU C a = expectedUtility P a := by
  exact (worstCase_le C a P hp).antisymm
    (le_csInf (C.feasible_nonempty.image _) (by rintro _ ⟨Q, hQ, rfl⟩; exact hmin Q hQ))

def maximinChoice (C : KSCredalSet) : Prop := worstCaseEU C cautious > worstCaseEU C normal

noncomputable def uncertaintyCredal : KSCredalSet :=
  ⟨17/20, 179/200, 1/10, 1/10, 1/200, 1/20, by norm_num, by norm_num, by norm_num,
    by norm_num, ⟨17/20, 1/10, 1/20, by norm_num⟩⟩

theorem highRisk_feasible : highRiskDist ∈ uncertaintyCredal.feasible := by
  norm_num [KSCredalSet.feasible, uncertaintyCredal, highRiskDist]

/-- Every feasible member has the same risky mass; both actions decrease with catastrophic mass. -/
theorem highRisk_minimizes (P : KSGroundedProb) (h : P ∈ uncertaintyCredal.feasible) (a : Action) :
    expectedUtility highRiskDist a ≤ expectedUtility P a := by
  have hr : P.pRisky = 1/10 := le_antisymm h.2.1.2 h.2.1.1
  have hc : P.pCatastrophic ≤ 1/20 := h.2.2.2
  cases a <;> simp only [expectedUtility, utility, highRiskDist] <;> nlinarith [P.sum_one]

theorem normal_worst : worstCaseEU uncertaintyCredal normal = 40 := by
  rw [worstCase_eq _ _ _ highRisk_feasible (fun P h => highRisk_minimizes P h normal)]
  norm_num [expectedUtility, utility, highRiskDist]
theorem cautious_worst : worstCaseEU uncertaintyCredal cautious = 78 := by
  rw [worstCase_eq _ _ _ highRisk_feasible (fun P h => highRisk_minimizes P h cautious)]
  norm_num [expectedUtility, utility, highRiskDist]
theorem lowRisk_EU_normal : expectedUtility lowRiskDist normal > expectedUtility lowRiskDist cautious := by
  norm_num [expectedUtility, utility, lowRiskDist]
theorem highRisk_EU_cautious : expectedUtility highRiskDist cautious > expectedUtility highRiskDist normal := by
  norm_num [expectedUtility, utility, highRiskDist]
theorem maximin_cautious : maximinChoice uncertaintyCredal := by
  unfold maximinChoice; rw [normal_worst, cautious_worst]; norm_num

theorem decisions_differ_grounded :
    expectedUtility lowRiskDist normal > expectedUtility lowRiskDist cautious ∧
    expectedUtility highRiskDist cautious > expectedUtility highRiskDist normal ∧
    maximinChoice uncertaintyCredal := ⟨lowRisk_EU_normal, highRisk_EU_cautious, maximin_cautious⟩

/-- Representation constraints and the normalized credal set have exactly the same members. -/
theorem uncertaintyCredal_matches_credalset (P : KSGroundedProb) :
    P ∈ uncertaintyCredal.feasible ↔ ∃ (R : KSBooleanRepresentation Event) (h : R.Θ Set.univ ≠ 0),
      R ∈ uncertaintyCredalSetReps ∧ probDistFromKSRep R h = P := by
  constructor
  · intro hp
    refine ⟨P.representation, by rw [P.representation_top]; norm_num, ?_, extraction_representation P⟩
    refine ⟨by rw [P.representation_top]; norm_num, ?_⟩
    simp only [P.probability_singleton, KSGroundedProb.weights]
    exact ⟨le_antisymm hp.2.1.2 hp.2.1.1, hp.2.2, hp.1⟩
  · rintro ⟨R, h, hR, rfl⟩
    change R.probability {safe} ∈ _ ∧ R.probability {risky} ∈ _ ∧ R.probability {catastrophic} ∈ _
    exact ⟨hR.2.2.2, by rw [hR.2.1]; constructor <;> rfl, hR.2.2.1⟩

/-- A genuine summary: extraction, different probability answers and attained minima. -/
theorem comprehensive_grounding :
    probDistFromKSRep lowRiskRep lowRiskTheta_top_nonzero = lowRiskDist ∧
    probDistFromKSRep highRiskRep highRiskTheta_top_nonzero = highRiskDist ∧
    lowRiskRep ∈ uncertaintyCredalSetReps ∧ highRiskRep ∈ uncertaintyCredalSetReps ∧
    (∀ P ∈ uncertaintyCredal.feasible, ∀ a, expectedUtility highRiskDist a ≤ expectedUtility P a) ∧
    maximinChoice uncertaintyCredal :=
  ⟨extraction_representation _, extraction_representation _, lowRisk_mem, highRisk_mem,
    highRisk_minimizes, maximin_cautious⟩

/-- Independent interval corners need not be normalized probability distributions. -/
theorem incompatible_corner : (2/5 : ℝ) + 0 + 1 ≠ 1 := by norm_num

noncomputable def cornerControl : KSCredalSet :=
  ⟨2/5, 1, 0, 1, 0, 1, by norm_num, by norm_num, by norm_num,
    by norm_num, ⟨2/5, 0, 3/5, by norm_num⟩⟩

/-- The old corner formula can exceed the genuine worst-case value. -/
theorem corner_score_not_worst_case :
    worstCaseEU cornerControl cautious ≤ 68 ∧ (2/5 : ℝ) * 80 + 1 * 60 = 92 := by
  let P : KSGroundedProb := ⟨2/5, 0, 3/5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hp : P ∈ cornerControl.feasible := by norm_num [KSCredalSet.feasible, cornerControl, P]
  constructor
  · have hh := worstCase_le cornerControl cautious P hp
    norm_num [expectedUtility, utility, P] at hh
    exact hh
  · norm_num

noncomputable def doubledLowRep : KSBooleanRepresentation Event :=
  FiniteEvents.representation (fun s => 2 * lowRiskDist.weights s)
    (fun s => mul_nonneg (by norm_num) (lowRiskDist.weights_nonneg s))

/-- Different supplied weight records give identical answers at every event. -/
theorem different_weights_same_probabilities :
    doubledLowRep ≠ lowRiskRep ∧ doubledLowRep.probability = lowRiskRep.probability := by
  have hd : doubledLowRep.Θ Set.univ = 2 := by
    simp only [doubledLowRep, FiniteEvents.representation, FiniteEvents.weight_univ]
    rw [← Finset.mul_sum, lowRiskDist.weights_sum, mul_one]
  constructor
  · intro heq
    have hl : lowRiskRep.Θ Set.univ = 1 := lowRiskDist.representation_top
    rw [heq, hl] at hd
    norm_num at hd
  · apply probability_eq_of_scale lowRiskRep doubledLowRep 2 (by norm_num)
    intro a
    simpa only [doubledLowRep, lowRiskRep, KSGroundedProb.representation,
      FiniteEvents.representation] using FiniteEvents.weight_scale lowRiskDist.weights 2 a

end KnuthSkilling.Examples.PreciseVsImpreciseGrounded
