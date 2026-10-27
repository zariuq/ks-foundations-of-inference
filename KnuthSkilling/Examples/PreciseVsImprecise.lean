import KnuthSkilling.Examples.PreciseVsImpreciseGrounded
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic

/-!
# Precise vs. Imprecise Probability (Toy Decision Example)

This file is a small, self-contained decision-theory example showing how different
decision criteria can lead to different recommendations when probabilities are not
known precisely.

## Setup

A decision problem with:
- 3 states of the world: Safe, Risky, Catastrophic
- 2 actions: Normal, Cautious
- Asymmetric payoffs (catastrophic outcome is very bad)

## What is shown

1. With precise probability, the optimal action depends sensitively on P(Catastrophic)
2. With interval uncertainty + maximin, the decision is robust (worst-case based)
3. There exist probability ranges where EU and maximin disagree
-/

namespace KnuthSkilling.Examples.PreciseVsImprecise

/-! ## §1: The Decision Problem -/

/-- States of the world -/
inductive State
  | safe        -- Everything is fine
  | risky       -- Some problems, manageable
  | catastrophic -- Very bad outcome
  deriving DecidableEq

/-- Available actions -/
inductive Action
  | normal   -- Business as usual
  | cautious -- Safety-first
  deriving DecidableEq

open State Action

/-! ## §2: Payoff Matrix (using rationals for exact computation) -/

/-- Payoff matrix using rationals for exact arithmetic.

| Action   | Safe | Risky | Catastrophic |
|----------|------|-------|--------------|
| Normal   | 100  | 50    | -1000        |
| Cautious | 80   | 70    | 60           |
-/
def payoff : Action → State → ℚ
  | normal, safe => 100
  | normal, risky => 50
  | normal, catastrophic => -1000
  | cautious, safe => 80
  | cautious, risky => 70
  | cautious, catastrophic => 60

/-! ## §3: Precise Probability -/

/-- A precise probability distribution over states (using rationals) -/
structure PreciseProb where
  pSafe : ℚ
  pRisky : ℚ
  pCatastrophic : ℚ
  nonneg_safe : 0 ≤ pSafe
  nonneg_risky : 0 ≤ pRisky
  nonneg_cat : 0 ≤ pCatastrophic
  sum_one : pSafe + pRisky + pCatastrophic = 1

namespace PreciseProb

/-- Expected utility of an action under a precise distribution -/
def expectedUtility (P : PreciseProb) (a : Action) : ℚ :=
  P.pSafe * payoff a safe + P.pRisky * payoff a risky + P.pCatastrophic * payoff a catastrophic

/-- Normal is better iff EU(normal) > EU(cautious) -/
def normalIsBetter (P : PreciseProb) : Prop :=
  P.expectedUtility normal > P.expectedUtility cautious

/-- Cautious is better iff EU(cautious) > EU(normal) -/
def cautiousIsBetter (P : PreciseProb) : Prop :=
  P.expectedUtility cautious > P.expectedUtility normal

/-- EU difference formula -/
theorem EU_diff_formula (P : PreciseProb) :
    P.expectedUtility normal - P.expectedUtility cautious =
    20 * P.pSafe - 20 * P.pRisky - 1060 * P.pCatastrophic := by
  simp only [expectedUtility, payoff]
  ring

end PreciseProb

/-- Rational calculations and real expected utilities agree under the explicit interpretation. -/
def PreciseProb.toGrounded (P : PreciseProb) : PreciseVsImpreciseGrounded.KSGroundedProb where
  pSafe := P.pSafe
  pRisky := P.pRisky
  pCatastrophic := P.pCatastrophic
  nonneg_safe := by exact_mod_cast P.nonneg_safe
  nonneg_risky := by exact_mod_cast P.nonneg_risky
  nonneg_cat := by exact_mod_cast P.nonneg_cat
  sum_one := by exact_mod_cast P.sum_one

theorem expectedUtility_cast (P : PreciseProb) (a : Action) :
    (P.expectedUtility a : ℝ) = PreciseVsImpreciseGrounded.expectedUtility P.toGrounded
      (match a with | .normal => .normal | .cautious => .cautious) := by
  cases a <;> simp [PreciseProb.expectedUtility, payoff, PreciseProb.toGrounded,
    PreciseVsImpreciseGrounded.expectedUtility, PreciseVsImpreciseGrounded.utility]

/-! ## §4: Example Distributions -/

/-- Low catastrophic risk: P(Cat) = 1/200 = 0.5% -/
def lowRiskDist : PreciseProb where
  pSafe := 179/200      -- 0.895
  pRisky := 1/10        -- 0.1
  pCatastrophic := 1/200  -- 0.005
  nonneg_safe := by norm_num
  nonneg_risky := by norm_num
  nonneg_cat := by norm_num
  sum_one := by norm_num

/-- High catastrophic risk: P(Cat) = 1/20 = 5% -/
def highRiskDist : PreciseProb where
  pSafe := 17/20        -- 0.85
  pRisky := 1/10        -- 0.1
  pCatastrophic := 1/20   -- 0.05
  nonneg_safe := by norm_num
  nonneg_risky := by norm_num
  nonneg_cat := by norm_num
  sum_one := by norm_num

/-- At low risk, Normal wins -/
theorem lowRisk_normal_wins : lowRiskDist.normalIsBetter := by
  unfold PreciseProb.normalIsBetter PreciseProb.expectedUtility payoff lowRiskDist
  norm_num

/-- At high risk, Cautious wins -/
theorem highRisk_cautious_wins : highRiskDist.cautiousIsBetter := by
  unfold PreciseProb.cautiousIsBetter PreciseProb.expectedUtility payoff highRiskDist
  norm_num

/-! ## §5: Imprecise Probability -/

/-- Imprecise probability: intervals for state probabilities -/
structure ImpreciseProb where
  pSafe_lo : ℚ
  pSafe_hi : ℚ
  pRisky_lo : ℚ
  pRisky_hi : ℚ
  pCat_lo : ℚ
  pCat_hi : ℚ
  safe_valid : pSafe_lo ≤ pSafe_hi
  risky_valid : pRisky_lo ≤ pRisky_hi
  cat_valid : pCat_lo ≤ pCat_hi
  all_nonneg : 0 ≤ pSafe_lo ∧ 0 ≤ pRisky_lo ∧ 0 ≤ pCat_lo
  nonempty : ∃ ps pr pc : ℝ, (pSafe_lo : ℝ) ≤ ps ∧ ps ≤ pSafe_hi ∧
    (pRisky_lo : ℝ) ≤ pr ∧ pr ≤ pRisky_hi ∧ (pCat_lo : ℝ) ≤ pc ∧ pc ≤ pCat_hi ∧ ps + pr + pc = 1

namespace ImpreciseProb

/-- Interpret rational interval bounds in the checked normalized credal model. -/
noncomputable def toCredal (I : ImpreciseProb) : PreciseVsImpreciseGrounded.KSCredalSet where
  pSafe_lo := I.pSafe_lo
  pSafe_hi := I.pSafe_hi
  pRisky_lo := I.pRisky_lo
  pRisky_hi := I.pRisky_hi
  pCat_lo := I.pCat_lo
  pCat_hi := I.pCat_hi
  safe_valid := by exact_mod_cast I.safe_valid
  risky_valid := by exact_mod_cast I.risky_valid
  cat_valid := by exact_mod_cast I.cat_valid
  all_nonneg := by exact_mod_cast I.all_nonneg
  nonempty := I.nonempty

/-- The true infimum over feasible normalized distributions, not an unchecked corner. -/
noncomputable def worstCase_normal (I : ImpreciseProb) : ℝ :=
  PreciseVsImpreciseGrounded.worstCaseEU I.toCredal .normal
noncomputable def worstCase_cautious (I : ImpreciseProb) : ℝ :=
  PreciseVsImpreciseGrounded.worstCaseEU I.toCredal .cautious

/-- Maximin prefers Cautious if worst(Cautious) > worst(Normal) -/
def maximinPrefersCautious (I : ImpreciseProb) : Prop :=
  I.worstCase_cautious > I.worstCase_normal

end ImpreciseProb

/-! ## §6: The Key Example -/

/-- Uncertainty range: P(Cat) ∈ [0.5%, 5%] = [1/200, 1/20] -/
def uncertaintyRange : ImpreciseProb where
  pSafe_lo := 17/20     -- 0.85 (when pCat is high)
  pSafe_hi := 179/200   -- 0.895 (when pCat is low)
  pRisky_lo := 1/10
  pRisky_hi := 1/10
  pCat_lo := 1/200      -- 0.5%
  pCat_hi := 1/20       -- 5%
  safe_valid := by norm_num
  risky_valid := by norm_num
  cat_valid := by norm_num
  all_nonneg := by norm_num
  nonempty := ⟨17/20, 1/10, 1/20, by norm_num⟩

theorem uncertaintyRange_toCredal :
    uncertaintyRange.toCredal = PreciseVsImpreciseGrounded.uncertaintyCredal := by
  norm_num [ImpreciseProb.toCredal, uncertaintyRange, PreciseVsImpreciseGrounded.uncertaintyCredal]

theorem normal_worst_simplified : uncertaintyRange.worstCase_normal = 40 := by
  simpa only [ImpreciseProb.worstCase_normal, uncertaintyRange_toCredal] using
    PreciseVsImpreciseGrounded.normal_worst

theorem cautious_worst_simplified : uncertaintyRange.worstCase_cautious = 78 := by
  simpa only [ImpreciseProb.worstCase_cautious, uncertaintyRange_toCredal] using
    PreciseVsImpreciseGrounded.cautious_worst

theorem normal_worst_case_val :
    uncertaintyRange.worstCase_normal = 17/20 * 100 + 1/10 * 50 + 1/20 * (-1000) := by
  rw [normal_worst_simplified]; norm_num

theorem cautious_worst_case_val :
    uncertaintyRange.worstCase_cautious = 17/20 * 80 + 1/10 * 70 + 1/20 * 60 := by
  rw [cautious_worst_simplified]; norm_num

/-- **Main Result**: Maximin prefers Cautious (78 > 40) -/
theorem maximin_prefers_cautious : uncertaintyRange.maximinPrefersCautious := by
  unfold ImpreciseProb.maximinPrefersCautious
  rw [normal_worst_simplified, cautious_worst_simplified]
  norm_num

/-! ## §7: The Central Theorem -/

/-- **Decisions Differ**: EU and Maximin give different answers depending on
    where in the uncertainty range the true probability lies.

    - At P(Cat) = 0.5%: EU prefers Normal
    - At P(Cat) = 5%: EU prefers Cautious
    - Maximin: Always prefers Cautious (robust to uncertainty)
-/
theorem decisions_differ :
    lowRiskDist.normalIsBetter ∧
    highRiskDist.cautiousIsBetter ∧
    uncertaintyRange.maximinPrefersCautious :=
  ⟨lowRisk_normal_wins, highRisk_cautious_wins, maximin_prefers_cautious⟩

/-! ## §8: The Breakeven Point -/

/-- The breakeven probability where EU(Normal) = EU(Cautious).

From EU_diff_formula: 20*pSafe - 20*pRisky - 1060*pCat = 0
With pRisky = 0.1 and pSafe = 0.9 - pCat:
  20*(0.9 - pCat) - 20*0.1 - 1060*pCat = 0
  18 - 2 - 20*pCat - 1060*pCat = 0
  16 = 1080*pCat
  pCat = 16/1080 = 2/135 ≈ 0.0148 ≈ 1.48%
-/
def breakeven_pCat : ℚ := 2/135

/-- Verify: At breakeven, EU difference is zero -/
def breakevenDist : PreciseProb where
  pSafe := 1 - 1/10 - 2/135  -- = 121/135 - 1/10 = (1210 - 135)/1350 = 1075/1350
  pRisky := 1/10
  pCatastrophic := 2/135
  nonneg_safe := by norm_num
  nonneg_risky := by norm_num
  nonneg_cat := by norm_num
  sum_one := by norm_num

theorem breakeven_EU_equal :
    breakevenDist.expectedUtility normal = breakevenDist.expectedUtility cautious := by
  unfold PreciseProb.expectedUtility payoff breakevenDist
  norm_num

/-! ## Summary

This file proves (by direct calculation):

* for a low catastrophic probability (`lowRiskDist`), expected utility prefers `normal`,
* for a higher catastrophic probability (`highRiskDist`), expected utility prefers `cautious`,
* for an interval of catastrophic probabilities (`uncertaintyRange`), the maximin rule prefers
  `cautious` (since it has a higher worst-case payoff),
* and the breakeven threshold for expected utility is `pCat = 2/135`.
-/

end KnuthSkilling.Examples.PreciseVsImprecise
