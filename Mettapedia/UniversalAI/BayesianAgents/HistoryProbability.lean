import Mettapedia.UniversalAI.BayesianAgents

/-!
# History Probability (Environment-Only)

This file factors out the basic “environment generates a (finite) history” probability
construction used in the Grain-of-Truth measure-theory development and elsewhere.

It lives in the `Mettapedia.UniversalAI.BayesianAgents` namespace so it can be reused by:
- bandit-style Bayesian mixtures,
- general (RL / POMDP) Bayesian environment classes,
- the Grain-of-Truth posterior / likelihood-ratio pipeline.
-/

namespace Mettapedia.UniversalAI.BayesianAgents

open scoped ENNReal NNReal

/-! ## History Probability

The probability that an environment `μ` generates a history `h`, treating the *actions in `h` as
given* (i.e. conditioning on the action sequence).

For a history `h = (a₁, x₁, a₂, x₂, ..., aₜ, xₜ)`:

`μ(h) = ∏ᵢ μ(xᵢ | a₁x₁...aᵢ)`
-/

/-- Auxiliary function for `historyProbability` with an accumulator prefix `pfx`. -/
noncomputable def historyProbabilityAux (μ : Environment) : History → History → ℝ≥0∞
  | _, [] => 1
  | _, [HistElem.act _] => 1
  | pfx, HistElem.act a :: HistElem.per x :: rest =>
      let conditioningHist := pfx ++ [HistElem.act a]
      let newPrefix := pfx ++ [HistElem.act a, HistElem.per x]
      μ.prob conditioningHist x * historyProbabilityAux μ newPrefix rest
  | _, HistElem.act _ :: HistElem.act _ :: _ => 0
  | pfx, HistElem.per _ :: rest => historyProbabilityAux μ pfx rest

/-- Environment-only probability of a history: product of the conditional percept probabilities. -/
noncomputable def historyProbability (μ : Environment) (h : History) : ℝ≥0∞ :=
  historyProbabilityAux μ [] h

/-! ## Well-Formedness Helpers -/

/-- Appending `[act a]` to a wellFormed history of even length preserves wellFormedness. -/
theorem wellFormed_append_act (h : History) (hw : h.wellFormed) (he : Even h.length) (a : Action) :
    (h ++ [HistElem.act a]).wellFormed := by
  induction h using List.twoStepInduction with
  | nil => rfl
  | singleton e =>
      simp only [List.length_singleton] at he
      exact (Nat.not_even_one he).elim
  | cons_cons e1 e2 rest ih =>
      match e1, e2 with
      | HistElem.act _, HistElem.per _ =>
          simp only [List.cons_append, History.wellFormed] at hw ⊢
          have he' : Even rest.length := by
            simp only [List.length_cons] at he
            obtain ⟨k, hk⟩ := he
            refine ⟨k - 1, ?_⟩
            omega
          exact ih hw he'
      | HistElem.act _, HistElem.act _ =>
          simp only [History.wellFormed] at hw
          cases hw
      | HistElem.per _, _ =>
          simp only [History.wellFormed] at hw
          cases hw

/-- Appending `[act a, per x]` to a wellFormed history of even length preserves wellFormedness. -/
theorem wellFormed_append_act_per (h : History) (hw : h.wellFormed) (he : Even h.length)
    (a : Action) (x : Percept) :
    (h ++ [HistElem.act a, HistElem.per x]).wellFormed := by
  induction h using List.twoStepInduction with
  | nil => rfl
  | singleton e =>
      simp only [List.length_singleton] at he
      exact (Nat.not_even_one he).elim
  | cons_cons e1 e2 rest ih =>
      match e1, e2 with
      | HistElem.act _, HistElem.per _ =>
          simp only [List.cons_append, History.wellFormed] at hw ⊢
          have he' : Even rest.length := by
            simp only [List.length_cons] at he
            obtain ⟨k, hk⟩ := he
            refine ⟨k - 1, ?_⟩
            omega
          exact ih hw he'
      | HistElem.act _, HistElem.act _ =>
          simp only [History.wellFormed] at hw
          cases hw
      | HistElem.per _, _ =>
          simp only [History.wellFormed] at hw
          cases hw

/-! ## Basic Bounds and Chain Rule -/

/-- Auxiliary bound: `historyProbabilityAux` is at most `1` given a well-formed even prefix. -/
theorem historyProbabilityAux_le_one (μ : Environment) (pfx h : History)
    (h_pfx_wf : pfx.wellFormed) (h_pfx_complete : Even pfx.length) :
    historyProbabilityAux μ pfx h ≤ 1 := by
  induction h generalizing pfx with
  | nil => simp [historyProbabilityAux]
  | cons elem rest ih =>
      cases elem with
      | act a =>
          cases rest with
          | nil => simp [historyProbabilityAux]
          | cons elem' rest' =>
              cases elem' with
              | act _ => simp [historyProbabilityAux]
              | per x =>
                  simp only [historyProbabilityAux]
                  have h1 : μ.prob (pfx ++ [HistElem.act a]) x ≤ 1 := by
                    have h_wf : (pfx ++ [HistElem.act a]).wellFormed :=
                      wellFormed_append_act pfx h_pfx_wf h_pfx_complete a
                    calc
                      μ.prob (pfx ++ [HistElem.act a]) x
                          ≤ ∑' y, μ.prob (pfx ++ [HistElem.act a]) y := ENNReal.le_tsum _
                      _ ≤ 1 := μ.prob_le_one _ h_wf
                  have h2 :
                      historyProbabilityAux μ (pfx ++ [HistElem.act a, HistElem.per x]) rest' ≤ 1 :=
                    ih (pfx ++ [HistElem.act a, HistElem.per x])
                      (wellFormed_append_act_per pfx h_pfx_wf h_pfx_complete a x)
                      (by
                        rcases h_pfx_complete with ⟨k, hk⟩
                        refine ⟨k + 1, ?_⟩
                        simp [List.length_append, hk]
                        omega)
                  exact mul_le_one' h1 h2
      | per _ => exact ih pfx h_pfx_wf h_pfx_complete

/-- History probability is at most `1`. -/
theorem historyProbability_le_one (μ : Environment) (h : History) :
    historyProbability μ h ≤ 1 := by
  simp only [historyProbability]
  exact historyProbabilityAux_le_one μ [] h rfl (by simp)

/-- Helper lemma: `historyProbabilityAux` factorizes when appending a full step. -/
theorem historyProbabilityAux_append_act_per (μ : Environment) (pfx h : History)
    (hw : h.wellFormed) (hc : Even h.length) (a : Action) (x : Percept) :
    historyProbabilityAux μ pfx (h ++ [HistElem.act a, HistElem.per x]) =
      historyProbabilityAux μ pfx h * μ.prob (pfx ++ h ++ [HistElem.act a]) x := by
  match h with
  | [] =>
      simp only [List.nil_append, historyProbabilityAux, one_mul, List.append_nil, mul_one]
  | [HistElem.act _] =>
      simp only [List.length_singleton] at hc
      exact absurd hc (by decide : ¬Even 1)
  | [HistElem.per _] =>
      simp [History.wellFormed] at hw
  | HistElem.act a' :: HistElem.per x' :: rest' =>
      simp only [List.cons_append, historyProbabilityAux]
      simp only [History.wellFormed] at hw
      simp only [List.length_cons] at hc
      have hc' : Even rest'.length := by
        obtain ⟨k, hk⟩ := hc
        refine ⟨k - 1, ?_⟩
        omega
      have ih :=
        historyProbabilityAux_append_act_per μ (pfx ++ [HistElem.act a', HistElem.per x'])
          rest' hw hc' a x
      rw [ih]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      ring
  | HistElem.act _ :: HistElem.act _ :: _ =>
      simp [History.wellFormed] at hw
  | HistElem.per _ :: _ :: _ =>
      simp [History.wellFormed] at hw
termination_by h.length

/-- Chain rule for history probability: appending one full (action, percept) step multiplies by the
one-step conditional probability. -/
theorem historyProbability_append_step (μ : Environment) (h : History)
    (hw : h.wellFormed) (hc : Even h.length) (a : Action) (x : Percept) :
    historyProbability μ (h ++ [HistElem.act a, HistElem.per x]) =
      historyProbability μ h * μ.prob (h ++ [HistElem.act a]) x := by
  unfold historyProbability
  rw [historyProbabilityAux_append_act_per μ [] h hw hc a x]
  simp only [List.nil_append]

end Mettapedia.UniversalAI.BayesianAgents
