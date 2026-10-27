import KnuthSkilling.Additive.Proofs.GridInduction.Core.Induction.Construction


namespace KnuthSkilling.Additive

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α]

/-!
# Trade identities and rational comparison statistics

An algebraic trade `μ r = μ s ⊕ d^Δ` shifts the absolute A/C comparisons by Δ.
Strict monotonicity of translation supplies cancellation; commuting powers supply
amplification. Neither operation requires an already constructed global representation.

The coefficient specification then identifies the observed difference with Δ·δ.
Internal trades use an old-grid B-witness directly. General trades use amplified
comparisons and the Archimedean bound, retaining the independent definition of μ.
-/

/-- δ is a tight Dedekind cut: for any ε > 0, there exist A and C witnesses
    whose statistics approximate δ within ε. -/
lemma delta_cut_tight {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∀ ε > 0, ∃ (rA : Multi k) (uA : ℕ) (rC : Multi k) (uC : ℕ)
      (huA : 0 < uA) (huC : 0 < uC),
      rA ∈ extensionSetA F d uA ∧ rC ∈ extensionSetC F d uC ∧
      |separationStatistic R rC uC huC - chooseδ hk R d hd| < ε ∧
      |chooseδ hk R d hd - separationStatistic R rA uA huA| < ε := by
  intro ε hε
  -- accuracy_lemma gives rA,uA,rC,uC with (C-stat) - (A-stat) < ε
  have hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
    extensionSetA_nonempty_of_B_empty F d hd hB_empty
  have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
    extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
  obtain ⟨rA, uA, huA, hrA, rC, uC, huC, hrC, h_gap⟩ :=
    accuracy_lemma R d hd hB_empty hA_nonempty hC_nonempty ε hε

  set δ := chooseδ hk R d hd
  have hA_le_δ : separationStatistic R rA uA huA ≤ δ :=
    chooseδ_A_bound hk R IH H d hd rA uA huA hrA
  have hδ_le_C : δ ≤ separationStatistic R rC uC huC :=
    chooseδ_C_bound hk R IH H d hd rC uC huC hrC

  use rA, uA, rC, uC, huA, huC
  refine ⟨hrA, hrC, ?C_close, ?A_close⟩

  · -- |C - δ| < ε
    -- We know δ ≤ C and C - A < ε ⇒ C - δ ≤ C - A < ε
    have h_diff : separationStatistic R rC uC huC - δ ≤
                  separationStatistic R rC uC huC - separationStatistic R rA uA huA := by
      linarith [hA_le_δ]
    have hpos : 0 ≤ separationStatistic R rC uC huC - δ := by linarith [hδ_le_C]
    have := lt_of_le_of_lt h_diff h_gap
    simp [abs_of_nonneg hpos]
    exact this

  · -- |δ - A| < ε
    have h_diff : δ - separationStatistic R rA uA huA ≤
                  separationStatistic R rC uC huC - separationStatistic R rA uA huA := by
      linarith [hδ_le_C]
    have hpos : 0 ≤ δ - separationStatistic R rA uA huA := by linarith [hA_le_δ]
    have := lt_of_le_of_lt h_diff h_gap
    simp [abs_of_nonneg hpos]
    exact this

/-- Positive common scaling leaves an absolute separation statistic unchanged. -/
lemma separationStatistic_scaleMult {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (r : Multi k) (u m : ℕ) (hu : 0 < u) (hm : 0 < m) :
    separationStatistic R (scaleMult m r) (u * m) (Nat.mul_pos hu hm) =
      separationStatistic R r u hu := by
  simp only [separationStatistic, Theta_scaleMult, Nat.cast_mul]
  rw [mul_comm (u : ℝ) (m : ℝ)]
  exact mul_div_mul_left _ _ (ne_of_gt (Nat.cast_pos.mpr hm : (0 : ℝ) < m))

/-- `delta_cut_tight`, but with A and C witnesses at a common denominator.

Given `ε>0`, produce `u>0` and witnesses `rA ∈ A(u)`, `rC ∈ C(u)` such that both statistics are
within `ε` of `δ := chooseδ hk R d hd`.

This is a convenience lemma for the K&S Appendix A.3.4 “B-empty” arguments where we repeatedly
need denominator-matched approximants on both sides of the cut. -/
lemma delta_cut_tight_common_den {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∀ ε > 0, ∃ (u : ℕ) (hu : 0 < u) (rA rC : Multi k),
      rA ∈ extensionSetA F d u ∧ rC ∈ extensionSetC F d u ∧
      |separationStatistic R rC u hu - chooseδ hk R d hd| < ε ∧
      |chooseδ hk R d hd - separationStatistic R rA u hu| < ε := by
  intro ε hε
  obtain ⟨rA, uA, rC, uC, huA, huC, hrA, hrC, hC, hA⟩ :=
    delta_cut_tight hk R IH H d hd hB_empty ε hε
  have hA' : scaleMult uC rA ∈ extensionSetA F d (uA * uC) := by
    change mu F (scaleMult uC rA) < iterate_op d (uA * uC)
    rw [IH.bridge, ← iterate_op_mul]
    exact iterate_op_strictMono_base uC huC _ _ hrA
  have hC' : scaleMult uA rC ∈ extensionSetC F d (uA * uC) := by
    change iterate_op d (uA * uC) < mu F (scaleMult uA rC)
    rw [IH.bridge, Nat.mul_comm uA uC, ← iterate_op_mul]
    exact iterate_op_strictMono_base uA huA _ _ hrC
  refine ⟨uA * uC, Nat.mul_pos huA huC, scaleMult uC rA, scaleMult uA rC, hA', hC', ?_, ?_⟩
  · have hs : separationStatistic R (scaleMult uA rC) (uA * uC) (Nat.mul_pos huA huC) =
        separationStatistic R rC uC huC := by
      simpa only [Nat.mul_comm uA uC] using separationStatistic_scaleMult R rC uC uA huC huA
    rw [hs]
    exact hC
  · rw [separationStatistic_scaleMult R rA uA uC huA huC]
    exact hA

omit [KSSeparation α] in
/-- Shift property for A: if trade holds and `s_old ∈ A(u)`, then `r_old ∈ A(u+Δ)`.

By trade, `mu F r_old = op (mu F s_old) (d^Δ)`.
Since `d^{u+Δ} = d^u ⊕ d^Δ` and `op` is strictly monotone:
`op (mu F s_old) (d^Δ) < op (d^u) (d^Δ) = d^{u+Δ}`.
So `r_old ∈ A(u+Δ)`. -/
lemma trade_shift_A {k : ℕ} {F : AtomFamily α k}
    {d : α} (_hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (_hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {u : ℕ} (hrA : s_old ∈ extensionSetA F d u) :
    r_old ∈ extensionSetA F d (u + Δ) := by
  change mu F r_old < iterate_op d (u + Δ)
  rw [htrade, ← iterate_op_add]
  exact op_strictMono_left (iterate_op d Δ) hrA

omit [KSSeparation α] in
/-- Backward shift property for A: if trade holds and `r_old ∈ A(u+Δ)`, then `s_old ∈ A(u)`. -/
lemma trade_shift_A_backward {k : ℕ} {F : AtomFamily α k}
    {d : α} (_hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (_hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {u : ℕ} (hrA : r_old ∈ extensionSetA F d (u + Δ)) :
    s_old ∈ extensionSetA F d u := by
  apply (op_strictMono_left (iterate_op d Δ)).monotone.reflect_lt
  simpa only [extensionSetA, Set.mem_ofPred_eq, htrade, ← iterate_op_add] using hrA

/-! ### Helper Lemmas for Cast Management and Proof Simplification -/

/-- If δ>0 and m*δ < u*δ, then m < u (as integers). -/
lemma int_lt_of_mul_lt_mul_right {δ : ℝ} (hδ : 0 < δ)
    {m u : ℤ} (h : (m:ℝ) * δ < (u:ℝ) * δ) : m < u := by
  -- cancel δ
  have : (m:ℝ) < (u:ℝ) := (mul_lt_mul_iff_left₀ hδ).1 h
  -- cast back to ℤ
  exact Int.cast_lt.mp this

/-- If δ>0 and u*δ < m*δ, then u < m (as integers). -/
lemma int_lt_of_mul_lt_mul_right' {δ : ℝ} (hδ : 0 < δ)
    {m u : ℤ} (h : (u:ℝ) * δ < (m:ℝ) * δ) : u < m := by
  have : (u:ℝ) < (m:ℝ) := (mul_lt_mul_iff_left₀ hδ).1 h
  exact Int.cast_lt.mp this

/-- If δ>0 and m*δ ≤ u*δ, then m ≤ u (as integers). -/
lemma int_le_of_mul_le_mul_right {δ : ℝ} (hδ : 0 < δ)
    {m u : ℤ} (h : (m:ℝ) * δ ≤ (u:ℝ) * δ) : m ≤ u := by
  have : (m:ℝ) ≤ (u:ℝ) := (mul_le_mul_iff_left₀ hδ).1 h
  exact Int.cast_le.mp this

omit [KSSeparation α] in
/-- **Shift property for C**: If trade holds and r_old ∈ C(v) with v > Δ, then s_old ∈ C(v-Δ).

Proof sketch: r_old ∈ C(v) means d^v < mu F r_old.
By trade, mu F r_old = op (mu F s_old) (d^Δ).
Since d^v = d^{v-Δ} ⊕ d^Δ and op is strictly monotone:
  If mu F s_old ≤ d^{v-Δ}, then op (mu F s_old) (d^Δ) ≤ d^v, contradicting hrC.
So d^{v-Δ} < mu F s_old, i.e., s_old ∈ C(v-Δ). -/
lemma trade_shift_C {k : ℕ} {F : AtomFamily α k}
    {d : α} (_hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (_hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {v : ℕ} (hv : Δ < v) (hrC : r_old ∈ extensionSetC F d v) :
    s_old ∈ extensionSetC F d (v - Δ) := by
  apply (op_strictMono_left (iterate_op d Δ)).monotone.reflect_lt
  simpa only [extensionSetC, Set.mem_ofPred_eq, htrade, iterate_op_add,
    Nat.sub_add_cancel hv.le] using hrC

omit [KSSeparation α] in
/-- **Forward shift property for C**: If trade holds and s_old ∈ C(v), then r_old ∈ C(v+Δ).

Proof sketch: s_old ∈ C(v) means d^v < mu F s_old.
By trade, mu F r_old = op (mu F s_old) (d^Δ).
Since op is strictly monotone:
  op (d^v) (d^Δ) < op (mu F s_old) (d^Δ) = mu F r_old
And op (d^v) (d^Δ) = d^{v+Δ} by iterate_op_add.
So d^{v+Δ} < mu F r_old, i.e., r_old ∈ C(v+Δ). -/
lemma trade_shift_C_forward {k : ℕ} {F : AtomFamily α k}
    {d : α} (_hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (_hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {v : ℕ} (hsC : s_old ∈ extensionSetC F d v) :
    r_old ∈ extensionSetC F d (v + Δ) := by
  change iterate_op d (v + Δ) < mu F r_old
  rw [htrade, ← iterate_op_add]
  exact op_strictMono_left (iterate_op d Δ) hsC

omit [KSSeparation α] in
/-- The trade relation shifts A-membership by `Δ` (for levels `U ≥ Δ`). -/
lemma trade_shift_A_iff {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {U : ℕ} (hU : Δ ≤ U) :
    r_old ∈ extensionSetA F d U ↔ s_old ∈ extensionSetA F d (U - Δ) := by
  constructor
  · intro hrA
    have : r_old ∈ extensionSetA F d ((U - Δ) + Δ) := by
      simpa [Nat.sub_add_cancel hU] using hrA
    exact trade_shift_A_backward (k := k) (F := F) hd hΔ htrade this
  · intro hsA
    have : r_old ∈ extensionSetA F d ((U - Δ) + Δ) :=
      trade_shift_A (k := k) (F := F) hd hΔ htrade (u := U - Δ) hsA
    simpa [Nat.sub_add_cancel hU] using this

omit [KSSeparation α] in
/-- The trade relation shifts C-membership by `Δ` (for levels `U > Δ`). -/
lemma trade_shift_C_iff {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {U : ℕ} (hU : Δ < U) :
    r_old ∈ extensionSetC F d U ↔ s_old ∈ extensionSetC F d (U - Δ) := by
  constructor
  · intro hrC
    exact trade_shift_C (k := k) (F := F) hd hΔ htrade hU hrC
  · intro hsC
    have : r_old ∈ extensionSetC F d ((U - Δ) + Δ) :=
      trade_shift_C_forward (k := k) (F := F) hd hΔ htrade (v := U - Δ) hsC
    have hU' : (U - Δ) + Δ = U := Nat.sub_add_cancel (le_of_lt hU)
    simpa [hU'] using this

omit [KSSeparation α] in
/-- If `x` commutes with `y`, then all iterates of `x` commute with `y`. -/
lemma iterate_op_comm_right {x y : α} (hxy : op x y = op y x) :
    ∀ n : ℕ, op (iterate_op x n) y = op y (iterate_op x n) := by
  let _ : Monoid α := KnuthSkillingMonoidBase.toMonoid
  have h : Commute x y := hxy
  intro n
  change iterate_op x n * y = y * iterate_op x n
  simpa only [iterate_op_eq_pow] using (h.pow_left n).eq

omit [KSSeparation α] in
/-- If `x` commutes with `y`, then iterating `x ⊕ y` distributes over iterating each term. -/
lemma iterate_op_op_of_comm {x y : α} (hxy : op x y = op y x) :
    ∀ n : ℕ, iterate_op (op x y) n = op (iterate_op x n) (iterate_op y n) := by
  let _ : Monoid α := KnuthSkillingMonoidBase.toMonoid
  have h : Commute x y := hxy
  intro n
  change iterate_op (x * y) n = iterate_op x n * iterate_op y n
  simpa only [iterate_op_eq_pow] using h.mul_pow n

/-- Internal δ-shift when `d^Δ` already lies on the old `k`-grid (i.e. we have a B-witness). -/
private lemma delta_shift_equiv_of_B_witness {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (_IH : GridBridge F) {d : α} (_hd : ident < d)
    {δ : ℝ} (_hδ_pos : 0 < δ)
    (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
    {r_old s_old rΔ : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    (hrΔB : rΔ ∈ extensionSetB F d Δ) :
    R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
      R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ = (Δ : ℝ) * δ := by
  have hμ : mu F r_old = mu F (s_old + rΔ) := by
    rw [mu_add_of_comm H, (show mu F rΔ = iterate_op d Δ from hrΔB)]
    exact htrade
  have hθ : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
      R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ +
        R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ :=
    (congrArg R.Θ_grid (Subtype.ext hμ)).trans (R.add s_old rΔ)
  have hs := hδB rΔ Δ hΔ hrΔB
  have hv : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = δ * (Δ : ℝ) :=
    (div_eq_iff (ne_of_gt (Nat.cast_pos.mpr hΔ : (0 : ℝ) < Δ))).mp hs
  nlinarith

/-- **The δ-Shift Equivalence Lemma** (K&S trade argument core)

Given a trade equality mu F r_old = op (mu F s_old) (d^Δ) and δ bounds,
the Θ-difference must equal Δ·δ.

**Proof strategy** (GPT-5.1 Pro / K&S Appendix A):
1. The shift rules give: r_old ∈ A(U) ↔ s_old ∈ A(U-Δ) for U > Δ
2. Similarly for C-membership
3. For upper bound: Use A-bound on r at U, C-bound on s at V, get Θ(r)-Θ(s) ≤ (U-V)·δ
4. For lower bound: Use C-bound on r at V+Δ, A-bound on s at U-Δ
5. As U → ∞ with the accuracy lemma squeezing A-C gap, we get equality

This is THE key lemma for Theta'_well_defined. -/
lemma delta_shift_equiv {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδA : ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu ≤ δ)
    (hδC : ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ ≤ separationStatistic R r u hu)
    (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ)) :
    R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
    R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ = (Δ : ℝ) * δ := by
  classical
  -- If d^Δ already lies on the old k-grid, the trade is internal and the result follows
  -- from additivity of Θ on the k-grid.
  by_cases hBΔ : ∃ rΔ : Multi k, rΔ ∈ extensionSetB F d Δ
  · rcases hBΔ with ⟨rΔ, hrΔB⟩
    exact delta_shift_equiv_of_B_witness R H IH hd hδ_pos hδB hΔ htrade hrΔB
  · -- External case: d^Δ is not already a μ-value on the old k-grid.
    -- If B is non-empty somewhere, scale the trade to an internal one; otherwise, this is the
    -- genuinely irrational case and needs the full K&S accuracy proof.
    set y := mu F s_old
    set z := iterate_op d Δ

    have hz_comm_y : op z y = op y z := by
      -- Use commutativity on the grid and cancel the common left factor.
      have hcomm := H.comm r_old s_old
      have h1 : op (op y z) y = op y (op y z) := by
        simpa [y, z, htrade] using hcomm
      have h2 : op y (op z y) = op y (op y z) := by
        simpa [op_assoc] using h1
      exact (op_strictMono_right y).injective h2

    by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u
    · rcases hB_global with ⟨rB, uB, huB, hrB⟩
      set n := uB
      have hn_pos : 0 < n := huB

      -- Iterate the trade n times, using commutativity between y and z.
      have htrade_iter :
          iterate_op (mu F r_old) n = op (iterate_op y n) (iterate_op z n) := by
        have h0 := congrArg (fun x : α => iterate_op x n) htrade
        -- rewrite the RHS using commutativity between y and z
        have hdist : iterate_op (op y z) n = op (iterate_op y n) (iterate_op z n) :=
          iterate_op_op_of_comm (x := y) (y := z) hz_comm_y.symm n
        simpa [y, z, hdist] using h0

      -- Move from iterates back to μ on scaled multiplicities, then reduce to the internal case.
      have hr_bridge : mu F (scaleMult n r_old) = iterate_op (mu F r_old) n := IH.bridge r_old n
      have hs_bridge : mu F (scaleMult n s_old) = iterate_op y n := by
        simpa [y] using (IH.bridge s_old n)

      have hz_iter : iterate_op z n = iterate_op d (Δ * n) := by
        simpa [z] using (iterate_op_mul d Δ n)

      have htrade_scaled :
          mu F (scaleMult n r_old) =
            op (mu F (scaleMult n s_old)) (iterate_op d (Δ * n)) := by
        -- rewrite `htrade_iter` using the bridge equations
        rw [hr_bridge, hs_bridge]
        simpa [hz_iter] using htrade_iter

      -- Build a B-witness for d^(Δ*n) by scaling the global B witness.
      have hrB_eq : mu F rB = iterate_op d n := by
        simpa [extensionSetB, Set.mem_ofPred_eq, n] using hrB
      have hrΔ_eq : mu F (scaleMult Δ rB) = iterate_op d (Δ * n) := by
        have h := IH.bridge rB Δ
        -- μ(Δ·rB) = (μ rB)^Δ = (d^n)^Δ = d^(n*Δ) = d^(Δ*n)
        rw [hrB_eq] at h
        -- turn (d^n)^Δ into d^(n*Δ), then swap multiplication order
        have : iterate_op (iterate_op d n) Δ = iterate_op d (Δ * n) := by
          simpa [Nat.mul_comm] using (iterate_op_mul d n Δ)
        simpa [this] using h
      have hΔn_pos : 0 < Δ * n := Nat.mul_pos hΔ hn_pos
      have hrΔB : (scaleMult Δ rB) ∈ extensionSetB F d (Δ * n) := by
        simp [extensionSetB, Set.mem_ofPred_eq, hrΔ_eq]

      have h_scaled_gap :
          R.Θ_grid ⟨mu F (scaleMult n r_old), mu_mem_kGrid F (scaleMult n r_old)⟩ -
            R.Θ_grid ⟨mu F (scaleMult n s_old), mu_mem_kGrid F (scaleMult n s_old)⟩ =
              ((Δ * n : ℕ) : ℝ) * δ :=
        delta_shift_equiv_of_B_witness R H IH hd hδ_pos hδB hΔn_pos htrade_scaled hrΔB

      -- Cancel the common scalar factor `n`.
      have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
      have hθr_scale := Theta_scaleMult R r_old n
      have hθs_scale := Theta_scaleMult R s_old n

      -- Rewrite the scaled gap in terms of θr and θs.
      have : (n : ℝ) *
            (R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
              R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩)
            = (n : ℝ) * ((Δ : ℝ) * δ) := by
        -- Expand the left using Theta_scaleMult, then simplify.
        -- First: rewrite the LHS of h_scaled_gap.
        have h_scaled_gap' :
            (n : ℝ) * R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
              (n : ℝ) * R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ =
                ((Δ * n : ℕ) : ℝ) * δ := by
          simpa [hθr_scale, hθs_scale] using h_scaled_gap
        -- Now factor out n on the left, and rewrite (Δ*n) on the right.
        -- `simp` turns `((Δ*n):ℕ : ℝ)` into `(Δ:ℝ) * (n:ℝ)`.
        simpa [mul_sub, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h_scaled_gap'
      exact mul_left_cancel₀ hn_ne this

    · -- TODO(K&S Appendix A): complete the accuracy-based proof for the globally B-empty case.
        -- This is the genuinely irrational trade configuration.
        have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u := by
          intro r u hu hrB
          exact hB_global ⟨r, u, hu, hrB⟩
  
        -- k = 0 is impossible under the trade hypothesis (μ is constantly ident).
        cases k with
        | zero =>
          have hmu_r : mu F r_old = ident := by simp [mu]
          have hmu_s : mu F s_old = ident := by simp [mu]
          have hEq : ident = iterate_op d Δ := by
            simpa [y, z, hmu_r, hmu_s, op_ident_left] using htrade
          have hpos : ident < iterate_op d Δ := iterate_op_pos d hd _ hΔ
          have : False := by
            have : iterate_op d Δ < iterate_op d Δ := by simp [hEq] at hpos
            exact (lt_irrefl _ this)
          exact False.elim this
        | succ k =>
          -- In the external B-empty case, μ(F, s_old) must be strictly above ident.
          have hy_ne : y ≠ ident := by
            intro hy_eq
            have hmu_s : mu F s_old = ident := by simpa [y] using hy_eq
            have hmu_r : mu F r_old = iterate_op d Δ := by
              simpa [y, z, hmu_s, op_ident_left] using htrade
            have hrB : r_old ∈ extensionSetB F d Δ := by
              simp [extensionSetB, Set.mem_ofPred_eq, hmu_r]
            exact hBΔ ⟨r_old, hrB⟩
          have hy_pos : ident < y :=
            lt_of_le_of_ne (ident_le y) (Ne.symm hy_ne)
  
          -- Abbreviate the Θ-values on the k-grid.
          set θr := R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩
          set θs := R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩
  
          -- Show the Θ-gap is arbitrarily close to Δ·δ by scaling and bracketing within a 1-step window.
          have h_close : ∀ ε > 0, |(θr - θs) - (Δ : ℝ) * δ| < ε := by
            intro ε hε
  
            -- Choose n large enough that d < y^n and δ/ε < n.
            obtain ⟨n_d, hn_d⟩ := bounded_by_iterate y hy_pos d
            obtain ⟨N, hN⟩ := exists_nat_gt (δ / ε)
            let n1 : ℕ := Nat.succ N
            let n : ℕ := max n_d n1
            have hn_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) (le_max_right _ _)
  
            have hn_ge_n1 : n1 ≤ n := le_max_right _ _
            have hn1_gt : δ / ε < (n1 : ℝ) := by
              have hle : (N : ℝ) ≤ (n1 : ℝ) := by exact_mod_cast Nat.le_succ N
              exact lt_of_lt_of_le hN hle
            have hratio : δ / ε < (n : ℝ) := by
              have hn1_le : (n1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_n1
              exact lt_of_lt_of_le hn1_gt hn1_le
            have hε_ne : (ε : ℝ) ≠ 0 := ne_of_gt hε
            have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos
            have hδ_div : δ / (n : ℝ) < ε := by
              have h_mul : (δ / ε) * ε < (n : ℝ) * ε :=
                mul_lt_mul_of_pos_right hratio hε
              have hleft : (δ / ε) * ε = δ := by field_simp [hε_ne]
              have hδ_lt : δ < (n : ℝ) * ε := by simpa [hleft] using h_mul
              -- turn δ < n*ε into δ/n < ε
              exact (div_lt_iff₀ hn_real).2 (by simpa [mul_comm] using hδ_lt)
  
            have hd_lt_y_iter : d < iterate_op y n := by
              have hn_d_le : n_d ≤ n := le_max_left _ _
              have hmono : Monotone (iterate_op y) := (iterate_op_strictMono y hy_pos).monotone
              exact lt_of_lt_of_le hn_d (hmono hn_d_le)
  
            -- Scale the trade by n and rewrite it as a trade on μ-values.
            have htrade_iter :
                iterate_op (mu F r_old) n = op (iterate_op y n) (iterate_op z n) := by
              have h0 := congrArg (fun x : α => iterate_op x n) htrade
              have hdist :
                  iterate_op (op y z) n = op (iterate_op y n) (iterate_op z n) :=
                iterate_op_op_of_comm (x := y) (y := z) hz_comm_y.symm n
              simpa [y, z, hdist] using h0
            have hr_bridge : mu F (scaleMult n r_old) = iterate_op (mu F r_old) n :=
              IH.bridge r_old n
            have hs_bridge : mu F (scaleMult n s_old) = iterate_op y n := by
              simpa [y] using (IH.bridge s_old n)
            have hz_iter : iterate_op z n = iterate_op d (Δ * n) := by
              simpa [z] using (iterate_op_mul d Δ n)
            have htrade_scaled :
                mu F (scaleMult n r_old) =
                  op (mu F (scaleMult n s_old)) (iterate_op d (Δ * n)) := by
              rw [hr_bridge, hs_bridge]
              simpa [hz_iter] using htrade_iter
  
            -- Define the scaled grid points for r_old and s_old.
            set rN : Multi (k + 1) := scaleMult n r_old
            set sN : Multi (k + 1) := scaleMult n s_old
            have hmu_sN : mu F sN = iterate_op y n := by
              simpa [sN] using hs_bridge
            have hmu_rN : mu F rN = op (mu F sN) (iterate_op d (Δ * n)) := by
              simpa [rN, sN] using htrade_scaled
  
            -- Find the crossing index m such that d^m < μ(sN) < d^(m+1).
            obtain ⟨K, hK⟩ := bounded_by_iterate d hd (mu F sN)
            let P : ℕ → Prop := fun u => iterate_op d u ≤ mu F sN
            have hP0 : P 0 := by
              simp [P, iterate_op_zero]
              exact ident_le _
            have hcross := findGreatest_crossing (P := P) K hP0
            set m : ℕ := Nat.findGreatest P K
            have hmP : P m := by simpa [m] using hcross.1
            have hm_le_K : m ≤ K := by simpa [m] using hcross.2.1
            have hmax : ∀ k, m < k → k ≤ K → ¬ P k := by
              simpa [m] using hcross.2.2
            have hPK_false : ¬ P K := by
              -- From μ(sN) < d^K, we get ¬(d^K ≤ μ(sN)).
              have : mu F sN < iterate_op d K := by simpa [P] using hK
              exact not_le_of_gt this
            have hm_lt_K : m < K :=
              lt_of_le_of_ne hm_le_K (by
                intro hm_eq
                apply hPK_false
                simpa [hm_eq] using hmP)
            have hm1_le_K : m + 1 ≤ K := Nat.succ_le_of_lt hm_lt_K
            have h_notP_m1 : ¬ P (m + 1) :=
              hmax (m + 1) (Nat.lt_succ_self m) hm1_le_K
            have hmu_sN_lt : mu F sN < iterate_op d (m + 1) :=
              lt_of_not_ge h_notP_m1
  
            -- Ensure m > 0: since d < μ(sN), we must have d^1 ≤ μ(sN), hence 1 ≤ m.
            have hP1 : P 1 := by
              have : d ≤ mu F sN := by
                -- d < y^n = μ(sN)
                have : d < mu F sN := by simpa [hmu_sN] using hd_lt_y_iter
                exact le_of_lt this
              simpa [P, iterate_op_one] using this
            have hm_pos : 0 < m := by
              by_contra hm0
              have hm_eq0 : m = 0 := Nat.eq_zero_of_not_pos hm0
              -- contradict maximality if m = 0 and P 1 holds
              have h1_le_K : 1 ≤ K := by
                -- since d < μ(sN) < d^K, we must have 1 < K
                have hd_lt : iterate_op d 1 < mu F sN := by
                  simpa [iterate_op_one, hmu_sN] using hd_lt_y_iter
                have : 1 < K := by
                  -- If K ≤ 1 then μ(sN) < d^K ≤ d^1 contradicts d^1 < μ(sN).
                  by_contra hK1
                  have hK_le1 : K ≤ 1 := le_of_not_gt hK1
                  have hK_le' : iterate_op d K ≤ iterate_op d 1 :=
                    (iterate_op_strictMono d hd).monotone hK_le1
                  have hmu_lt : mu F sN < iterate_op d 1 := lt_of_lt_of_le hK hK_le'
                  have : iterate_op d 1 < iterate_op d 1 := lt_trans hd_lt hmu_lt
                  exact (lt_irrefl _ this)
                exact le_of_lt this
              have h_notP1 : ¬ P 1 := by
                have hm_lt_1 : m < 1 := by simp [hm_eq0]
                exact hmax 1 hm_lt_1 h1_le_K
              exact h_notP1 hP1
  
            -- Use global B-emptiness to rule out equality at level m and obtain strictness.
            have hm_ne : mu F sN ≠ iterate_op d m := by
              intro hEq
              have : sN ∈ extensionSetB F d m := by
                simp [extensionSetB, Set.mem_ofPred_eq, hEq]
              exact hB_empty sN m hm_pos this
            have hdm_lt : iterate_op d m < mu F sN :=
              lt_of_le_of_ne hmP (Ne.symm hm_ne)
  
            have hs_in_C : sN ∈ extensionSetC F d m := by
              simp [extensionSetC, Set.mem_ofPred_eq, hdm_lt]
            have hs_in_A : sN ∈ extensionSetA F d (m + 1) := by
              simp [extensionSetA, Set.mem_ofPred_eq, hmu_sN_lt]
  
            -- Shift the bounds through the scaled trade to bracket μ(rN).
            have hdmn_lt : iterate_op d (m + Δ * n) < mu F rN := by
              have h1 : op (iterate_op d m) (iterate_op d (Δ * n)) < op (mu F sN) (iterate_op d (Δ * n)) :=
                op_strictMono_left (iterate_op d (Δ * n)) hdm_lt
              have hpow : op (iterate_op d m) (iterate_op d (Δ * n)) = iterate_op d (m + Δ * n) := by
                simpa using (iterate_op_add d m (Δ * n))
              simpa [hmu_rN, hpow] using h1
            have hdmn1_gt : mu F rN < iterate_op d (m + 1 + Δ * n) := by
              have h1 : op (mu F sN) (iterate_op d (Δ * n)) < op (iterate_op d (m + 1)) (iterate_op d (Δ * n)) :=
                op_strictMono_left (iterate_op d (Δ * n)) hmu_sN_lt
              have hpow : op (iterate_op d (m + 1)) (iterate_op d (Δ * n)) = iterate_op d (m + 1 + Δ * n) := by
                simpa using (iterate_op_add d (m + 1) (Δ * n))
              simpa [hmu_rN, hpow] using h1
  
            have hr_in_C : rN ∈ extensionSetC F d (m + Δ * n) := by
              simp [extensionSetC, Set.mem_ofPred_eq, hdmn_lt]
            have hr_in_A : rN ∈ extensionSetA F d (m + 1 + Δ * n) := by
              simp [extensionSetA, Set.mem_ofPred_eq, hdmn1_gt]
  
            -- Convert A/C bounds into Θ bounds for the scaled points.
            have hm1_pos : 0 < m + 1 := Nat.succ_pos m
            have hmn_pos : 0 < m + Δ * n := lt_of_lt_of_le hm_pos (Nat.le_add_right _ _)
            have hmn1_pos : 0 < m + 1 + Δ * n := lt_of_lt_of_le hm1_pos (Nat.le_add_right _ _)
  
            have hsA_bound : separationStatistic R sN (m + 1) hm1_pos ≤ δ :=
              hδA sN (m + 1) hm1_pos hs_in_A
            have hsC_bound : δ ≤ separationStatistic R sN m hm_pos :=
              hδC sN m hm_pos hs_in_C
            have hrA_bound : separationStatistic R rN (m + 1 + Δ * n) hmn1_pos ≤ δ :=
              hδA rN (m + 1 + Δ * n) hmn1_pos hr_in_A
            have hrC_bound : δ ≤ separationStatistic R rN (m + Δ * n) hmn_pos :=
              hδC rN (m + Δ * n) hmn_pos hr_in_C
  
            have hθs_upper : R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ ≤ (m + 1 : ℝ) * δ := by
              have hm1_real : 0 < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm1_pos
              unfold separationStatistic at hsA_bound
              have h := (div_le_iff₀ hm1_real).1 hsA_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
            have hθs_lower : (m : ℝ) * δ ≤ R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ := by
              have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm_pos
              unfold separationStatistic at hsC_bound
              have h := (le_div_iff₀ hm_real).1 hsC_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
            have hθr_upper :
                R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ ≤ (m + 1 + Δ * n : ℝ) * δ := by
              have hmn1_real : 0 < ((m + 1 + Δ * n : ℕ) : ℝ) := by exact_mod_cast hmn1_pos
              unfold separationStatistic at hrA_bound
              have h := (div_le_iff₀ hmn1_real).1 hrA_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
            have hθr_lower :
                (m + Δ * n : ℝ) * δ ≤ R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ := by
              have hmn_real : 0 < ((m + Δ * n : ℕ) : ℝ) := by exact_mod_cast hmn_pos
              unfold separationStatistic at hrC_bound
              have h := (le_div_iff₀ hmn_real).1 hrC_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
  
            -- Use Θ scaling: Θ(rN) = n·θr and Θ(sN) = n·θs.
            have hθr_scale : R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ = n * θr := by
              simpa [rN, θr] using (Theta_scaleMult R r_old n)
            have hθs_scale : R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ = n * θs := by
              simpa [sN, θs] using (Theta_scaleMult R s_old n)
  
            -- Bracket n*(θr-θs) within (Δ*n ± 1)·δ.
            have h_abs_scaled : |(n : ℝ) * ((θr - θs) - (Δ : ℝ) * δ)| ≤ δ := by
              rw [abs_le]
              constructor <;> nlinarith only [hθr_lower, hθs_upper, hθr_upper, hθs_lower,
                hθr_scale, hθs_scale]
            have h_abs : |(θr - θs) - (Δ : ℝ) * δ| ≤ δ / (n : ℝ) := by
              rw [abs_mul, abs_of_pos hn_real] at h_abs_scaled
              exact (le_div_iff₀ hn_real).mpr (by simpa only [mul_comm] using h_abs_scaled)
            exact lt_of_le_of_lt h_abs hδ_div
  
          -- Conclude equality by the standard "arbitrarily small absolute difference" argument.
          have h_eq : θr - θs = (Δ : ℝ) * δ := by
            by_contra hne
            have hpos : 0 < |(θr - θs) - (Δ : ℝ) * δ| := by
              apply abs_pos.mpr
              intro h0
              apply hne
              exact (sub_eq_zero.mp h0)
            have h_small := h_close (|(θr - θs) - (Δ : ℝ) * δ| / 2) (half_pos hpos)
            have h_half : |(θr - θs) - (Δ : ℝ) * δ| / 2 < |(θr - θs) - (Δ : ℝ) * δ| :=
              half_lt_self hpos
            exact (lt_irrefl _ (lt_trans h_small h_half))
  
          simpa [θr, θs] using h_eq






end KnuthSkilling.Additive
