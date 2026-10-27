import KnuthSkilling.Additive.Proofs.GridInduction.Core.MultiGrid
import KnuthSkilling.Additive.Representation

/-!
# Extending a finite atom grid

Multiplicity vectors record how many times each authored atom occurs. Their ordered
fold `mu` determines a grid point; different vectors can determine the same point.
A real-valued observation descends to the reachable grid exactly when it is constant
on these fibres. This criterion does not identify the multiplicity vectors themselves.

The structural extension appends one atom, without assuming commutativity. The later
cut construction assigns its coefficient from the A/B/C comparison statistics.
`DeltaSpec_unique` proves that this coefficient is determined by those comparisons.
Strict base admissibility, used in `ThetaPrime`, remains a separate premise.
-/

namespace KnuthSkilling.Additive

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-- Append the new atom at the final coordinate. -/
def extendAtomFamily {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d) :
    AtomFamily α (k + 1) where
  atoms i := if h : i.val < k then F.atoms ⟨i.val, h⟩ else d
  pos i := by
    split_ifs with h
    · exact F.pos ⟨i.val, h⟩
    · exact hd

lemma extendAtomFamily_old {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (i : Fin k) :
    (extendAtomFamily F d hd).atoms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = F.atoms i := by
  simp [extendAtomFamily, i.isLt]

lemma extendAtomFamily_new {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d) :
    (extendAtomFamily F d hd).atoms ⟨k, Nat.lt_succ_self k⟩ = d := by
  simp [extendAtomFamily]

/-- Old-coordinate and final-coordinate agreement determine the entire family. -/
lemma AtomFamily.eq_extendAtomFamily_of_old_new {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (F' : AtomFamily α (k + 1))
    (hF'_old : ∀ i : Fin k,
      F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = F.atoms i)
    (hF'_new : F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d) :
    F' = extendAtomFamily F d hd := by
  have h : F'.atoms = (extendAtomFamily F d hd).atoms := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hF'_new.trans (extendAtomFamily_new F d hd).symm
    · exact (hF'_old j).trans (extendAtomFamily_old F d hd j).symm
  cases F'
  cases h
  rfl

/-- Split off the final coordinate, retaining all old coordinate occurrences. -/
def splitMulti {k : ℕ} (r : Multi (k + 1)) : Multi k × ℕ :=
  (fun i => r ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, r ⟨k, Nat.lt_succ_self k⟩)

/-- Reconstruct the multiplicity vector in its original coordinate order. -/
def joinMulti {k : ℕ} (r_old : Multi k) (t : ℕ) : Multi (k + 1) :=
  fun i => if h : i.val < k then r_old ⟨i.val, h⟩ else t

lemma splitMulti_joinMulti {k : ℕ} (r_old : Multi k) (t : ℕ) :
    splitMulti (joinMulti r_old t) = (r_old, t) := by
  apply Prod.ext
  · funext i
    exact dif_pos i.isLt
  · exact dif_neg (Nat.lt_irrefl k)

lemma joinMulti_splitMulti {k : ℕ} (r : Multi (k + 1)) :
    let (r_old, t) := splitMulti r
    joinMulti r_old t = r := by
  unfold splitMulti joinMulti
  ext i
  by_cases hi : i.val < k
  · simp [hi]
  · simp [hi]
    have hik : i.val = k := by omega
    have h : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hik
    rw [h]

/-- The explicit projection form is convenient for rewriting under other functions. -/
@[simp] lemma joinMulti_splitMulti_eq {k : ℕ} (r : Multi (k + 1)) :
    joinMulti (splitMulti r).1 (splitMulti r).2 = r := joinMulti_splitMulti r

lemma splitMulti_add {k : ℕ} (r s : Multi (k + 1)) :
    splitMulti (fun i => r i + s i) = ((fun i => (splitMulti r).1 i + (splitMulti s).1 i),
                                        (splitMulti r).2 + (splitMulti s).2) := rfl

lemma joinMulti_add {k : ℕ} (r_old s_old : Multi k) (t_r t_s : ℕ) :
    (fun i => joinMulti r_old t_r i + joinMulti s_old t_s i) =
    joinMulti (fun i => r_old i + s_old i) (t_r + t_s) := by
  funext i
  simp only [joinMulti]
  split_ifs <;> rfl

omit [KnuthSkillingAlgebraBase α] in
/-- Split the ordered enumeration at its last coordinate. -/
private lemma foldl_fin_succ_split {k : ℕ} (f : α → Fin (k + 1) → α) (acc : α) :
    List.foldl f acc (List.finRange (k + 1)) =
    f (List.foldl f acc ((List.finRange k).map (Fin.castAdd 1))) (Fin.last k) := by
  have h : (Fin.castSucc : Fin k → Fin (k + 1)) = Fin.castAdd 1 := rfl
  simp [List.finRange_succ_last, List.foldl_append, h]

/-- Appending an atom appends its iterate to the fold. No reordering is used. -/
lemma mu_extend_last {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (r_old : Multi k) (t : ℕ) :
    mu (extendAtomFamily F d hd) (joinMulti r_old t) =
    op (mu F r_old) (iterate_op d t) := by
  unfold mu
  rw [foldl_fin_succ_split, List.foldl_map]
  simp [extendAtomFamily, joinMulti, Fin.last]

/-- Every extended evaluation can be read through its old and final coordinates. -/
lemma mu_extend_split {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (r : Multi (k + 1)) :
    mu (extendAtomFamily F d hd) r =
      op (mu F (splitMulti r).1) (iterate_op d (splitMulti r).2) := by
  simpa only [joinMulti_splitMulti_eq] using
    mu_extend_last F d hd (splitMulti r).1 (splitMulti r).2

/-- The same law for an extension supplied by its coordinate agreements. -/
lemma mu_extend_last_of_old_new {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (F' : AtomFamily α (k + 1))
    (hF'_old : ∀ i : Fin k,
      F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i)
    (hF'_new : F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d)
    (r_old : Multi k) (t : ℕ) :
    mu F' (joinMulti r_old t) = op (mu F r_old) (iterate_op d t) := by
  rw [AtomFamily.eq_extendAtomFamily_of_old_new F d hd F' hF'_old hF'_new]
  exact mu_extend_last F d hd r_old t

variable [KSSeparation α]

/-! ## Observations on reachable grid points -/

/-- A chosen witness provides a readout on the reachable grid. Its computation rule
requires fibre invariance; the fallback is never observed on this subtype. -/
noncomputable def gridObservation {k : ℕ} (F : AtomFamily α k) (o : Multi k → ℝ) :
    {x // x ∈ kGrid F} → ℝ :=
  fun x => Function.extend (mu F) o (fun _ => 0) x.val

omit [KSSeparation α] in
theorem gridObservation_apply {k : ℕ} {F : AtomFamily α k} {o : Multi k → ℝ}
    (h : o.FactorsThrough (mu F)) (r : Multi k) :
    gridObservation F o ⟨mu F r, mu_mem_kGrid F r⟩ = o r :=
  h.extend_apply _ r

omit [KSSeparation α] in
/-- Descent is equivalent to fibre invariance, and is unique on reachable points. -/
theorem factorsThrough_mu_iff_existsUnique {k : ℕ} (F : AtomFamily α k) (o : Multi k → ℝ) :
    o.FactorsThrough (mu F) ↔
      ∃! q : {x // x ∈ kGrid F} → ℝ, ∀ r, q ⟨mu F r, mu_mem_kGrid F r⟩ = o r := by
  constructor
  · intro h
    refine ⟨gridObservation F o, gridObservation_apply h, ?_⟩
    intro q hq
    funext x
    obtain ⟨r, hr⟩ := x.property
    have hx : x = (⟨mu F r, mu_mem_kGrid F r⟩ : {x // x ∈ kGrid F}) := Subtype.ext hr
    rw [hx, hq, gridObservation_apply h]
  · rintro ⟨q, hq, _⟩ r s h
    rw [← hq r, ← hq s]
    exact congrArg q (Subtype.ext h)

/-- Restrict a supplied global representation to a grid. This does not construct a
global representation or assume that the atom parametrization is injective. -/
noncomputable def MultiGridRep.ofRepresentation {k : ℕ} (F : AtomFamily α k)
    (r : RepresentationResult α) : MultiGridRep F where
  Θ_grid x := r.Θ x.val
  strictMono := r.toOrderEmbedding.strictMono.comp (Subtype.strictMono_coe _)
  add a b := by
    have H : GridComm F := ⟨fun a b => r.op_comm (mu F a) (mu F b)⟩
    change r.Θ (mu F (a + b)) = _
    rw [mu_add_of_comm H, r.additive]
  ident_eq_zero := r.ident_zero_of_ident

/-! ## The cut coefficient and its comparison laws

Following K&S Appendix A, once we have the extended family F', we need to:
1. Choose δ (the representation value for the new atom d):
   - Case B non-empty: δ = common statistic from B witnesses
   - Case B empty: δ = limit value from accuracy lemma
2. Define Θ' on kGrid F' via: Θ'(μ(F', r_old, t)) := Θ(μ(F, r_old)) + t * δ
3. Prove Θ' satisfies MultiGridRep requirements (strict mono, additive, normalized)
-/

omit [KSSeparation α] in
/-- When B is empty, A is non-empty (zero multiplicity is always in A). -/
lemma extensionSetA_nonempty_of_B_empty {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (_hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u := by
  -- Take zero multiplicity and u = 1
  refine ⟨fun _ => 0, 1, Nat.one_pos, ?_⟩
  simp only [extensionSetA, Set.mem_ofPred_eq]
  -- μ(F, 0) = ident < d = d^1
  have : mu F (fun _ => 0) = ident := mu_zero (F := F)
  rw [this, iterate_op_one]
  exact hd

/-- When B is empty and k ≥ 1, C is non-empty (by Archimedean property). -/
lemma extensionSetC_nonempty_of_B_empty {k : ℕ} (F : AtomFamily α k) (hk : k ≥ 1) (d : α) (_hd : ident < d)
    (_hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u := by
  -- Pick any atom from F (exists since k ≥ 1)
  have : 0 < k := hk
  let i₀ : Fin k := ⟨0, this⟩
  let a := F.atoms i₀
  have ha : ident < a := F.pos i₀
  -- By Archimedean property, ∃ N such that d < a^N
  obtain ⟨N, hN⟩ := bounded_by_iterate a ha d
  -- Take r = unitMulti i₀ N and u = 1
  refine ⟨unitMulti i₀ N, 1, Nat.one_pos, ?_⟩
  simp only [extensionSetC, Set.mem_ofPred_eq]
  -- d^1 = d < a^N = μ(F, unitMulti i₀ N)
  rw [iterate_op_one]
  have : mu F (unitMulti i₀ N) = iterate_op a N := mu_unitMulti F i₀ N
  rw [this]
  exact hN

/-- Choose the representation value δ for the new atom d.
This is the Θ-value we assign to d in the extended representation. -/
noncomputable def chooseδ {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1) (R : MultiGridRep F)
    (d : α) (hd : ident < d) : ℝ :=
  if hB : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u then
    -- Case B non-empty: use common statistic
    B_common_statistic R d hd hB
  else
    -- Case B empty: use B_empty_delta
    have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u := fun r u hu hr => hB ⟨r, u, hu, hr⟩
    have hA : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
      extensionSetA_nonempty_of_B_empty F d hd hB_empty
    have hC : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
      extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
    B_empty_delta R d hd hB_empty hA hC

/-! ### ZQuantized: A (Strong) Quantization Hypothesis

`ZQuantized F R δ` says every k-grid value of `R.Θ_grid` is an integer multiple of a *fixed*
step `δ`. This property is useful for “mesh collapse” lemmas (closing a width-`2δ` window to an
exact integer).

Important: in the B-empty branch, `chooseδ` is defined as a `sSup` of A-statistics. In general,
there is no reason for this newly chosen `δ := chooseδ hk R d hd` to be commensurate with the
existing k-grid values, so `ZQuantized F R (chooseδ hk R d hd)` should not be treated as an
automatic inductive invariant of the extension step.

Even a nonempty B-region does not imply quantization: on the additive nonnegative
reals, a grid generated by 1 contains value 1, whereas appending 2 chooses coefficient
2. The old value 1 is not an integer multiple of 2.
-/

/-- ZQuantized: Every Θ-value on the k-grid is an integer multiple of δ.
This additional commensurability premise closes the floor bracket; it is not automatic. -/
def ZQuantized {k : ℕ} (F : AtomFamily α k) (R : MultiGridRep F) (δ : ℝ) : Prop :=
  ∀ r : Multi k, ∃ m : ℤ, R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ = (m : ℝ) * δ

/-- Cast bookkeeping for the ZQuantized induction step:
turn `m*δ + t*δ` into `(m+t)*δ` where `m : ℤ` and `t : ℕ`. -/
lemma zquantized_cast_add (m : ℤ) (t : ℕ) (δ : ℝ) :
    (m : ℝ) * δ + (t : ℝ) * δ = ((m + (t : ℤ)) : ℝ) * δ := by
  simp [add_mul]

/-- If every Θ on the k-grid is an integer multiple of δ, then differences are too. -/
lemma ZQuantized_diff
    {k : ℕ} {F : AtomFamily α k} {R : MultiGridRep F} {δ : ℝ}
    (hQZ : ZQuantized F R δ)
    (r s : Multi k) :
    ∃ m : ℤ,
      R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
      R.Θ_grid ⟨mu F s, mu_mem_kGrid F s⟩ = (m : ℝ) * δ := by
  rcases hQZ r with ⟨mr, hmr⟩
  rcases hQZ s with ⟨ms, hms⟩
  refine ⟨mr - ms, ?_⟩
  rw [hmr, hms, Int.cast_sub, sub_mul]

/-- Collapse the ±δ bracket to the unique integer.
If an integer multiple of δ lies strictly between ((Δ-1)·δ) and ((Δ+1)·δ),
then it must be exactly Δ·δ. -/
lemma int_multiple_eq_of_tight_bounds
    {δ : ℝ} (hδ : 0 < δ) {Δ : ℕ} {m : ℤ}
    {x : ℝ} (hx : x = (m : ℝ) * δ)
    (hlo : ((Δ : ℝ) - 1) * δ < x)
    (hhi : x < ((Δ : ℝ) + 1) * δ) :
    m = (Δ : ℤ) := by
  -- Divide strict inequalities by δ > 0
  rw [hx] at hlo hhi
  have hlo' : (Δ : ℝ) - 1 < (m : ℝ) := by
    have := (mul_lt_mul_iff_left₀ hδ).1 hlo
    linarith
  have hhi' : (m : ℝ) < (Δ : ℝ) + 1 := by
    have := (mul_lt_mul_iff_left₀ hδ).1 hhi
    linarith
  -- Now (Δ-1) < m < (Δ+1) in ℝ
  -- Since m is an integer and Δ is a natural number, the only possibility is m = Δ
  have h₁ : m < (Δ : ℤ) + 1 := by
    have : (m : ℝ) < ((Δ : ℤ) + 1 : ℤ) := by
      simp only [Int.cast_add, Int.cast_one, Int.cast_natCast]
      exact hhi'
    exact Int.cast_lt.mp this
  have h₂ : (Δ : ℤ) - 1 < m := by
    have : ((Δ : ℤ) - 1 : ℤ) < (m : ℝ) := by
      simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast]
      exact hlo'
    exact Int.cast_lt.mp this
  omega

/-- Integer-multiple collapses inside a width-2δ window.
    If x is an integer multiple of δ and lies strictly between (Δ-1)·δ and (Δ+1)·δ,
    then x = Δ·δ exactly. This is the key "mesh collapse" lemma. -/
lemma intmul_eq_in_2δ_window
    {δ x : ℝ} {Δ : ℤ}
    (hδ : 0 < δ)
    (hZ : ∃ m : ℤ, x = (m : ℝ) * δ)
    (hlo : ((Δ : ℝ) - 1) * δ < x)
    (hhi : x < ((Δ : ℝ) + 1) * δ) :
    x = (Δ : ℝ) * δ := by
  rcases hZ with ⟨m, rfl⟩
  have : m = Δ := by
    by_contra hne
    have hm_lt : m ≤ Δ - 1 ∨ Δ + 1 ≤ m := by
      have := lt_trichotomy m Δ
      rcases this with hlt | hEQ | hgt
      · -- `Int.le_of_lt_add_one` wants `m < (Δ - 1) + 1`; rewrite using `sub_add_cancel`.
        have hlt' : m < (Δ - 1) + 1 := by
          simpa [sub_add_cancel] using hlt
        exact Or.inl (Int.le_of_lt_add_one hlt')      -- m ≤ Δ - 1
      · exact (hne hEQ).elim
      · exact Or.inr (Int.add_one_le_of_lt hgt)      -- Δ + 1 ≤ m
    rcases hm_lt with hle | hge
    · have : (m : ℝ) * δ ≤ ((Δ : ℝ) - 1) * δ := by
        have : (m : ℝ) ≤ (Δ : ℝ) - 1 := by exact_mod_cast hle
        exact mul_le_mul_of_nonneg_right this (le_of_lt hδ)
      exact (not_lt_of_ge this hlo).elim
    · have : ((Δ : ℝ) + 1) * δ ≤ (m : ℝ) * δ := by
        have : (Δ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hge
        exact mul_le_mul_of_nonneg_right this (le_of_lt hδ)
      exact (not_lt_of_ge this hhi).elim
  simp [this]

/-! ### Theta' Helper Lemmas

These lemmas establish key properties of the extended representation Θ':
1. δ > 0 (chooseδ is always positive)
2. Theta'_increment_t: Incrementing t increases Θ' by exactly δ
3. Theta'_strictMono_same_t: With fixed t, Θ' is strictly monotone in the old part

These are used to complete the extend_grid_rep_with_atom proof.
-/

/-- δ is positive in both branches of `chooseδ`. -/
lemma delta_pos {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d) :
    0 < chooseδ hk R d hd := by
  classical
  unfold chooseδ
  split_ifs with hB
  · -- B ≠ ∅: δ = B_common_statistic = Θ(d^u)/u with u>0
    -- Extract a concrete B-witness without destroying hB
    have ⟨r,u,hu,hr⟩ := hB
    have hstat :
      B_common_statistic R d hd hB = separationStatistic R r u hu :=
      B_common_statistic_eq_any_witness R IH d hd hB r u hu hr
    -- Expand the statistic and use strict monotonicity + Θ(ident)=0
    simp [hstat, separationStatistic]
    -- Since ident < d^u, strict monotonicity of Θ_grid gives Θ(d^u) > Θ(ident)=0
    -- Key: hr : r ∈ extensionSetB means mu F r = iterate_op d u
    have h_mu_eq : mu F r = iterate_op d u := by simpa [extensionSetB] using hr
    -- So ident < mu F r (via ident < d^u = mu F r)
    have h_ident_lt : ident < mu F r := by
      rw [h_mu_eq]
      exact iterate_op_pos d hd u hu
    have hθ : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩
              > R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ :=
      R.strictMono h_ident_lt
    have huℝ : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
    have : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
      by simpa [R.ident_eq_zero] using hθ
    exact div_pos this huℝ
  · -- B = ∅: B_empty_delta lies strictly between A and C statistics
    have hC : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
      extensionSetC_nonempty_of_B_empty F hk d hd
        (by intro r u hu hr; exact hB ⟨r,u,hu,hr⟩)
    rcases hC with ⟨r,u,hu,hrC⟩
    -- Key: By Archimedean property, the same r is in A(N) for large enough N
    -- So B_empty_delta ≥ Θ(mu F r)/N > 0
    have hθ_pos : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      have h_ident_lt : ident < mu F r := by
        have hμ : iterate_op d u < mu F r := by simpa [extensionSetC] using hrC
        calc ident < iterate_op d u := iterate_op_pos d hd u hu
          _ < mu F r := hμ
      have hθ : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ >
                R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ :=
        R.strictMono h_ident_lt
      simpa [R.ident_eq_zero] using hθ
    -- Use Archimedean to find N with mu F r < d^N (so r ∈ A(N))
    obtain ⟨N, hN_bound⟩ := bounded_by_iterate d hd (mu F r)
    have hN_pos : 0 < N := by
      by_contra h_not
      push Not at h_not
      have : N = 0 := Nat.eq_zero_of_le_zero h_not
      subst this
      simp [iterate_op_zero] at hN_bound
      exact absurd hN_bound (not_lt.mpr (ident_le (mu F r)))
    have hrA : r ∈ extensionSetA F d N := by simpa [extensionSetA] using hN_bound
    have hN_stat_pos : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / N := by
      have hNℝ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN_pos
      exact div_pos hθ_pos hNℝ
    -- B_empty_delta = sSup {A-statistics} ≥ Θ(mu F r)/N > 0
    have h_stat_in : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / N ∈
      {s : ℝ | ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' ∧
        s = R.Θ_grid ⟨mu F r', mu_mem_kGrid F r'⟩ / u'} := by
      exact ⟨r, N, hN_pos, hrA, rfl⟩
    unfold B_empty_delta
    exact lt_csSup_of_lt
      (by {
        -- Bounded above by the C-statistic (r, u) using separation_property
        use separationStatistic R r u hu
        intro s ⟨r', u', hu', hrA', hs⟩
        subst hs
        -- Every A-statistic is < every C-statistic by separation_property
        exact le_of_lt (separation_property R H IH hd hu' hrA' hu hrC)
      })
      (by exact h_stat_in)
      hN_stat_pos

/-- chooseδ satisfies the A-bound: all A-statistics are ≤ δ. -/
lemma chooseδ_A_bound {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) :
    ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u →
      separationStatistic R r u hu ≤ chooseδ hk R d hd := by
  intro r u hu hrA
  unfold chooseδ
  split_ifs with hB_exists
  · -- B ≠ ∅: δ = B_common_statistic
    -- The B-statistic is the boundary separating A from C
    -- All A-statistics are < B-statistic by separation_property_A_B
    have hB_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u := hB_exists
    rcases hB_nonempty with ⟨rB, uB, huB, hrB⟩
    have h_B_eq : B_common_statistic R d hd hB_exists = separationStatistic R rB uB huB :=
      B_common_statistic_eq_any_witness R IH d hd hB_exists rB uB huB hrB
    rw [h_B_eq]
    exact le_of_lt (separation_property_A_B R H hd hu hrA huB hrB)
  · -- B = ∅: δ = B_empty_delta = sSup of A-statistics
    -- So A-stat ≤ sSup(A-statistics) = δ by definition
    have hB_empty : ∀ r' u', 0 < u' → r' ∉ extensionSetB F d u' :=
      fun r' u' hu' hr' => hB_exists ⟨r', u', hu', hr'⟩
    have hA_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' :=
      extensionSetA_nonempty_of_B_empty F d hd hB_empty
    have hC_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetC F d u' :=
      extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
    -- B_empty_delta is defined as sSup of A-statistics
    -- So our A-stat is ≤ sSup by le_csSup
    have h_in_set : separationStatistic R r u hu ∈
        {s : ℝ | ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' ∧
          s = R.Θ_grid ⟨mu F r', mu_mem_kGrid F r'⟩ / u'} := by
      use r, u, hu, hrA
      rfl
    have h_bdd : BddAbove {s : ℝ | ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' ∧
        s = R.Θ_grid ⟨mu F r', mu_mem_kGrid F r'⟩ / u'} := by
      obtain ⟨rC, uC, huC, hrC⟩ := hC_nonempty
      use separationStatistic R rC uC huC
      intro s ⟨r', u', hu', hrA', hs⟩
      subst hs
      exact le_of_lt (separation_property R H IH hd hu' hrA' huC hrC)
    simp only [separationStatistic]
    exact le_csSup h_bdd h_in_set

/-- chooseδ satisfies the C-bound: δ ≤ all C-statistics. -/
lemma chooseδ_C_bound {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) :
    ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u →
      chooseδ hk R d hd ≤ separationStatistic R r u hu := by
  intro r u hu hrC
  unfold chooseδ
  split_ifs with hB_exists
  · -- B ≠ ∅: δ = B_common_statistic
    -- The B-statistic is the boundary separating A from C
    -- B-statistic < C-statistics by separation_property_B_C
    have hB_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u := hB_exists
    rcases hB_nonempty with ⟨rB, uB, huB, hrB⟩
    have h_B_eq : B_common_statistic R d hd hB_exists = separationStatistic R rB uB huB :=
      B_common_statistic_eq_any_witness R IH d hd hB_exists rB uB huB hrB
    rw [h_B_eq]
    exact le_of_lt (separation_property_B_C R H hd huB hrB hu hrC)
  · -- B = ∅: δ = B_empty_delta = sSup of A-statistics
    -- sSup(A) ≤ C-stat by separation_property (all A < all C)
    have hB_empty : ∀ r' u', 0 < u' → r' ∉ extensionSetB F d u' :=
      fun r' u' hu' hr' => hB_exists ⟨r', u', hu', hr'⟩
    have hA_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' :=
      extensionSetA_nonempty_of_B_empty F d hd hB_empty
    have hC_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetC F d u' :=
      extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
    -- sSup(A-stats) ≤ C-stat because all A-stats < C-stat (separation)
    apply csSup_le
    · -- Set is nonempty
      obtain ⟨rA, uA, huA, hrA⟩ := hA_nonempty
      use R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ / uA
      exact ⟨rA, uA, huA, hrA, rfl⟩
    · -- Every element is ≤ the C-statistic
      intro s ⟨r', u', hu', hrA', hs⟩
      subst hs
      simp only [separationStatistic]
      exact le_of_lt (separation_property R H IH hd hu' hrA' hu hrC)

/-- chooseδ satisfies the B-bound: all B-statistics equal δ. -/
lemma chooseδ_B_bound {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (d : α) (hd : ident < d) :
    ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u →
      separationStatistic R r u hu = chooseδ hk R d hd := by
  intro r u hu hrB
  unfold chooseδ
  split_ifs with hB_exists
  · -- B ≠ ∅: δ = B_common_statistic
    -- B_common_statistic equals any B-witness's statistic
    exact (B_common_statistic_eq_any_witness R IH d hd hB_exists r u hu hrB).symm
  · -- B = ∅: Contradiction - we have r ∈ B but B is empty!
    exfalso
    exact hB_exists ⟨r, u, hu, hrB⟩

/-! ## Uniqueness of the cut coefficient

B-witnesses determine the coefficient exactly. Without B-witnesses, the accuracy
lemma supplies A/C brackets of arbitrarily small width, so two admissible
coefficients cannot differ. The statement retains both comparison inequalities.
-/

/-- The specification that any valid δ must satisfy. -/
def DeltaSpec {k : ℕ} (F : AtomFamily α k) (R : MultiGridRep F)
    (d : α) (_hd : ident < d) (v : ℝ) : Prop :=
  (∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu ≤ v) ∧
  (∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → v ≤ separationStatistic R r u hu) ∧
  (∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = v)

/-- chooseδ satisfies the DeltaSpec. -/
lemma chooseδ_spec {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) :
    DeltaSpec F R d hd (chooseδ hk R d hd) := by
  refine ⟨?hA, ?hC, ?hB⟩
  · -- A-bound
    exact chooseδ_A_bound hk R IH H d hd
  · -- C-bound
    exact chooseδ_C_bound hk R IH H d hd
  · -- B-bound
    intro r u hu hrB
    exact chooseδ_B_bound hk R IH d hd r u hu hrB

/-- Any two values satisfying DeltaSpec are equal (the uniqueness hammer).

The proof splits on B nonempty vs B empty:
- B nonempty: Both values equal the B-statistic, hence equal each other
- B empty: Both are squeezed between A-stats (below) and C-stats (above).
  The accuracy lemma shows A-stats and C-stats get arbitrarily close,
  so the squeeze forces equality. -/
lemma DeltaSpec_unique {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (_IH : GridBridge F) (_H : GridComm F)
    (d : α) (hd : ident < d) {v w : ℝ}
    (hv : DeltaSpec F R d hd v) (hw : DeltaSpec F R d hd w) :
    v = w := by
  by_cases hB : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u
  · obtain ⟨r, u, hu, hr⟩ := hB
    exact (hv.2.2 r u hu hr).symm.trans (hw.2.2 r u hu hr)
  · have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u :=
      fun r u hu hr => hB ⟨r, u, hu, hr⟩
    by_contra hne
    have hε : 0 < |v - w| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨rA, uA, huA, hrA, rC, uC, huC, hrC, hgap⟩ :=
      accuracy_lemma R d hd hB_empty
        (extensionSetA_nonempty_of_B_empty F d hd hB_empty)
        (extensionSetC_nonempty_of_B_empty F hk d hd hB_empty)
        (|v - w| / 2) (by linarith)
    have hAv := hv.1 rA uA huA hrA
    have hCv := hv.2.1 rC uC huC hrC
    have hAw := hw.1 rA uA huA hrA
    have hCw := hw.2.1 rC uC huC hrC
    have hdist : |v - w| ≤ separationStatistic R rC uC huC -
        separationStatistic R rA uA huA := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

/-- If v satisfies DeltaSpec, then v = chooseδ.

This is the main hammer for path-independence:
Any construction that produces a valid δ (satisfying the A/B/C bounds)
must produce exactly chooseδ. -/
lemma delta_unique {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d) {v : ℝ}
    (hv : DeltaSpec F R d hd v) :
    v = chooseδ hk R d hd := by
  have hw := chooseδ_spec hk R IH H d hd
  exact DeltaSpec_unique hk R IH H d hd hv hw

/-- The independently constructed cut agrees with a supplied global representation.
This is an interpretation law for given representation data, not an existence argument. -/
lemma chooseδ_ofRepresentation {k : ℕ} (hk : k ≥ 1) (F : AtomFamily α k)
    (r : RepresentationResult α) (d : α) (hd : ident < d) :
    chooseδ hk (MultiGridRep.ofRepresentation F r) d hd = r.Θ d := by
  have H : GridComm F := ⟨fun a b => r.op_comm (mu F a) (mu F b)⟩
  symm
  apply delta_unique hk (MultiGridRep.ofRepresentation F r) (gridBridge_of_gridComm H) H d hd
  refine ⟨?_, ?_, ?_⟩
  · intro a u hu ha
    change r.Θ (mu F a) / (u : ℝ) ≤ r.Θ d
    apply (div_le_iff₀ (Nat.cast_pos.mpr hu : (0 : ℝ) < u)).mpr
    have h := (r.strict_order_preserving (mu F a) (iterate_op d u)).mp ha
    rw [r.map_iterate] at h
    simpa only [mul_comm] using h.le
  · intro a u hu ha
    change r.Θ d ≤ r.Θ (mu F a) / (u : ℝ)
    apply (le_div_iff₀ (Nat.cast_pos.mpr hu : (0 : ℝ) < u)).mpr
    have h := (r.strict_order_preserving (iterate_op d u) (mu F a)).mp ha
    rw [r.map_iterate] at h
    simpa only [mul_comm] using h.le
  · intro a u hu ha
    change r.Θ (mu F a) / (u : ℝ) = r.Θ d
    apply (div_eq_iff (ne_of_gt (Nat.cast_pos.mpr hu : (0 : ℝ) < u))).mpr
    have h := congrArg r.Θ (show mu F a = iterate_op d u from ha)
    rw [r.map_iterate] at h
    simpa only [mul_comm] using h

/-- Preserving the evaluated grid points and their observations preserves the cut.
No injectivity of the witness embedding and no B-witness are required. -/
lemma chooseδ_eq_of_grid_embedding {k l : ℕ} (hk : k ≥ 1) (hl : l ≥ 1)
    {F : AtomFamily α k} {G : AtomFamily α l} (R : MultiGridRep F) (S : MultiGridRep G)
    (IH : GridBridge F) (H : GridComm F) (IHG : GridBridge G) (HG : GridComm G)
    (e : Multi k → Multi l) (hmu : ∀ r, mu G (e r) = mu F r)
    (hobs : ∀ r, S.Θ_grid ⟨mu G (e r), mu_mem_kGrid G _⟩ =
      R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩) (d : α) (hd : ident < d) :
    chooseδ hk R d hd = chooseδ hl S d hd := by
  symm
  apply delta_unique hk R IH H d hd
  have hs := chooseδ_spec hl S IHG HG d hd
  refine ⟨?_, ?_, ?_⟩
  · intro r u hu hr
    have h := hs.1 (e r) u hu (by simpa only [extensionSetA, Set.mem_ofPred_eq, hmu] using hr)
    simpa only [separationStatistic, hobs] using h
  · intro r u hu hr
    have h := hs.2.1 (e r) u hu (by simpa only [extensionSetC, Set.mem_ofPred_eq, hmu] using hr)
    simpa only [separationStatistic, hobs] using h
  · intro r u hu hr
    have h := hs.2.2 (e r) u hu (by simpa only [extensionSetB, Set.mem_ofPred_eq, hmu] using hr)
    simpa only [separationStatistic, hobs] using h

/-- The historical monotonicity law follows from exact preservation of the cut. -/
lemma chooseδ_monotone_family
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (y : α) (hy : ident < y)
    {F' : AtomFamily α (k + 1)} (R' : MultiGridRep F')
    (hF'_old : ∀ i : Fin k, F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i)
    (hF'_new : F'.atoms ⟨k, Nat.lt_succ_self k⟩ = y)
    (hR'_extends : ∀ (r : Multi k),
        R'.Θ_grid ⟨mu F' (joinMulti r 0), mu_mem_kGrid F' (joinMulti r 0)⟩ =
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩)
    (hk' : k + 1 ≥ 1) (IH' : GridBridge F') (H' : GridComm F')
    (x : α) (hx : ident < x) :
    chooseδ hk R x hx ≤ chooseδ hk' R' x hx := by
  apply le_of_eq
  apply chooseδ_eq_of_grid_embedding hk hk' R R' IH H IH' H'
    (fun r => joinMulti r 0) ?_ hR'_extends x hx
  intro r
  simpa only [iterate_op_zero, op_ident_right] using
    mu_extend_last_of_old_new F y hy F' hF'_old hF'_new r 0

/-- Historical B-nonempty interface. Exact grid preservation suffices even when B is empty. -/
lemma chooseδ_eq_of_B_nonempty
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (y : α) (hy : ident < y)
    {F' : AtomFamily α (k + 1)} (R' : MultiGridRep F')
    (hF'_old : ∀ i : Fin k, F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i)
    (hF'_new : F'.atoms ⟨k, Nat.lt_succ_self k⟩ = y)
    (hR'_extends : ∀ (r : Multi k),
        R'.Θ_grid ⟨mu F' (joinMulti r 0), mu_mem_kGrid F' (joinMulti r 0)⟩ =
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩)
    (hk' : k + 1 ≥ 1) (IH' : GridBridge F') (H' : GridComm F')
    (x : α) (hx : ident < x)
    (_hB : ∃ r u, 0 < u ∧ r ∈ extensionSetB F x u) :
    chooseδ hk R x hx = chooseδ hk' R' x hx := by
  apply chooseδ_eq_of_grid_embedding hk hk' R R' IH H IH' H'
    (fun r => joinMulti r 0) ?_ hR'_extends x hx
  intro r
  simpa only [iterate_op_zero, op_ident_right] using
    mu_extend_last_of_old_new F y hy F' hF'_old hF'_new r 0

/-- An extension satisfying the supplied coefficient formula satisfies its base cut.
The formula already fixes the new coefficient to `chooseδ`; this is a compatibility
lemma for that formula, not a uniqueness theorem for arbitrary extensions. -/
lemma ext_value_satisfies_base_spec
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    {F' : AtomFamily α (k + 1)} (R' : MultiGridRep F')
    (_hF'_old : ∀ i : Fin k, F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i)
    (_hF'_new : F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d)
    (hR'_extends : ∀ (r : Multi k) (t : ℕ),
        R'.Θ_grid ⟨mu F' (joinMulti r t), mu_mem_kGrid F' (joinMulti r t)⟩ =
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ + (t : ℝ) * chooseδ hk R d hd) :
    let v := R'.Θ_grid ⟨mu F' (unitMulti ⟨k, Nat.lt_succ_self k⟩ 1), mu_mem_kGrid F' _⟩
    DeltaSpec F R d hd v := by
  have hunit : unitMulti ⟨k, Nat.lt_succ_self k⟩ 1 = joinMulti (fun _ => 0) 1 := by
    funext i
    by_cases hi : i.val < k
    · have hne : i ≠ ⟨k, Nat.lt_succ_self k⟩ := by
        intro h
        have heq : i.val = k := congrArg Fin.val h
        omega
      simp [unitMulti, joinMulti, hi, hne]
    · have hlast : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by change i.val = k; have := i.isLt; omega)
      subst i
      simp [unitMulti, joinMulti]
  have h0 : R.Θ_grid ⟨mu F (fun _ => 0), mu_mem_kGrid F _⟩ = 0 := by
    simpa only [mu_zero] using R.ident_eq_zero
  dsimp only
  rw [hunit, hR'_extends, h0, Nat.cast_one, one_mul, zero_add]
  exact chooseδ_spec hk R IH H d hd

/-- Under the supplied full coefficient formula, the new coordinate reads `chooseδ`. -/
lemma ext_value_eq_chooseδ
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    {F' : AtomFamily α (k + 1)} (R' : MultiGridRep F')
    (hF'_old : ∀ i : Fin k, F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i)
    (hF'_new : F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d)
    (hR'_extends : ∀ (r : Multi k) (t : ℕ),
        R'.Θ_grid ⟨mu F' (joinMulti r t), mu_mem_kGrid F' (joinMulti r t)⟩ =
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ + (t : ℝ) * chooseδ hk R d hd) :
    R'.Θ_grid ⟨mu F' (unitMulti ⟨k, Nat.lt_succ_self k⟩ 1), mu_mem_kGrid F' _⟩ =
    chooseδ hk R d hd := by
  have spec := ext_value_satisfies_base_spec hk R IH H d hd R' hF'_old hF'_new hR'_extends
  exact delta_unique hk R IH H d hd spec

/-! ### δ-Scaling: chooseδ(d²) = 2 * chooseδ(d)

When we compute δ for extending with d² = d⊕d, it equals twice the δ for extending with d.

**Key insight**: B-witnesses scale appropriately:
- If (r, u) is a B-witness for d (mu r = d^u), then (scaleMult 2 r, u) is a B-witness for d² (mu(2r) = (d^u)² = (d²)^u)
- The separation statistic doubles: θ(2r)/u = 2θ(r)/u = 2δ

For B = ∅ case:
- A-witnesses for d² correspond to A-witnesses for d at even levels
- By accuracy argument, sSup at even levels equals sSup at all levels
- Therefore δ_{d²} = 2 * δ_d
-/

omit [KSSeparation α] in
/-- The positivity of iterate_op d 2 = d ⊕ d. -/
lemma iterate_op_two_pos (d : α) (hd : ident < d) : ident < iterate_op d 2 := by
  exact iterate_op_pos d hd 2 (by decide)

/-- **δ-scaling lemma**: chooseδ for d² equals twice chooseδ for d.

This is the key to proving additivity in the x = y case:
- Θ(x ⊕ x) is defined using chooseδ(R₁, x⊕x)
- We need this to equal 2 * Θ(x) = 2 * chooseδ(R₁, x)
-/
lemma chooseδ_square_scaling {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) :
    chooseδ hk R (iterate_op d 2) (iterate_op_two_pos d hd) = 2 * chooseδ hk R d hd := by
  have hs := chooseδ_spec hk R IH H d hd
  have hstat r u (hu : 0 < u) :
      separationStatistic R r u hu =
        2 * separationStatistic R r (2 * u) (by omega) := by
    simp only [separationStatistic, Nat.cast_mul, Nat.cast_ofNat]
    ring
  symm
  apply delta_unique hk R IH H (iterate_op d 2) (iterate_op_two_pos d hd)
  refine ⟨?_, ?_, ?_⟩
  · intro r u hu hr
    have h := hs.1 r (2 * u) (by omega)
      (by simpa only [extensionSetA, Set.mem_ofPred_eq, iterate_op_mul] using hr)
    rw [hstat r u hu]
    linarith
  · intro r u hu hr
    have h := hs.2.1 r (2 * u) (by omega)
      (by simpa only [extensionSetC, Set.mem_ofPred_eq, iterate_op_mul] using hr)
    rw [hstat r u hu]
    linarith
  · intro r u hu hr
    have h := hs.2.2 r (2 * u) (by omega)
      (by simpa only [extensionSetB, Set.mem_ofPred_eq, iterate_op_mul] using hr)
    rw [hstat r u hu, h]

end KnuthSkilling.Additive
