import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.Induction.ThetaPrime

set_option linter.unnecessarySimpa false

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
Goertzel (Foundations-of-inference-new-proofs_v1, Lemma 7) reframes the B-empty difficulty as an
*order-invariance inside an admissible gap* statement:

If a B-empty extension step admits multiple admissible choices for the new “slope”/parameter, then
the relative order between any two newly-formed expressions should be independent of which
admissible choice is used; otherwise some “critical value” would force an equality, contradicting
the B-empty assumption.

This file records that idea in the current refactored codebase vocabulary, and links it to the
existing explicit blocker `BEmptyStrictGapSpec` in `ThetaPrime.lean`.

Status: This file currently provides *interfaces* (no placeholder proofs) that make the Goertzel
dependency explicit. Proving these interfaces from the existing K&S `Core/` development is the
next step.

Important: Goertzel’s Lemma 7 proof sketch contains the inference
“`X ⊕ d^n = Y` (old `X,Y`) ⇒ an old-grid value equals `d^n`”, i.e. a B-witness for `n`.
This is not valid in general for an associative ordered monoid: it would require additional
structure (e.g. a cancellative group/inverses, or a special unique-decomposition property).
See the concrete counterexample `lean-projects/mettapedia/Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/GoertzelLemma7.lean`.
-/

section
variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d)

noncomputable def ThetaRaw (δ : ℝ) (r_old : Multi k) (t : ℕ) : ℝ :=
  R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ

/-- The extended μ-value of a join-multiplicity witness, packaged as an element of the extended k-grid. -/
noncomputable def joinPoint (r_old : Multi k) (t : ℕ) :
    {x // x ∈ kGrid (extendAtomFamily F d hd)} :=
  ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
    mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩

/-- The (finite) “two-point slice” of the extended k-grid used by the Ben/Goertzel Lemma‑7 flip argument. -/
def joinPairSet (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) :
    Set {x // x ∈ kGrid (extendAtomFamily F d hd)} :=
  {p | p = joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x ∨
        p = joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y}

/-- A *realization* of the Ben/Goertzel `ThetaRaw` formula on the extended μ-grid.

This packages the missing link in Goertzel/Ben Lemma 7: to turn a *numeric* equality
`ThetaRaw δ … = ThetaRaw δ …` into an *algebraic* equality on the extended grid, one needs an
actual evaluator on `kGrid (extendAtomFamily F d hd)` that is strictly monotone (hence injective)
and agrees with `ThetaRaw` on the `joinMulti` witnesses. -/
def RealizesThetaRaw (δ : ℝ) : Prop :=
  ∃ Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ,
    StrictMono Θ' ∧
      (∀ (r_old : Multi k) (t : ℕ),
          Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
                mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
            ThetaRaw (R := R) (F := F) δ r_old t)

/-- A *local* realization of `ThetaRaw` on just two join-multiplicity points.

This is the minimal hypothesis needed to turn a single numeric equality
`ThetaRaw δ r_old_x t_x = ThetaRaw δ r_old_y t_y` into an equality of the corresponding μ-values.
It is strictly weaker than `RealizesThetaRaw` (which provides a strictly monotone evaluator on the
entire extended k-grid). -/
def RealizesThetaRaw_pair (δ : ℝ) (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) : Prop :=
  ∃ Θ' : {p // p ∈ joinPairSet (F := F) (d := d) (hd := hd) r_old_x r_old_y t_x t_y} → ℝ,
    StrictMono Θ' ∧
      Θ' ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x, Or.inl rfl⟩ =
          ThetaRaw (R := R) (F := F) δ r_old_x t_x ∧
      Θ' ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y, Or.inr rfl⟩ =
          ThetaRaw (R := R) (F := F) δ r_old_y t_y

lemma realizesThetaRaw_pair_of_realizesThetaRaw
    {δ : ℝ} (hδ : RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) δ)
    (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) :
    RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r_old_x r_old_y t_x t_y := by
  classical
  rcases hδ with ⟨Θ', hΘ'_mono, hΘ'_on_join⟩
  refine ⟨fun p => Θ' p.1, ?_, ?_, ?_⟩
  · intro a b hab
    exact hΘ'_mono hab
  · -- left point
    simp [joinPoint, hΘ'_on_join]
  · -- right point
    simp [joinPoint, hΘ'_on_join]

lemma ThetaRaw_eq_implies_mu_joinMulti_eq
    {δ : ℝ} (hδ : RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) δ)
    (r_old_x r_old_y : Multi k) (t_x t_y : ℕ)
    (hEq :
      ThetaRaw (R := R) (F := F) δ r_old_x t_x =
        ThetaRaw (R := R) (F := F) δ r_old_y t_y) :
    mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x) =
      mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y) := by
  classical
  rcases hδ with ⟨Θ', hΘ'_mono, hΘ'_on_join⟩
  have hEq' :
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x t_x)⟩ =
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y t_y)⟩ := by
    simpa [hΘ'_on_join] using hEq
  have hxy :
      (⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x t_x)⟩ :
          {x // x ∈ kGrid (extendAtomFamily F d hd)}) =
        ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y),
          mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y t_y)⟩ :=
    hΘ'_mono.injective hEq'
  simpa using congrArg Subtype.val hxy

lemma ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair
    {δ : ℝ} {r_old_x r_old_y : Multi k} {t_x t_y : ℕ}
    (hδ :
      RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r_old_x r_old_y t_x t_y)
    (hEq :
      ThetaRaw (R := R) (F := F) δ r_old_x t_x =
        ThetaRaw (R := R) (F := F) δ r_old_y t_y) :
    mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x) =
      mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y) := by
  classical
  rcases hδ with ⟨Θ', hΘ'_mono, hx, hy⟩
  -- Evaluate the local Θ' at the two designated points.
  let px :
      {p // p ∈ joinPairSet (F := F) (d := d) (hd := hd) r_old_x r_old_y t_x t_y} :=
    ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x, Or.inl rfl⟩
  let py :
      {p // p ∈ joinPairSet (F := F) (d := d) (hd := hd) r_old_x r_old_y t_x t_y} :=
    ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y, Or.inr rfl⟩
  have hEq' : Θ' px = Θ' py := by
    -- Rewrite both sides to the common `ThetaRaw` value.
    calc
      Θ' px = ThetaRaw (R := R) (F := F) δ r_old_x t_x := by simpa [px] using hx
      _ = ThetaRaw (R := R) (F := F) δ r_old_y t_y := hEq
      _ = Θ' py := by simpa [py] using hy.symm
  have hxy : px = py := hΘ'_mono.injective hEq'
  -- Project back to underlying α-values.
  have : (joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x : {x // x ∈ kGrid (extendAtomFamily F d hd)}) =
      joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y := by
    simpa [px, py] using congrArg Subtype.val hxy
  simpa [joinPoint] using congrArg Subtype.val this

/-!
`AdmissibleDelta` is a deliberately *local* notion: it says δ lies strictly between A- and C-side
statistics at *every* witness level u.

This matches the informal “δ is in the open gap” reading needed for Goertzel’s “invariance inside
the gap” proof outline.

Note: the current `chooseδ` definition in the B-empty branch uses `sSup` of A-statistics, which
does not automatically provide strict inequalities on the C-side. As a result, proving
`AdmissibleDelta (chooseδ …)` from the current Core library is a nontrivial task (and may require
strengthening hypotheses).
-/
def AdmissibleDelta (δ : ℝ) : Prop :=
  (∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetA F d u → separationStatistic R r u hu < δ) ∧
  (∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetC F d u → δ < separationStatistic R r u hu)

/-!
## Ben/Goertzel v2 Lemma 6 interface (base-indexed)

In Ben Goertzel’s v2 notes (and K&S Appendix A.3.4), the “B = ∅” regime is treated *relative to a
fixed base* `X0 := μ(F,r0)` and a fixed level `u`. The relevant constraints compare *old-grid*
values to the “target family” boundary `X0 ⊕ d^u`, and therefore the natural “slope candidates” are
the base-indexed statistics

`(Θ(μ(F,r)) - Θ(μ(F,r0))) / u`.

Lemma 6 asserts that in the base-indexed `B = ∅` case, these constraints carve out a **nonempty
open interval** of admissible slopes.

Rather than baking this into the core construction via `sSup`/`sInf`, we record the existence of
such an interval as an explicit interface. This keeps the dependency clear and avoids forcing a
singleton “global admissibility” notion (which is incompatible with the “interval freedom” reading).
-/

/-- Base-indexed admissibility at a fixed base `r0` and level `u`.

Note: `R` and `d` are explicit parameters in this file’s surrounding `section`, so we keep them
explicit here as well to make elaboration predictable. -/
def AdmissibleDelta_base (R₀ : MultiGridRep F) (d₀ : α)
    (δ : ℝ) (r0 : Multi k) (u : ℕ) (hu : 0 < u) : Prop :=
  (∀ r : Multi k, r ∈ extensionSetA_base F d₀ r0 u →
      separationStatistic_base R₀ r0 r u hu < δ) ∧
  (∀ r : Multi k, r ∈ extensionSetC_base F d₀ r0 u →
      δ < separationStatistic_base R₀ r0 r u hu)

/-- Base-indexed admissibility for *all* levels `u > 0` at a fixed base `r0`.

This matches the quantification in Ben Goertzel’s v2 Lemma 7: once a base `X0 := μ(F,r0)` is
fixed, comparisons against the entire “target family” `X0 ⊕ d^u` for all `u` constrain a single
choice of slope/parameter.

In the current Lean development, this “for all u” admissibility is strong enough to imply the
global (base `ident`) admissibility predicate `AdmissibleDelta`, hence the chosen δ must be the
canonical `chooseδ`. -/
def AdmissibleDelta_base_all (R₀ : MultiGridRep F) (d₀ : α) (δ : ℝ) (r0 : Multi k) : Prop :=
  ∀ u : ℕ, ∀ hu : 0 < u, AdmissibleDelta_base (k := k) (F := F) R₀ d₀ δ r0 u hu

/-- A nonempty open interval of base-indexed admissible deltas.

This is **data** (it carries explicit endpoints `L,U : ℝ`), so it lives in `Type`, not `Prop`. -/
structure AdmissibleInterval_base (R₀ : MultiGridRep F) (d₀ : α)
    (r0 : Multi k) (u : ℕ) (hu : 0 < u) where
  L : ℝ
  U : ℝ
  hLU : L < U
  admissible :
    ∀ δ : ℝ, L < δ → δ < U → AdmissibleDelta_base R₀ d₀ δ r0 u hu

lemma admissibleInterval_base_nonempty
    {r0 : Multi k} {u : ℕ} {hu : 0 < u}
    (hI : AdmissibleInterval_base R d r0 u hu) :
    ∃ δ : ℝ, hI.L < δ ∧ δ < hI.U := by
  classical
  refine ⟨(hI.L + hI.U) / 2, ?_, ?_⟩ <;> linarith [hI.hLU]

/-!
### Existence of a base-indexed admissible interval (Goertzel v2 Lemma 6, fixed `u`)

For a fixed base `r0` and level `u>0`, the “old-grid comparisons against the target family”
`μ(F,r0) ⊕ d^u` only constrain finitely many old-grid points below a fixed bound, so we can pick:
- a **maximal** old-grid point strictly below the boundary (A-side), and
- a **minimal** old-grid point strictly above the boundary (C-side),

and take the corresponding strict inequality window of base-indexed statistics.

This yields an *open interval* of δ choices that separate all base-indexed A and C statistics at
this fixed `u`.
-/

theorem admissibleInterval_base_exists
    (hk : k ≥ 1) (hd' : ident < d) (r0 : Multi k) (u : ℕ) (hu : 0 < u) :
    Nonempty (AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 u hu) := by
  classical
  -- Boundary value in `α` we compare old-grid points against.
  let boundary : α := op (mu F r0) (iterate_op d u)

  -- A-base set is finite under the fixed threshold `boundary`.
  have hA_fin : (extensionSetA_base F d r0 u).Finite := by
    -- `extensionSetA_base` is defined by the strict bound `mu F r < boundary`.
    simpa [extensionSetA_base, boundary] using (finite_set_mu_lt (F := F) boundary)

  -- C-base has a concrete witness `rC0` above the boundary, hence is nonempty.
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  let i₀ : Fin k := ⟨0, hk_pos⟩
  let a₀ : α := F.atoms i₀
  have ha₀ : ident < a₀ := F.pos i₀
  obtain ⟨N, hN⟩ := bounded_by_iterate a₀ ha₀ boundary
  let rC0 : Multi k := unitMulti i₀ N
  have hrC0C : rC0 ∈ extensionSetC_base F d r0 u := by
    -- `boundary < μ(F, rC0) = a₀^N`.
    have : boundary < mu F rC0 := by
      simpa [rC0, a₀, mu_unitMulti] using hN
    simpa [extensionSetC_base, boundary, Set.mem_setOf_eq] using this

  -- Restrict the C-side to a finite “below μ(F,rC0)” set to extract a global minimal C-witness.
  let C_bdd : Set (Multi k) := {r : Multi k | mu F r ≤ mu F rC0}
  have hC_bdd_fin : C_bdd.Finite := by
    simpa [C_bdd] using (finite_set_mu_le (F := F) (mu F rC0))
  let Cset : Set (Multi k) := extensionSetC_base F d r0 u
  let C' : Set (Multi k) := Cset ∩ C_bdd
  have hC'_fin : C'.Finite := hC_bdd_fin.inter_of_right Cset
  have hC'_nonempty : C'.Nonempty := by
    refine ⟨rC0, ?_, le_rfl⟩
    exact hrC0C

  obtain ⟨rC, hrC_min⟩ :=
    Set.Finite.exists_minimalFor (f := fun r : Multi k => mu F r) C' hC'_fin hC'_nonempty
  have hrC_mem : rC ∈ C' := hrC_min.1
  have hrC_Cset : rC ∈ Cset := hrC_mem.1
  have hrC_le_rC0 : mu F rC ≤ mu F rC0 := hrC_mem.2

  -- Extract a maximal A-witness by finiteness (nonempty since `r0 ∈ A_base`).
  have hr0A : r0 ∈ extensionSetA_base F d r0 u := by
    have hdu : ident < iterate_op d u := iterate_op_pos d hd' u hu
    have : mu F r0 < op (mu F r0) (iterate_op d u) := by
      simpa [op_ident_right] using (op_strictMono_right (mu F r0) hdu)
    simpa [extensionSetA_base, boundary, Set.mem_setOf_eq] using this
  have hA_nonempty : (extensionSetA_base F d r0 u).Nonempty := ⟨r0, hr0A⟩
  obtain ⟨rA, hrA_max⟩ :=
    Set.Finite.exists_maximalFor (f := fun r : Multi k => mu F r) (extensionSetA_base F d r0 u)
      hA_fin hA_nonempty
  have hrA_mem : rA ∈ extensionSetA_base F d r0 u := hrA_max.1

  -- Define the interval endpoints from the extremal base-indexed statistics.
  let L : ℝ := separationStatistic_base R r0 rA u hu
  let U : ℝ := separationStatistic_base R r0 rC u hu

  -- Show `L < U` using `μ(F,rA) < boundary < μ(F,rC)`.
  have hμ_rA_lt : mu F rA < boundary := by
    simpa [extensionSetA_base, boundary, Set.mem_setOf_eq] using hrA_mem
  have hμ_rC_gt : boundary < mu F rC := by
    simpa [extensionSetC_base, boundary, Set.mem_setOf_eq] using hrC_Cset
  have hμ_rA_lt_rC : mu F rA < mu F rC := lt_trans hμ_rA_lt hμ_rC_gt
  have hθ_rA_lt_rC :
      R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ <
        R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ := R.strictMono hμ_rA_lt_rC
  have hu_pos_real : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
  have hLU : L < U := by
    -- Divide by `u>0` after subtracting the common base term.
    have :
        (R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) <
          (R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) := by
      have hsub :
          R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ -
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ <
            R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ -
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
        -- Subtracting the same value preserves strict inequality.
        simpa [sub_eq_add_neg] using
          add_lt_add_right hθ_rA_lt_rC (-R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩)
      have hu_inv_pos : 0 < (u : ℝ)⁻¹ := inv_pos.mpr hu_pos_real
      have := mul_lt_mul_of_pos_right hsub hu_inv_pos
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    simpa [L, U, separationStatistic_base] using this

  -- Show `L` is an upper bound for all A-statistics.
  have hA_stat_le_L :
      ∀ r : Multi k, r ∈ extensionSetA_base F d r0 u →
        separationStatistic_base R r0 r u hu ≤ L := by
    intro r hrA
    have hμ_le : mu F r ≤ mu F rA := by
      -- `rA` is maximal for `mu` on the finite A-set.
      rcases le_total (mu F rA) (mu F r) with hle | hge
      · -- If `mu rA ≤ mu r`, maximality gives `mu r ≤ mu rA`.
        exact hrA_max.2 hrA hle
      · exact hge
    have hθ_mono : Monotone R.Θ_grid := R.strictMono.monotone
    have hθ_le :
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ ≤
          R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ := hθ_mono hμ_le
    have :
        (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) ≤
          (R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) := by
      have hsub :
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ ≤
            R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
        -- Subtracting preserves `≤`.
        exact sub_le_sub_right hθ_le _
      have hu_inv_nonneg : 0 ≤ (u : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hu_pos_real)
      have := mul_le_mul_of_nonneg_right hsub hu_inv_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    simpa [L, separationStatistic_base] using this

  -- Show `U` is a lower bound for all C-statistics.
  have hU_le_C_stat :
      ∀ r : Multi k, r ∈ Cset →
        U ≤ separationStatistic_base R r0 r u hu := by
    intro r hrC
    have hμ_le : mu F rC ≤ mu F r := by
      -- Either `mu r ≤ mu rC0` and minimality applies, or `mu rC0 < mu r` and transitivity applies.
      by_cases hle : mu F r ≤ mu F rC0
      · have hrC' : r ∈ C' := ⟨hrC, hle⟩
        -- `rC` is minimal for `mu` on `C'`.
        have : mu F rC ≤ mu F r := by
          -- If `mu r ≤ mu rC`, we'd contradict minimality (swap roles).
          rcases le_total (mu F r) (mu F rC) with hrc | hcr
          · exact hrC_min.2 hrC' hrc
          · exact hcr
        exact this
      · have hgt : mu F rC0 < mu F r := lt_of_not_ge hle
        exact le_trans hrC_le_rC0 (le_of_lt hgt)
    have hθ_mono : Monotone R.Θ_grid := R.strictMono.monotone
    have hθ_le :
        R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ ≤
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := hθ_mono hμ_le
    have :
        (R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) ≤
          (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) := by
      have hsub :
          R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ ≤
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ :=
        sub_le_sub_right hθ_le _
      have hu_inv_nonneg : 0 ≤ (u : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hu_pos_real)
      have := mul_le_mul_of_nonneg_right hsub hu_inv_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    -- Flip sides to get the desired `U ≤ stat r`.
    simpa [U, separationStatistic_base] using this

  refine ⟨{ L := L
            U := U
            hLU := hLU
            admissible := ?_ }⟩
  intro δ hLδ hδU
  refine ⟨?_, ?_⟩
  · intro r hrA
    have hle : separationStatistic_base R r0 r u hu ≤ L := hA_stat_le_L r hrA
    exact lt_of_le_of_lt hle hLδ
  · intro r hrC
    have hle : U ≤ separationStatistic_base R r0 r u hu := hU_le_C_stat r hrC
    exact lt_of_lt_of_le hδU hle

/-- A convenient extraction: for any fixed base `r0` and level `u>0`, there exists at least one
δ satisfying the base-indexed strict A/C inequalities at that level. -/
theorem exists_admissibleDelta_base
    (hk : k ≥ 1) (hd' : ident < d) (r0 : Multi k) (u : ℕ) (hu : 0 < u) :
    ∃ δ : ℝ, AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 u hu := by
  classical
  rcases admissibleInterval_base_exists (hk := hk) (R := R) (d := d) (hd' := hd') r0 u hu with ⟨hI⟩
  rcases admissibleInterval_base_nonempty (R := R) (d := d) (r0 := r0) (u := u) (hu := hu) hI with
    ⟨δ, hLδ, hδU⟩
  exact ⟨δ, hI.admissible δ hLδ hδU⟩

/-!
### Base-indexed accuracy (lifting `accuracy_lemma` by translation)

K&S’s “accuracy” argument (Appendix A.3.4) constructs A/C witnesses with statistics whose gap can
be made arbitrarily small by allowing sufficiently large multiplicities.

The core `accuracy_lemma` in `.../Core/MultiGrid.lean` is phrased in the absolute (`r0 = 0`) form.
Since the k-grid representation is additive on μ-values, translating both witnesses by a fixed base
`r0` preserves the statistics gap, yielding the corresponding base-indexed statement.
-/

/-- Base-indexed analogue of `accuracy_lemma`: for any base `r0`, there exist level-`u` witnesses
on both sides of the boundary `μ(r0) ⊕ d^u` whose base-indexed statistics differ by less than `ε`. -/
theorem accuracy_lemma_base
    (hk : k ≥ 1) (IH : GridBridge F) (H : GridComm F) (hd : ident < d)
    (r0 : Multi k)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (rA : Multi k) (u : ℕ) (hu : 0 < u) (_hrA : rA ∈ extensionSetA_base F d r0 u)
      (rC : Multi k) (_hrC : rC ∈ extensionSetC_base F d r0 u),
      separationStatistic_base R r0 rC u hu - separationStatistic_base R r0 rA u hu < ε := by
  classical
  have hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
    extensionSetA_nonempty_of_B_empty F d hd hB_empty
  have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
    extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
  obtain ⟨rA, uA, huA, hrA, rC, uC, huC, hrC, hgap⟩ :=
    accuracy_lemma (R := R) (d := d) (hd := hd) hB_empty hA_nonempty hC_nonempty ε hε

  -- Scale to a common denominator `u := uA * uC` so both witnesses live at the same level.
  let u : ℕ := uA * uC
  have hu : 0 < u := Nat.mul_pos huA huC
  let rA' : Multi k := scaleMult uC rA
  let rC' : Multi k := scaleMult uA rC
  have hA' : rA' ∈ extensionSetA F d u := by
    have hμA : mu F rA < iterate_op d uA := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hrA
    have h_iter : iterate_op (mu F rA) uC < iterate_op d (uA * uC) := by
      have : iterate_op (mu F rA) (1 * uC) < iterate_op d (uA * uC) :=
        repetition_lemma_lt (mu F rA) d 1 uA uC huC (by simpa [iterate_op_one] using hμA)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult uC rA) = iterate_op (mu F rA) uC := IH.bridge rA uC
    have : mu F rA' < iterate_op d u := by
      simpa [rA', u, hbridge] using h_iter
    simpa [extensionSetA, Set.mem_setOf_eq, rA', u] using this

  have hC' : rC' ∈ extensionSetC F d u := by
    have hμC : iterate_op d uC < mu F rC := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC
    have h_iter : iterate_op d (uC * uA) < iterate_op (mu F rC) uA := by
      have : iterate_op d (uC * uA) < iterate_op (mu F rC) (1 * uA) :=
        repetition_lemma_lt d (mu F rC) uC 1 uA huA (by simpa [iterate_op_one] using hμC)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult uA rC) = iterate_op (mu F rC) uA := IH.bridge rC uA
    have : iterate_op d u < mu F rC' := by
      have : iterate_op d (uC * uA) < mu F (scaleMult uA rC) := by
        simpa [hbridge] using h_iter
      simpa [u, Nat.mul_comm uA uC, rC'] using this
    simpa [extensionSetC, Set.mem_setOf_eq, rC', u] using this

  have hstatA : separationStatistic R rA' u hu = separationStatistic R rA uA huA := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult uC rA), mu_mem_kGrid F _⟩ =
          uC * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ :=
      Theta_scaleMult (R := R) (r := rA) uC
    have huA0 : (uA : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huA)
    have huC0 : (uC : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huC)
    have hcancel :
        (uC : ℝ) * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ /
            ((uA : ℝ) * (uC : ℝ)) =
          R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ / (uA : ℝ) := by
      field_simp [huA0, huC0]
    simpa [separationStatistic, rA', u, hθ, Nat.cast_mul, hcancel]

  have hstatC : separationStatistic R rC' u hu = separationStatistic R rC uC huC := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult uA rC), mu_mem_kGrid F _⟩ =
          uA * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ :=
      Theta_scaleMult (R := R) (r := rC) uA
    have huA0 : (uA : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huA)
    have huC0 : (uC : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huC)
    have hcancel :
        (uA : ℝ) * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ /
            ((uA : ℝ) * (uC : ℝ)) =
          R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ / (uC : ℝ) := by
      field_simp [huA0, huC0]
    simpa [separationStatistic, rC', u, hθ, Nat.cast_mul, hcancel]

  have hgap' :
      separationStatistic R rC' u hu - separationStatistic R rA' u hu < ε := by
    -- Rewrite the original gap inequality through the scaled statistics.
    simpa [hstatA, hstatC] using hgap

  have hrA_base : (r0 + rA') ∈ extensionSetA_base F d r0 u := by
    have hμA : mu F rA' < iterate_op d u := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hA'
    have hμadd : mu F (r0 + rA') = op (mu F r0) (mu F rA') := by
      simpa using (mu_add_of_comm (F := F) H r0 rA')
    have h :
        op (mu F r0) (mu F rA') < op (mu F r0) (iterate_op d u) :=
      op_strictMono_right (mu F r0) hμA
    have : mu F (r0 + rA') < op (mu F r0) (iterate_op d u) :=
      lt_of_eq_of_lt hμadd h
    simpa [extensionSetA_base, Set.mem_setOf_eq] using this

  have hrC_base : (r0 + rC') ∈ extensionSetC_base F d r0 u := by
    have hμC : iterate_op d u < mu F rC' := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hC'
    have hμadd : mu F (r0 + rC') = op (mu F r0) (mu F rC') := by
      simpa using (mu_add_of_comm (F := F) H r0 rC')
    have h :
        op (mu F r0) (iterate_op d u) < op (mu F r0) (mu F rC') :=
      op_strictMono_right (mu F r0) hμC
    have : op (mu F r0) (iterate_op d u) < mu F (r0 + rC') :=
      lt_of_lt_of_eq h hμadd.symm
    simpa [extensionSetC_base, Set.mem_setOf_eq] using this

  have hstatA :
      separationStatistic_base R r0 (r0 + rA') u hu = separationStatistic R rA' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rA'), mu_mem_kGrid F (r0 + rA')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rA', mu_mem_kGrid F rA'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rA')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  have hstatC :
      separationStatistic_base R r0 (r0 + rC') u hu = separationStatistic R rC' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rC'), mu_mem_kGrid F (r0 + rC')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rC', mu_mem_kGrid F rC'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rC')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  refine ⟨r0 + rA', u, hu, hrA_base, r0 + rC', hrC_base, ?_⟩
  simpa [hstatA, hstatC] using hgap'

/-- Base-indexed cut tightness at a common denominator: translating the absolute `δ`-approximants
from `delta_cut_tight_common_den` preserves statistics gaps. -/
theorem delta_cut_tight_common_den_base
    (hk : k ≥ 1) (IH : GridBridge F) (H : GridComm F) (hd : ident < d)
    (r0 : Multi k)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : ℕ) (hu : 0 < u) (rA rC : Multi k),
      rA ∈ extensionSetA_base F d r0 u ∧ rC ∈ extensionSetC_base F d r0 u ∧
      |separationStatistic_base R r0 rC u hu - chooseδ hk R d hd| < ε ∧
      |chooseδ hk R d hd - separationStatistic_base R r0 rA u hu| < ε := by
  classical
  obtain ⟨u, hu, rA', rC', hrA', hrC', hC_close, hA_close⟩ :=
    delta_cut_tight_common_den (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
      (hB_empty := hB_empty) ε hε

  have hrA_base : (r0 + rA') ∈ extensionSetA_base F d r0 u := by
    have hμA : mu F rA' < iterate_op d u := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hrA'
    have hμadd : mu F (r0 + rA') = op (mu F r0) (mu F rA') := by
      simpa using (mu_add_of_comm (F := F) H r0 rA')
    have h :
        op (mu F r0) (mu F rA') < op (mu F r0) (iterate_op d u) :=
      op_strictMono_right (mu F r0) hμA
    have : mu F (r0 + rA') < op (mu F r0) (iterate_op d u) :=
      lt_of_eq_of_lt hμadd h
    simpa [extensionSetA_base, Set.mem_setOf_eq] using this

  have hrC_base : (r0 + rC') ∈ extensionSetC_base F d r0 u := by
    have hμC : iterate_op d u < mu F rC' := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC'
    have hμadd : mu F (r0 + rC') = op (mu F r0) (mu F rC') := by
      simpa using (mu_add_of_comm (F := F) H r0 rC')
    have h :
        op (mu F r0) (iterate_op d u) < op (mu F r0) (mu F rC') :=
      op_strictMono_right (mu F r0) hμC
    have : op (mu F r0) (iterate_op d u) < mu F (r0 + rC') :=
      lt_of_lt_of_eq h hμadd.symm
    simpa [extensionSetC_base, Set.mem_setOf_eq] using this

  have hstatA :
      separationStatistic_base R r0 (r0 + rA') u hu = separationStatistic R rA' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rA'), mu_mem_kGrid F (r0 + rA')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rA', mu_mem_kGrid F rA'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rA')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  have hstatC :
      separationStatistic_base R r0 (r0 + rC') u hu = separationStatistic R rC' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rC'), mu_mem_kGrid F (r0 + rC')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rC', mu_mem_kGrid F rC'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rC')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  refine ⟨u, hu, r0 + rA', r0 + rC', hrA_base, hrC_base, ?_, ?_⟩
  · simpa [hstatC] using hC_close
  · simpa [hstatA] using hA_close

/-!
### Local realizability from base-indexed admissibility (Ben/Goertzel v2 helper)

Ben’s Lemma 7 (“order-invariance inside an admissible gap”) needs an intermediate hypothesis:
for each δ in an admissible interval, there is a strictly monotone evaluator on the *relevant*
join-multiplicity points that agrees with the affine `ThetaRaw` formula.

In this file, the minimal such hypothesis is `RealizesThetaRaw_pair`, which lives only on the
two-point slice `{joinPoint r0 u, joinPoint ry v}`.

The lemma below shows how to build this local realization from a base-indexed admissibility
assumption at the *difference level* `u - v` (together with “no base-indexed B-witness” to rule
out the degenerate equality case).
-/

lemma realizesThetaRaw_pair_of_admissibleDelta_base
    {δ : ℝ} (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hδ :
      AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v)) :
    RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v := by
  classical
  -- Name the two designated points in the extended grid.
  let pL := joinPoint (F := F) (d := d) (hd := hd) r0 u
  let pR := joinPoint (F := F) (d := d) (hd := hd) ry v

  have pR_ne_pL : (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}) ≠ pL := by
    intro hEq
    -- Equality of join-points yields a base-indexed B-witness at level (u - v).
    have huv_le : v ≤ u := le_of_lt huv
    have hμEq :
        mu (extendAtomFamily F d hd) (joinMulti r0 u) =
          mu (extendAtomFamily F d hd) (joinMulti ry v) := by
      -- `joinPoint` is the underlying `mu`-value packaged as a grid element.
      simpa [pL, pR, joinPoint] using (congrArg Subtype.val hEq).symm
    have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
      extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd r0 ry u v huv_le hμEq
    exact hB_base ⟨ry, hB⟩

  -- Define the evaluator by case-splitting on which of the two points we have.
  refine
    ⟨fun p =>
        if p.1 = pL then ThetaRaw (R := R) (F := F) δ r0 u
        else ThetaRaw (R := R) (F := F) δ ry v,
      ?_, ?_, ?_⟩

  · -- StrictMono on the two-point slice.
    intro a b hab
    have hab' :
        (a : {x // x ∈ kGrid (extendAtomFamily F d hd)}) <
          (b : {x // x ∈ kGrid (extendAtomFamily F d hd)}) := hab
    -- Reduce to cases for the underlying points.
    rcases a.property with ha | ha <;> rcases b.property with hb | hb
    · -- a.val = pL, b.val = pL: impossible
      have hab'' : pL < pL := by
        simpa [ha, hb] using hab'
      exact (lt_irrefl _ hab'').elim
    · -- a.val = pL, b.val = pR
        -- Determine which base-indexed side `ry` lies on, by cancelling the common `d^v` tail.
        have hμ : (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}) <
            (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}) := by
          simpa [ha, hb] using hab'
        have hμL :
            (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
              op (mu F r0) (iterate_op d u) := by
          simpa [pL, joinPoint] using (mu_extend_last F d hd r0 u)
        have hμR :
            (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
              op (mu F ry) (iterate_op d v) := by
          simpa [pR, joinPoint] using (mu_extend_last F d hd ry v)
        have hsplt : iterate_op d u = op (iterate_op d (u - v)) (iterate_op d v) := by
          have huv_le : v ≤ u := le_of_lt huv
          have huv_eq : u - v + v = u := Nat.sub_add_cancel huv_le
          have h :
              iterate_op d (u - v + v) = op (iterate_op d (u - v)) (iterate_op d v) :=
            (iterate_op_add d (u - v) v).symm
          -- `h` is `iterate_op d (u - v + v) = ...`; rewrite the LHS to `iterate_op d u`.
          simpa [huv_eq] using h
        have hμ' :
            op (op (mu F r0) (iterate_op d (u - v))) (iterate_op d v) <
              op (mu F ry) (iterate_op d v) := by
          have : op (mu F r0) (iterate_op d u) < op (mu F ry) (iterate_op d v) := by
            simpa [hμL, hμR] using (show (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 <
              (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 from hμ)
          simpa [hsplt, op_assoc] using this
        have hmono : Monotone (fun z : α => op z (iterate_op d v)) :=
          (op_strictMono_left (iterate_op d v)).monotone
        have h_base_lt : op (mu F r0) (iterate_op d (u - v)) < mu F ry :=
          hmono.reflect_lt hμ'
        have hryC : ry ∈ extensionSetC_base F d r0 (u - v) := by
          simpa [extensionSetC_base, Set.mem_setOf_eq] using h_base_lt
        have hstat : δ < separationStatistic_base R r0 ry (u - v) (Nat.sub_pos_of_lt huv) :=
          (hδ.2 ry hryC)
        -- Convert δ < statistic into a ΘRaw inequality.
        have hu_pos_real : (0 : ℝ) < (u - v : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt huv)
        have hgap :
            δ * ((u : ℝ) - (v : ℝ)) <
              R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ -
                R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
          have h :=
            (lt_div_iff₀ hu_pos_real).1 (by simpa [separationStatistic_base] using hstat)
          have huv_le : v ≤ u := le_of_lt huv
          -- Rewrite the casted subtraction as a difference of casts.
          have h' :
              δ * ((u : ℝ) - (v : ℝ)) <
                R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ -
                  R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
            simpa [Nat.cast_sub huv_le, mul_assoc, mul_left_comm, mul_comm] using h
          exact h'
        have huv_cast : (u : ℝ) = (v : ℝ) + (u - v : ℕ) := by
          have : u = v + (u - v) := by omega
          simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ)) this
        have hΘraw : ThetaRaw (R := R) (F := F) δ r0 u < ThetaRaw (R := R) (F := F) δ ry v := by
          -- Θ(r0)+uδ = Θ(r0)+vδ+(u-v)δ < Θ(ry)+vδ
          have : R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ <
              R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ := by
            calc
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ
                  = R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + ((v : ℝ) + (u - v : ℕ)) * δ := by
                      simp [huv_cast]
              _ = R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (v : ℝ) * δ + δ * ((u : ℝ) - (v : ℝ)) := by
                      -- Expand `(v + (u-v)) * δ` and rewrite the casted subtraction as `u - v`.
                      have huv_le : v ≤ u := le_of_lt huv
                      -- `((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ)`
                      have hsub : ((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ) := by
                        simpa using (Nat.cast_sub huv_le : ((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ))
                      -- Distribute and commute into the target shape.
                      -- `ring_nf` is robust once casts are normalized.
                      -- (The goal is pure ℝ arithmetic.)
                      -- First rewrite the casted subtraction, then normalize.
                      simp [hsub]
                      ring_nf
              _ < R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ := by
                      linarith [hgap]
              _ = R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ := rfl
          simpa [ThetaRaw, add_comm, add_left_comm, add_assoc] using this
        -- Finish this StrictMono case.
        -- `pL` picks the left branch; `pR` picks the right branch using `pR_ne_pL`.
        simpa [ha, hb, pL, pR, pR_ne_pL] using hΘraw
    · -- a.val = pR, b.val = pL
      -- Cancel the common tail as above, but in the opposite direction.
      have hμ : (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}) <
          (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}) := by
        simpa [ha, hb] using hab'
      have hμL :
          (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
            op (mu F r0) (iterate_op d u) := by
        simpa [pL, joinPoint] using (mu_extend_last F d hd r0 u)
      have hμR :
          (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
            op (mu F ry) (iterate_op d v) := by
        simpa [pR, joinPoint] using (mu_extend_last F d hd ry v)
      have hsplt : iterate_op d u = op (iterate_op d (u - v)) (iterate_op d v) := by
        have huv_le : v ≤ u := le_of_lt huv
        have huv_eq : u - v + v = u := Nat.sub_add_cancel huv_le
        have h :
            iterate_op d (u - v + v) = op (iterate_op d (u - v)) (iterate_op d v) :=
          (iterate_op_add d (u - v) v).symm
        simpa [huv_eq] using h
      have hμ' :
          op (mu F ry) (iterate_op d v) <
            op (op (mu F r0) (iterate_op d (u - v))) (iterate_op d v) := by
        have : op (mu F ry) (iterate_op d v) < op (mu F r0) (iterate_op d u) := by
          simpa [hμL, hμR] using (show (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 <
            (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 from hμ)
        simpa [hsplt, op_assoc] using this
      have h_base_lt : mu F ry < op (mu F r0) (iterate_op d (u - v)) :=
        (by
          have hmono : Monotone (fun z : α => op z (iterate_op d v)) :=
            (op_strictMono_left (iterate_op d v)).monotone
          exact hmono.reflect_lt hμ')
      have hryA : ry ∈ extensionSetA_base F d r0 (u - v) := by
        simpa [extensionSetA_base, Set.mem_setOf_eq] using h_base_lt
      have hstat : separationStatistic_base R r0 ry (u - v) (Nat.sub_pos_of_lt huv) < δ :=
        (hδ.1 ry hryA)
      have hu_pos_real : (0 : ℝ) < (u - v : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt huv)
      have hgap :
          R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ < δ * ((u : ℝ) - (v : ℝ)) := by
        have h :=
          (div_lt_iff₀ hu_pos_real).1 (by simpa [separationStatistic_base] using hstat)
        have huv_le : v ≤ u := le_of_lt huv
        simpa [Nat.cast_sub huv_le, mul_comm, mul_left_comm, mul_assoc] using h
      have huv_cast : (u : ℝ) = (v : ℝ) + (u - v : ℕ) := by
        have : u = v + (u - v) := by omega
        simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ)) this
      have hΘraw :
          ThetaRaw (R := R) (F := F) δ ry v < ThetaRaw (R := R) (F := F) δ r0 u := by
        have : R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ <
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ := by
          -- Θ(ry) - Θ(r0) < (u-v)δ
          have : R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ <
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + δ * ((u : ℝ) - (v : ℝ)) := by
            linarith [hgap]
          calc
            R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ
                < (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + δ * ((u : ℝ) - (v : ℝ))) + (v : ℝ) * δ := by
                    linarith
            _ = R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ := by
                  simp [huv_cast]; ring_nf
        simpa [ThetaRaw, add_comm, add_left_comm, add_assoc] using this
      -- Rewrite evaluator values at the two points.
      simpa [ha, hb, pL, pR, pR_ne_pL] using hΘraw
    · -- a.val = pR, b.val = pR: impossible
      have hab'' : pR < pR := by
        simpa [ha, hb] using hab'
      exact (lt_irrefl _ hab'').elim
  · -- left point equation
    simp [pL, joinPoint]
  · -- right point equation
    -- Keep `joinPoint` folded so the `if_neg pR_ne_pL` rewrite can fire.
    simp [pR, pL, pR_ne_pL]

/-!
### Base-indexed “interval freedom” cannot be global in this development

Ben/Goertzel v2 Lemma 6 is phrased as an “open interval of admissible slopes” in the (base-indexed)
`B = ∅` case.  In the current Lean development, the cut-tightness lemma `delta_cut_tight` (proved
from K&S’s repetition/accuracy arguments) makes the *global* admissibility predicate rigid: there
can be at most one δ satisfying *all* A/C constraints simultaneously.

The lemma below makes a related point for the base-indexed, all-levels predicate
`AdmissibleDelta_base_all`: if some δ works for *all* levels `u` relative to a base `r0`, then δ is
already globally admissible (relative to `ident`), hence δ must equal `chooseδ`.

This does not rule out “interval freedom” for *finite* sets of constraints (or for a fixed `u`);
it only rules out a nontrivial open interval of δ’s satisfying *all* constraints at once.
-/

lemma admissibleDelta_base_all_implies_admissibleDelta
    (H : GridComm F) (r0 : Multi k) {δ : ℝ}
    (hδ : AdmissibleDelta_base_all (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0) :
    AdmissibleDelta (R := R) (F := F) (d := d) δ := by
  classical
  refine ⟨?_, ?_⟩
  · intro r u hu hrA
    -- Translate an absolute A-witness by the base `r0`.
    have hrA_base : (r0 + r) ∈ extensionSetA_base F d r0 u := by
      have hμr : mu F r < iterate_op d u := by
        simpa [extensionSetA, Set.mem_setOf_eq] using hrA
      have hμadd : mu F (r0 + r) = op (mu F r0) (mu F r) := by
        simpa using (mu_add_of_comm (H := H) r0 r)
      have : mu F (r0 + r) < op (mu F r0) (iterate_op d u) := by
        -- Strict monotone translation on the right.
        simpa [hμadd] using (op_strictMono_right (mu F r0) hμr)
      simpa [extensionSetA_base, Set.mem_setOf_eq] using this
    have hstat_base_lt : separationStatistic_base R r0 (r0 + r) u hu < δ :=
      (hδ u hu).1 (r0 + r) hrA_base
    -- Cancel the common Θ(r0) using additivity.
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + r), mu_mem_kGrid F (r0 + r)⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 r)
    have hstat_eq :
        separationStatistic_base R r0 (r0 + r) u hu = separationStatistic R r u hu := by
      -- (Θ(r0+r) - Θ(r0))/u = Θ(r)/u by additivity
      simp [separationStatistic_base, separationStatistic, hθ_add]
    simpa [hstat_eq] using hstat_base_lt
  · intro r u hu hrC
    have hrC_base : (r0 + r) ∈ extensionSetC_base F d r0 u := by
      have hμr : iterate_op d u < mu F r := by
        simpa [extensionSetC, Set.mem_setOf_eq] using hrC
      have hμadd : mu F (r0 + r) = op (mu F r0) (mu F r) := by
        simpa using (mu_add_of_comm (H := H) r0 r)
      have : op (mu F r0) (iterate_op d u) < mu F (r0 + r) := by
        simpa [hμadd] using (op_strictMono_right (mu F r0) hμr)
      simpa [extensionSetC_base, Set.mem_setOf_eq] using this
    have hstat_base_gt : δ < separationStatistic_base R r0 (r0 + r) u hu :=
      (hδ u hu).2 (r0 + r) hrC_base
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + r), mu_mem_kGrid F (r0 + r)⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 r)
    have hstat_eq :
        separationStatistic_base R r0 (r0 + r) u hu = separationStatistic R r u hu := by
      simp [separationStatistic_base, separationStatistic, hθ_add]
    simpa [hstat_eq] using hstat_base_gt

/-!
### Uniqueness of an admissible δ (global, absolute A/B/C)

Ben/Goertzel v2 (Lemma 6) informally speaks of an *open interval* of admissible “slopes” in the
`B = ∅` regime. In the current Lean formalization, an “admissible δ” for a fixed `(F,d)` is the
predicate `AdmissibleDelta` above: δ lies strictly between *all* A- and C-side statistics for
every `u > 0`.

Under the existing `delta_cut_tight` lemma (K&S “accuracy”/Dedekind-cut tightness), this *global*
notion of admissibility is rigid: there can be **at most one** such δ, namely `chooseδ`.

This does not refute K&S Appendix A; it clarifies that any “interval of freedom” must come from a
weaker (e.g. finite‑constraint and/or base‑indexed) admissibility notion than `AdmissibleDelta`.
-/

lemma admissibleDelta_eq_chooseδ
    (IH : GridBridge F) (H : GridComm F)
    (hB_empty : ∀ (r : Multi k) (u : ℕ), 0 < u → r ∉ extensionSetB F d u)
    {δ : ℝ} (hδ : AdmissibleDelta (R := R) (F := F) (d := d) δ) :
    δ = chooseδ hk R d hd := by
  classical
  set δ₀ : ℝ := chooseδ hk R d hd
  by_contra hne
  have hε : 0 < |δ - δ₀| / 2 := by
    have : 0 < |δ - δ₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  obtain ⟨rA, uA, rC, uC, huA, huC, hrA, hrC, hC_close, hA_close⟩ :=
    delta_cut_tight (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
      (hB_empty := hB_empty) (ε := |δ - δ₀| / 2) hε
  have hA_bound : separationStatistic R rA uA huA ≤ δ₀ :=
    by simpa [δ₀] using chooseδ_A_bound hk R IH H d hd rA uA huA hrA
  have hC_bound : δ₀ ≤ separationStatistic R rC uC huC :=
    by simpa [δ₀] using chooseδ_C_bound hk R IH H d hd rC uC huC hrC
  have hA_lt : separationStatistic R rA uA huA < δ := hδ.1 rA uA huA hrA
  have hC_gt : δ < separationStatistic R rC uC huC := hδ.2 rC uC huC hrC
  have hδ₀_minus : δ₀ - (|δ - δ₀| / 2) < δ := by
    -- From `|δ₀ - statA| < ε` and `statA ≤ δ₀`, get `δ₀ - ε < statA < δ`.
    have hpos : 0 ≤ δ₀ - separationStatistic R rA uA huA := by linarith [hA_bound]
    have hδ₀_lt : δ₀ - separationStatistic R rA uA huA < |δ - δ₀| / 2 := by
      -- `|δ₀ - statA| < ε` and `δ₀ ≥ statA` ⇒ `δ₀ - statA < ε`.
      simpa [abs_of_nonneg hpos, δ₀] using hA_close
    have : δ₀ - (|δ - δ₀| / 2) < separationStatistic R rA uA huA := by linarith
    exact lt_trans this hA_lt
  have hδ₀_plus : δ < δ₀ + (|δ - δ₀| / 2) := by
    -- From `|statC - δ₀| < ε` and `δ₀ ≤ statC`, get `δ < statC < δ₀ + ε`.
    have hpos : 0 ≤ separationStatistic R rC uC huC - δ₀ := by linarith [hC_bound]
    have hδ₀_lt : separationStatistic R rC uC huC - δ₀ < |δ - δ₀| / 2 := by
      simpa [abs_of_nonneg hpos, δ₀] using hC_close
    have hC_lt : separationStatistic R rC uC huC < δ₀ + (|δ - δ₀| / 2) := by linarith
    exact lt_trans hC_gt hC_lt
  -- Now δ lies strictly inside the interval (δ₀ - ε, δ₀ + ε), contradicting ε = |δ-δ₀|/2.
  have habs : |δ - δ₀| < |δ - δ₀| / 2 := by
    have h1 : -( |δ - δ₀| / 2) < δ - δ₀ := by linarith [hδ₀_minus]
    have h2 : δ - δ₀ < (|δ - δ₀| / 2) := by linarith [hδ₀_plus]
    simpa [abs_lt] using And.intro h1 h2
  linarith

lemma admissibleDelta_base_all_eq_chooseδ
    (IH : GridBridge F) (H : GridComm F)
    (hB_empty : ∀ (r : Multi k) (u : ℕ), 0 < u → r ∉ extensionSetB F d u)
    (r0 : Multi k) {δ : ℝ}
    (hδ : AdmissibleDelta_base_all (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0) :
    δ = chooseδ hk R d hd :=
  admissibleDelta_eq_chooseδ (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
    (hB_empty := hB_empty) (δ := δ)
    (admissibleDelta_base_all_implies_admissibleDelta (R := R) (F := F) (d := d) (H := H) r0 hδ)

/-!
### A concrete “false lead” that can be ruled out

Ben/Goertzel v2 Lemma 6 speaks of an *open interval* of admissible “slopes” in the `B = ∅` case.
For the **global** admissibility notion `AdmissibleDelta` (which quantifies over *all* A/C witnesses
at every level), this cannot happen: under `delta_cut_tight`, any globally admissible δ is forced to
equal `chooseδ`, so there is at most one such δ.

This does not refute the v2 strategy: it clarifies that any “interval of freedom” must be a weaker,
more local admissibility notion (e.g. finite-constraint and/or base-indexed), not `AdmissibleDelta`.
-/

theorem no_open_interval_of_global_admissibleDelta
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ (r : Multi k) (u : ℕ), 0 < u → r ∉ extensionSetB F d u) :
    ¬ ∃ L U : ℝ, L < U ∧
        ∀ δ : ℝ, L < δ → δ < U → AdmissibleDelta (R := R) (F := F) (d := d) δ := by
  classical
  intro h
  rcases h with ⟨L, U, hLU, hAdm⟩
  -- Pick two distinct points in the open interval.
  set δ₁ : ℝ := (L + U) / 2
  set δ₂ : ℝ := (L + δ₁) / 2
  have hδ₁_in : L < δ₁ ∧ δ₁ < U := by
    have h1 : L < (L + U) / 2 := by linarith [hLU]
    have h2 : (L + U) / 2 < U := by linarith [hLU]
    simpa [δ₁] using And.intro h1 h2
  have hδ₂_in : L < δ₂ ∧ δ₂ < U := by
    have hLδ₁ : L < δ₁ := hδ₁_in.1
    have hδ₁U : δ₁ < U := hδ₁_in.2
    have h1 : L < (L + δ₁) / 2 := by linarith [hLδ₁]
    have h2 : (L + δ₁) / 2 < U := by linarith [hδ₁U]
    simpa [δ₂] using And.intro h1 h2
  have hδ₁ : AdmissibleDelta (R := R) (F := F) (d := d) δ₁ := hAdm δ₁ hδ₁_in.1 hδ₁_in.2
  have hδ₂ : AdmissibleDelta (R := R) (F := F) (d := d) δ₂ := hAdm δ₂ hδ₂_in.1 hδ₂_in.2
  -- Global admissibility is rigid: both must equal chooseδ.
  have hEq₁ :
      δ₁ = chooseδ hk R d hd :=
    admissibleDelta_eq_chooseδ (hk := hk) (R := R) (F := F) (d := d) (hd := hd)
      (IH := IH) (H := H) (hB_empty := hB_empty) hδ₁
  have hEq₂ :
      δ₂ = chooseδ hk R d hd :=
    admissibleDelta_eq_chooseδ (hk := hk) (R := R) (F := F) (d := d) (hd := hd)
      (IH := IH) (H := H) (hB_empty := hB_empty) hδ₂
  -- But δ₂ < δ₁ by construction.
  have hδ₂_lt_δ₁ : δ₂ < δ₁ := by
    have : (L + δ₁) / 2 < δ₁ := by linarith [hδ₁_in.1]
    simpa [δ₂] using this
  -- Contradiction: δ₂ < δ₁ but both equal chooseδ.
  have hcontra' : chooseδ hk R d hd < chooseδ hk R d hd := by
    have h' : δ₂ < δ₁ := hδ₂_lt_δ₁
    -- Replace δ₂ and δ₁ by `chooseδ` using the two rigidity equalities.
    rw [hEq₂, hEq₁] at h'
    exact h'
  exact lt_irrefl _ hcontra'

/-!
Goertzel Lemma 7 (invariance inside the admissible gap), specialized to the current
`ThetaRaw` expression family: if two admissible δ choices are both valid, then the sign of the
difference between two “new expressions” is invariant.

This is *exactly* the qualitative ingredient needed to rule out boundary equalities in the B-empty
strict-gap lemmas: if a boundary equality held for δ, then small admissible perturbations of δ
would flip the inequality, contradicting invariance.
-/
class GoertzelInvarianceSpec : Prop where
  invariant :
    ∀ {δ₁ δ₂ : ℝ},
      AdmissibleDelta (R := R) (F := F) (d := d) δ₁ →
      AdmissibleDelta (R := R) (F := F) (d := d) δ₂ →
      ∀ (r_old_x r_old_y : Multi k) (t_x t_y : ℕ),
        (ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x < ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y) ↔
        (ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x < ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y)

end

/-!
## Base-indexed A/B/C sets (as in K&S A.3.4 and Goertzel v2)

One recurring source of confusion is the meaning of “B is empty”.

In the Appendix-A *extension step*, K&S define A/B/C **relative to a fixed base old-grid element**
`X0` (their `µ(r0,…,t0)`), by comparing *old-grid values* to the “new family” value
`X0 ⊕ d^u`. In that base-indexed sense:
- `B` consists of old-grid values that land *exactly on* `X0 ⊕ d^u` for some `u>0`.

This is **not** the same as the absolute set
`extensionSetB F d u := {r | mu F r = d^u}` used in parts of the current codebase
(which corresponds to the special base `X0 = ident`).

Ben/Goertzel Lemma 7’s cancellation step produces an equality of the form `X0 ⊕ d^w = Y`
with `Y` an old-grid value; this is a *base-indexed* B-witness for base `X0`, but it need not
produce an absolute witness `mu F r = d^w`.

The counterexample `.../AppendixA/Counterexamples/GoertzelLemma7.lean` demonstrates this mismatch
in a concrete additive model: global “absolute B-empty” can hold while there exist old-grid
values `X0, Y` with `X0 ⊕ d = Y`.
-/

section BaseIndexed

variable {k : ℕ} {F : AtomFamily α k}

open scoped BigOperators

noncomputable def baseTarget (r0 : Multi k) (d : α) (u : ℕ) : α :=
  op (mu F r0) (iterate_op d u)

def baseSetA (r0 : Multi k) (d : α) (u : ℕ) : Set (Multi k) :=
  extensionSetA_base F d r0 u

def baseSetB (r0 : Multi k) (d : α) (u : ℕ) : Set (Multi k) :=
  extensionSetB_base F d r0 u

def baseSetC (r0 : Multi k) (d : α) (u : ℕ) : Set (Multi k) :=
  extensionSetC_base F d r0 u

lemma mem_baseSetB_iff
    (r0 r : Multi k) (d : α) (u : ℕ) :
    r ∈ baseSetB (F := F) r0 d u ↔ mu F r = op (mu F r0) (iterate_op d u) := by
  rfl

lemma baseSetB_witness_of_eq
    (r0 r : Multi k) (d : α) (u : ℕ)
    (h : mu F r = op (mu F r0) (iterate_op d u)) :
    r ∈ baseSetB (F := F) r0 d u := by
  exact h

lemma baseIndexed_cancel_eq
    (r0 ry : Multi k) (d : α) (u v : ℕ) (huv : v ≤ u)
    (hEq :
      op (mu F r0) (iterate_op d u) =
        op (mu F ry) (iterate_op d v)) :
    mu F ry = op (mu F r0) (iterate_op d (u - v)) := by
  simpa using cancel_right_iterate_eq (F := F) (d := d) r0 ry u v huv hEq

end BaseIndexed

/-!
## Algebraic core of Goertzel Lemma 7 (affine “flip ⇒ equality”)

In the refactored codebase, the would-be extended evaluator on join-multiplicity witnesses is

`ThetaRaw δ r_old t = Θ(old) + t·δ`.

For fixed `(r_old_x,t_x)` and `(r_old_y,t_y)`, the difference is affine in `δ`.  Therefore, if
the strict inequality flips between two parameters `δ₁ < δ₂`, then there is an explicit “critical
value” `δ₀` where equality holds.  This step is *pure algebra* (no topology, no IVT).

Turning that equality into a contradiction in the B-empty case requires an *additional* link
between “numeric equality” and “algebraic equality” (injectivity of the extension map), which is
exactly where circularity can enter.
-/

section
variable {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)

lemma ThetaRaw_sub
    (δ : ℝ) (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) :
    ThetaRaw (R := R) (F := F) δ r_old_x t_x - ThetaRaw (R := R) (F := F) δ r_old_y t_y =
      (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) +
        ((t_x : ℝ) - (t_y : ℝ)) * δ := by
  simp [ThetaRaw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, mul_comm]

theorem ThetaRaw_flip_implies_eq_between
    {δ₁ δ₂ : ℝ} (_hδ : δ₁ < δ₂)
    (r_old_x r_old_y : Multi k) (t_x t_y : ℕ)
    (ht : t_y < t_x)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x <
          ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y <
          ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x) :
    ∃ δ₀ : ℝ, δ₁ < δ₀ ∧ δ₀ < δ₂ ∧
      ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x =
        ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y := by
  classical
  set a : ℝ :=
    (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) with ha
  set b : ℝ := (t_x : ℝ) - (t_y : ℝ) with hb
  have hb_pos : 0 < b := by
    have : (t_y : ℝ) < (t_x : ℝ) := by exact_mod_cast ht
    simpa [b] using sub_pos.mpr this
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  set δ₀ : ℝ := (-a) / b with hδ₀
  refine ⟨δ₀, ?_, ?_, ?_⟩
  · -- δ₁ < δ₀ from `a + b*δ₁ < 0`
    have hdiff₁ : a + b * δ₁ < 0 := by
      have : ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x -
            ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y < 0 := sub_neg.mpr h1
      simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm] using this
    have hmul : δ₁ * b < -a := by
      have : b * δ₁ < -a := by linarith [hdiff₁]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : δ₁ < (-a) / b := (lt_div_iff₀ hb_pos).2 hmul
    simpa [hδ₀] using this
  · -- δ₀ < δ₂ from `0 < a + b*δ₂`
    have hdiff₂ : 0 < a + b * δ₂ := by
      have : 0 < ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x -
            ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y := sub_pos.mpr h2
      simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm] using this
    have hmul : -a < δ₂ * b := by
      have : -a < b * δ₂ := by linarith [hdiff₂]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : (-a) / b < δ₂ := (div_lt_iff₀ hb_pos).2 hmul
    simpa [hδ₀] using this
  · -- equality at δ₀
    have hdiff0 : ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x -
          ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y = 0 := by
      have hab : a + b * δ₀ = 0 := by
        have hb_mul : b * ((-a) / b) = -a := by
          field_simp [hb_ne]
        have : a + b * ((-a) / b) = 0 := by linarith [hb_mul]
        simpa [δ₀, hδ₀] using this
      have hdiff :
          ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x -
              ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y = a + b * δ₀ := by
        simp [ThetaRaw_sub (R := R) (F := F), a, b]
      simp [hdiff, hab]
    exact sub_eq_zero.mp hdiff0

end

section BenV2

variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d)

/-! Ben/Goertzel v2 Lemma 7, extracted as a *conditional* Lean lemma:

If a comparison between two `ThetaRaw` expressions flips between `δ₁ < δ₂`, then there is an
intermediate `δ₀` with equality (pure affine algebra). If every intermediate `δ` realizes the
`ThetaRaw` formula via a strictly monotone evaluator on the extended μ-grid, then that numeric
equality forces an *algebraic* equality on the extended grid, hence a **base-indexed B-witness**
by right-cancellation. -/
/-- Pair-realization version of Ben/Goertzel v2 Lemma 7.

This is strictly weaker than `flip_implies_baseIndexed_B_witness`: it only assumes realizability
of `ThetaRaw` on the **specific two join-multiplicity points** involved in the flip. -/
lemma flip_implies_baseIndexed_B_witness_pair
    {δ₁ δ₂ : ℝ} (hδ : δ₁ < δ₂)
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hRealize :
      ∀ δ, δ₁ < δ → δ < δ₂ →
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u) :
    ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v) := by
  classical
  have huv_le : v ≤ u := le_of_lt huv
  obtain ⟨δ₀, hδ₁, hδ₂, hEq⟩ :=
    ThetaRaw_flip_implies_eq_between (R := R) (F := F) (δ₁ := δ₁) (δ₂ := δ₂) hδ
      r0 ry u v huv h1 h2
  have hμEq :
      mu (extendAtomFamily F d hd) (joinMulti r0 u) =
        mu (extendAtomFamily F d hd) (joinMulti ry v) :=
    ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd)
      (hδ := hRealize δ₀ hδ₁ hδ₂) hEq
  have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
    extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd r0 ry u v huv_le hμEq
  exact ⟨ry, hB⟩

/-!
### Ben/Goertzel v2 Lemma 7 “wiring” (from admissible intervals)

The flip lemma above is purely algebraic: it turns a sign flip into an intermediate equality, and
then requires `RealizesThetaRaw_pair` on that intermediate point to convert a `ThetaRaw`-equality
into an equality of the corresponding μ-values.

The helper `realizesThetaRaw_pair_of_admissibleDelta_base` (proved earlier in this file) shows how
to build `RealizesThetaRaw_pair` from a **base-indexed admissibility** hypothesis at the
difference-level `u - v`, together with the **absence** of base-indexed B-witnesses at that level.

The two lemmas below package that wiring so it can be used directly in Goertzel-v2 style proofs.
-/

lemma realizesThetaRaw_pair_of_admissibleInterval_base
    {δ : ℝ} (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hI :
      AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v))
    (hδL : hI.L < δ) (hδU : δ < hI.U) :
    RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v := by
  have hδ :
      AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 (u - v)
        (Nat.sub_pos_of_lt huv) :=
    hI.admissible δ hδL hδU
  exact
    realizesThetaRaw_pair_of_admissibleDelta_base (R := R) (F := F) (d := d) (hd := hd) (r0 := r0)
      (ry := ry) (u := u) (v := v) huv hδ hB_base

lemma flip_implies_baseIndexed_B_witness_pair_of_admissibleInterval_base
    {δ₁ δ₂ : ℝ} (hδ : δ₁ < δ₂)
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hd' : ident < d)
    (hI :
      AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v))
    (hδ₁I : hI.L < δ₁) (_hδ₁U : δ₁ < hI.U) (_hδ₂I : hI.L < δ₂) (hδ₂U : δ₂ < hI.U)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u) :
    ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v) := by
  have hRealize :
      ∀ δ, δ₁ < δ → δ < δ₂ →
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ r0 ry u v := by
    intro δ hδ₁ hδ₂
    have hδL : hI.L < δ := lt_trans hδ₁I hδ₁
    have hδU : δ < hI.U := lt_trans hδ₂ hδ₂U
    exact
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := ry) (u := u) (v := v) huv hI hB_base hδL hδU
  exact
    flip_implies_baseIndexed_B_witness_pair (R := R) (F := F) (d := d) (hd := hd') hδ r0 ry u v
      huv hRealize h1 h2

/-- **Goertzel v2 Lemma 7 (order-invariance, base-indexed)**.

Within a fixed admissible interval `I` (for the base `r0` at the difference level `u - v`),
the truth value of `ThetaRaw δ r0 u < ThetaRaw δ ry v` cannot depend on the particular choice
`δ ∈ I`, provided there is no base-indexed `B`-witness at that difference level.

This matches Lemma 7 in `/home/zar/claude/literature/Foundations-of-inference-new-proofs_v2.pdf`
(§4.3.3), specialized to the Lean `ThetaRaw` encoding. -/
theorem ThetaRaw_order_invariant_inside_admissibleInterval_base
    {δ₁ δ₂ : ℝ}
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hd' : ident < d)
    (hI :
      AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v))
    (hδ₁L : hI.L < δ₁) (hδ₁U : δ₁ < hI.U)
    (hδ₂L : hI.L < δ₂) (hδ₂U : δ₂ < hI.U) :
    (ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v) ↔
      (ThetaRaw (R := R) (F := F) δ₂ r0 u < ThetaRaw (R := R) (F := F) δ₂ ry v) := by
  classical
  -- Trichotomy on the two choices.
  rcases lt_trichotomy δ₁ δ₂ with hδ | rfl | hδ
  · -- Case δ₁ < δ₂: show both directions.
    have huv_le : v ≤ u := le_of_lt huv
    have hReal2 :
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ₂ r0 ry u v :=
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := ry) (u := u) (v := v) huv hI hB_base hδ₂L hδ₂U
    constructor
    · intro h1
      -- If the inequality failed at δ₂, we’d get either an equality or a strict reversal; both
      -- imply a base-indexed B-witness at (u - v), contradicting `hB_base`.
      by_contra h2
      have h2le :
          ThetaRaw (R := R) (F := F) δ₂ ry v ≤ ThetaRaw (R := R) (F := F) δ₂ r0 u :=
        le_of_not_gt h2
      have h2' : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u ∨
          ThetaRaw (R := R) (F := F) δ₂ ry v = ThetaRaw (R := R) (F := F) δ₂ r0 u :=
        lt_or_eq_of_le h2le
      cases h2' with
      | inl hrev =>
          rcases
              flip_implies_baseIndexed_B_witness_pair_of_admissibleInterval_base (R := R) (F := F)
                (d := d) (hd' := hd') (r0 := r0) (ry := ry)
                (u := u) (v := v) hδ huv hI hB_base hδ₁L hδ₁U hδ₂L hδ₂U h1 hrev
            with ⟨rB, hrB⟩
          exact hB_base ⟨rB, hrB⟩
      | inr hEq =>
          have hμEq :
              mu (extendAtomFamily F d hd') (joinMulti r0 u) =
                mu (extendAtomFamily F d hd') (joinMulti ry v) :=
            ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd')
              (hδ := hReal2) (hEq := hEq.symm)
          have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
            extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd' r0 ry u v huv_le hμEq
          exact hB_base ⟨ry, hB⟩
    · -- The converse direction (δ₂ inequality ⇒ δ₁ inequality) holds unconditionally because
      -- `v < u` makes the comparison affine-decreasing in δ.
      intro h2
      -- Work with the difference `ThetaRaw … - ThetaRaw …`.
      have hdiff2 :
          ThetaRaw (R := R) (F := F) δ₂ r0 u - ThetaRaw (R := R) (F := F) δ₂ ry v < 0 :=
        sub_neg.mpr h2
      set a : ℝ :=
        (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ -
            R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩) with ha
      set b : ℝ := (u : ℝ) - (v : ℝ) with hb
      have hb_pos : 0 < b := by
        have : (v : ℝ) < (u : ℝ) := by exact_mod_cast huv
        simpa [b] using sub_pos.mpr this
      have hdiff2' : a + b * δ₂ < 0 := by
        -- Rewrite the δ₂ difference using `ThetaRaw_sub`.
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff2
      have hmul : b * δ₁ < b * δ₂ := mul_lt_mul_of_pos_left hδ hb_pos
      -- Avoid a convoluted inequality chain by using `linarith`.
      have hdiff1' : a + b * δ₁ < 0 := by
        linarith [hdiff2', hmul]
      have hdiff1 :
          ThetaRaw (R := R) (F := F) δ₁ r0 u - ThetaRaw (R := R) (F := F) δ₁ ry v < 0 := by
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff1'
      exact sub_neg.mp hdiff1
  · -- Case δ₁ = δ₂.
    simp
  · -- Case δ₂ < δ₁: apply the δ₂<δ₁ result and then symmetrize.
    have huv_le : v ≤ u := le_of_lt huv
    have hReal1 :
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ₁ r0 ry u v :=
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := ry) (u := u) (v := v) huv hI hB_base hδ₁L hδ₁U
    constructor
    · intro h1
      -- The direction δ₁-inequality ⇒ δ₂-inequality holds unconditionally (smaller δ strengthens the `<`).
      have hdiff1 :
          ThetaRaw (R := R) (F := F) δ₁ r0 u - ThetaRaw (R := R) (F := F) δ₁ ry v < 0 :=
        sub_neg.mpr h1
      set a : ℝ :=
        (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ -
            R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩) with ha
      set b : ℝ := (u : ℝ) - (v : ℝ) with hb
      have hb_pos : 0 < b := by
        have : (v : ℝ) < (u : ℝ) := by exact_mod_cast huv
        simpa [b] using sub_pos.mpr this
      have hdiff1' : a + b * δ₁ < 0 := by
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff1
      have hmul : b * δ₂ < b * δ₁ := mul_lt_mul_of_pos_left hδ hb_pos
      have hdiff2' : a + b * δ₂ < 0 := by
        linarith [hdiff1', hmul]
      have hdiff2 :
          ThetaRaw (R := R) (F := F) δ₂ r0 u - ThetaRaw (R := R) (F := F) δ₂ ry v < 0 := by
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff2'
      exact sub_neg.mp hdiff2
    · intro h2
      -- If the inequality failed at δ₁, we’d get either an equality or a strict reversal; both
      -- imply a base-indexed B-witness at (u - v), contradicting `hB_base`.
      by_contra h1
      have h1le :
          ThetaRaw (R := R) (F := F) δ₁ ry v ≤ ThetaRaw (R := R) (F := F) δ₁ r0 u :=
        le_of_not_gt h1
      have h1' : ThetaRaw (R := R) (F := F) δ₁ ry v < ThetaRaw (R := R) (F := F) δ₁ r0 u ∨
          ThetaRaw (R := R) (F := F) δ₁ ry v = ThetaRaw (R := R) (F := F) δ₁ r0 u :=
        lt_or_eq_of_le h1le
      cases h1' with
      | inl hrev =>
          rcases
              flip_implies_baseIndexed_B_witness_pair_of_admissibleInterval_base (R := R) (F := F)
                (d := d) (hd' := hd') (r0 := r0) (ry := ry)
                (u := u) (v := v) hδ huv hI hB_base hδ₂L hδ₂U hδ₁L hδ₁U h2 hrev
            with ⟨rB, hrB⟩
          exact hB_base ⟨rB, hrB⟩
      | inr hEq =>
          have hμEq :
              mu (extendAtomFamily F d hd') (joinMulti r0 u) =
                mu (extendAtomFamily F d hd') (joinMulti ry v) :=
            ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd')
              (hδ := hReal1) (hEq := hEq.symm)
          have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
            extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd' r0 ry u v huv_le hμEq
          exact hB_base ⟨ry, hB⟩

/-- **Goertzel v2 Lemma 8 (finite truncation, base-indexed)**.

For a fixed base `r0` and a finite set of positive “new levels” `U`, consider the set of formal
symbols consisting of:
- old-grid witnesses `r : Multi k` (interpreted as `ThetaRaw δ r 0`), and
- base-family witnesses `(r0,u)` for `u ∈ U` (interpreted as `ThetaRaw δ r0 u`).

If two choices `δ₁, δ₂` lie inside the base-indexed admissible interval at **each** `u ∈ U`, and
there are no base-indexed `B` witnesses at those levels, then every pairwise strict comparison in
this finite “old ∪ base-family” set is independent of whether one uses `δ₁` or `δ₂`.

This is the Lean analogue of Lemma 8 in
`/home/zar/claude/literature/Foundations-of-inference-new-proofs_v2.pdf` (where the argument is
presented for the coordinate-host picture; here we express it directly in terms of `ThetaRaw`). -/
theorem ThetaRaw_order_invariant_oldGrid_with_baseFamily_finset
    {δ₁ δ₂ : ℝ} (r0 : Multi k) (U : Finset ℕ)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hd' : ident < d)
    (hI :
      ∀ u (huU : u ∈ U),
        AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 u (hUpos u huU))
    (hB :
      ∀ u ∈ U, ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 u)
    (hδ₁ :
      ∀ u (huU : u ∈ U), (hI u huU).L < δ₁ ∧ δ₁ < (hI u huU).U)
    (hδ₂ :
      ∀ u (huU : u ∈ U), (hI u huU).L < δ₂ ∧ δ₂ < (hI u huU).U) :
    ∀ a b : Sum (Multi k) {u : ℕ // u ∈ U},
      ((match a with
          | Sum.inl r => ThetaRaw (R := R) (F := F) δ₁ r 0
          | Sum.inr u => ThetaRaw (R := R) (F := F) δ₁ r0 u.1) <
          (match b with
            | Sum.inl r => ThetaRaw (R := R) (F := F) δ₁ r 0
            | Sum.inr u => ThetaRaw (R := R) (F := F) δ₁ r0 u.1)) ↔
        ((match a with
          | Sum.inl r => ThetaRaw (R := R) (F := F) δ₂ r 0
          | Sum.inr u => ThetaRaw (R := R) (F := F) δ₂ r0 u.1) <
          (match b with
            | Sum.inl r => ThetaRaw (R := R) (F := F) δ₂ r 0
            | Sum.inr u => ThetaRaw (R := R) (F := F) δ₂ r0 u.1)) := by
  classical
  intro a b
  -- Name the evaluation function to keep the cases readable.
  let val : ℝ → Sum (Multi k) {u : ℕ // u ∈ U} → ℝ := fun δ p =>
    match p with
    | Sum.inl r => ThetaRaw (R := R) (F := F) δ r 0
    | Sum.inr u => ThetaRaw (R := R) (F := F) δ r0 u.1
  -- Helper: any δ in the admissible interval at level `u` is positive (since `r0 ∈ A_base`).
  have delta_pos_of_mem {δ : ℝ} {u : ℕ} (huU : u ∈ U)
      (hL : (hI u huU).L < δ) (hU : δ < (hI u huU).U) : 0 < δ := by
    have hu : 0 < u := hUpos u huU
    have hAd : AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 u hu :=
      (hI u huU).admissible δ hL hU
    have hr0A : r0 ∈ extensionSetA_base F d r0 u := by
      have hdu : ident < iterate_op d u := iterate_op_pos d hd' u hu
      have : mu F r0 < op (mu F r0) (iterate_op d u) := by
        simpa [op_ident_right] using (op_strictMono_right (mu F r0) hdu)
      simpa [extensionSetA_base, Set.mem_setOf_eq] using this
    have h0lt : separationStatistic_base R r0 r0 u hu < δ := (hAd.1 r0 hr0A)
    simpa [separationStatistic_base] using h0lt
  -- Helper: old/new equality at an admissible δ creates a base-indexed B-witness, hence is impossible under `hB`.
  have no_old_new_eq {δ : ℝ} {u : ℕ} (huU : u ∈ U)
      (hL : (hI u huU).L < δ) (hU : δ < (hI u huU).U)
      (r : Multi k) :
      ThetaRaw (R := R) (F := F) δ r0 u ≠ ThetaRaw (R := R) (F := F) δ r 0 := by
    intro hEq
    have hu : 0 < u := hUpos u huU
    have hReal :
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ r0 r u 0 :=
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := r) (u := u) (v := 0) hu
        (hI := by simpa [Nat.sub_zero] using (hI u huU))
        (hB_base := by
          -- `u - 0 = u`, so the hypothesis `hB` applies directly.
          simpa [Nat.sub_zero] using (hB u huU))
        (hδL := hL) (hδU := hU)
    have hμEq :
        mu (extendAtomFamily F d hd') (joinMulti r0 u) =
          mu (extendAtomFamily F d hd') (joinMulti r 0) :=
      ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd')
        (hδ := hReal) (hEq := hEq)
    have hBmem : r ∈ extensionSetB_base F d r0 (u - 0) :=
      extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd' r0 r u 0 (Nat.zero_le _) hμEq
    have : ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 u := by
      refine ⟨r, ?_⟩
      simpa [Nat.sub_zero] using hBmem
    exact (hB u huU) this
  -- Case analysis on the two formal symbols.
  cases a with
  | inl ra =>
      cases b with
      | inl rb =>
          -- old-old: δ disappears since `t = 0`.
          simp [ThetaRaw]
      | inr ub =>
          -- old-new: reduce to invariance of the opposite comparison (new-old) plus exclusion of equality.
          have huU : ub.1 ∈ U := ub.2
          have hδ₁b := hδ₁ ub.1 huU
          have hδ₂b := hδ₂ ub.1 huU
          have hneq1 :
              ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 ≠ ThetaRaw (R := R) (F := F) δ₁ ra 0 :=
            no_old_new_eq (u := ub.1) huU hδ₁b.1 hδ₁b.2 ra
          have hneq2 :
              ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 ≠ ThetaRaw (R := R) (F := F) δ₂ ra 0 :=
            no_old_new_eq (u := ub.1) huU hδ₂b.1 hδ₂b.2 ra
          have hflip :
              (ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₁ ra 0) ↔
                (ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₂ ra 0) :=
            ThetaRaw_order_invariant_inside_admissibleInterval_base (R := R) (F := F) (d := d)
              (r0 := r0) (ry := ra) (u := ub.1) (v := 0) (huv := hUpos ub.1 huU) (hd' := hd')
              (hI := by simpa [Nat.sub_zero] using (hI ub.1 huU))
              (hB_base := by simpa [Nat.sub_zero] using (hB ub.1 huU))
              (hδ₁L := hδ₁b.1) (hδ₁U := hδ₁b.2) (hδ₂L := hδ₂b.1) (hδ₂U := hδ₂b.2)
          -- Convert `<` by trichotomy using `hneq1`/`hneq2`.
          have hold1 :
              ThetaRaw (R := R) (F := F) δ₁ ra 0 < ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 ↔
                ¬ ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₁ ra 0 := by
            constructor
            · intro hlt
              exact not_lt_of_gt hlt
            · intro hn
              rcases lt_trichotomy (ThetaRaw (R := R) (F := F) δ₁ r0 ub.1)
                  (ThetaRaw (R := R) (F := F) δ₁ ra 0) with hlt | heq | hgt
              · exact (hn hlt).elim
              · exact (hneq1 heq).elim
              · exact hgt
          have hold2 :
              ThetaRaw (R := R) (F := F) δ₂ ra 0 < ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 ↔
                ¬ ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₂ ra 0 := by
            constructor
            · intro hlt
              exact not_lt_of_gt hlt
            · intro hn
              rcases lt_trichotomy (ThetaRaw (R := R) (F := F) δ₂ r0 ub.1)
                  (ThetaRaw (R := R) (F := F) δ₂ ra 0) with hlt | heq | hgt
              · exact (hn hlt).elim
              · exact (hneq2 heq).elim
              · exact hgt
          -- Put it together.
          have :
              (ThetaRaw (R := R) (F := F) δ₁ ra 0 < ThetaRaw (R := R) (F := F) δ₁ r0 ub.1) ↔
                (ThetaRaw (R := R) (F := F) δ₂ ra 0 < ThetaRaw (R := R) (F := F) δ₂ r0 ub.1) := by
            -- `old<new` is the negation of `new<old` on each side.
            simpa [hold1, hold2] using (not_congr hflip)
          simpa [val] using this
  | inr ua =>
      cases b with
      | inl rb =>
          -- new-old: direct use of Lemma 7.
          have huU : ua.1 ∈ U := ua.2
          have hδ₁a := hδ₁ ua.1 huU
          have hδ₂a := hδ₂ ua.1 huU
          have :
              (ThetaRaw (R := R) (F := F) δ₁ r0 ua.1 < ThetaRaw (R := R) (F := F) δ₁ rb 0) ↔
                (ThetaRaw (R := R) (F := F) δ₂ r0 ua.1 < ThetaRaw (R := R) (F := F) δ₂ rb 0) :=
            ThetaRaw_order_invariant_inside_admissibleInterval_base (R := R) (F := F) (d := d)
              (r0 := r0) (ry := rb) (u := ua.1) (v := 0) (huv := hUpos ua.1 huU) (hd' := hd')
              (hI := by simpa [Nat.sub_zero] using (hI ua.1 huU))
              (hB_base := by simpa [Nat.sub_zero] using (hB ua.1 huU))
              (hδ₁L := hδ₁a.1) (hδ₁U := hδ₁a.2) (hδ₂L := hδ₂a.1) (hδ₂U := hδ₂a.2)
          simpa [val] using this
        | inr ub =>
            -- new-new: comparisons depend only on the nat levels since admissible δ's are positive.
            have huU : ua.1 ∈ U := ua.2
            have hδ₁u := hδ₁ ua.1 huU
            have hδ₂u := hδ₂ ua.1 huU
            have hδ₁_pos : 0 < δ₁ := delta_pos_of_mem (u := ua.1) huU hδ₁u.1 hδ₁u.2
            have hδ₂_pos : 0 < δ₂ := delta_pos_of_mem (u := ua.1) huU hδ₂u.1 hδ₂u.2
            have hcmp₁ :
                (ThetaRaw (R := R) (F := F) δ₁ r0 ua.1 <
                      ThetaRaw (R := R) (F := F) δ₁ r0 ub.1) ↔ ua.1 < ub.1 := by
              have hmul :
                  (ThetaRaw (R := R) (F := F) δ₁ r0 ua.1 <
                        ThetaRaw (R := R) (F := F) δ₁ r0 ub.1) ↔
                    ((ua.1 : ℝ) * δ₁ < (ub.1 : ℝ) * δ₁) := by
                simpa [ThetaRaw] using
                  (add_lt_add_iff_left (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩))
              constructor
              · intro hlt
                have hmul_lt : (ua.1 : ℝ) * δ₁ < (ub.1 : ℝ) * δ₁ := (hmul.mp hlt)
                have hmul_lt' : δ₁ * (ua.1 : ℝ) < δ₁ * (ub.1 : ℝ) := by
                  simpa [mul_comm] using hmul_lt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₁_pos).1 hmul_lt'
                exact_mod_cast hcast
              · intro hlt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) := by exact_mod_cast hlt
                have hmul_lt' : δ₁ * (ua.1 : ℝ) < δ₁ * (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₁_pos).2 hcast
                have hmul_lt : (ua.1 : ℝ) * δ₁ < (ub.1 : ℝ) * δ₁ := by
                  simpa [mul_comm] using hmul_lt'
                exact hmul.mpr hmul_lt
            have hcmp₂ :
                (ThetaRaw (R := R) (F := F) δ₂ r0 ua.1 <
                      ThetaRaw (R := R) (F := F) δ₂ r0 ub.1) ↔ ua.1 < ub.1 := by
              have hmul :
                  (ThetaRaw (R := R) (F := F) δ₂ r0 ua.1 <
                        ThetaRaw (R := R) (F := F) δ₂ r0 ub.1) ↔
                    ((ua.1 : ℝ) * δ₂ < (ub.1 : ℝ) * δ₂) := by
                simpa [ThetaRaw] using
                  (add_lt_add_iff_left (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩))
              constructor
              · intro hlt
                have hmul_lt : (ua.1 : ℝ) * δ₂ < (ub.1 : ℝ) * δ₂ := (hmul.mp hlt)
                have hmul_lt' : δ₂ * (ua.1 : ℝ) < δ₂ * (ub.1 : ℝ) := by
                  simpa [mul_comm] using hmul_lt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₂_pos).1 hmul_lt'
                exact_mod_cast hcast
              · intro hlt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) := by exact_mod_cast hlt
                have hmul_lt' : δ₂ * (ua.1 : ℝ) < δ₂ * (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₂_pos).2 hcast
                have hmul_lt : (ua.1 : ℝ) * δ₂ < (ub.1 : ℝ) * δ₂ := by
                  simpa [mul_comm] using hmul_lt'
                exact hmul.mpr hmul_lt
            simpa [val] using (hcmp₁.trans hcmp₂.symm)
lemma flip_implies_baseIndexed_B_witness
    {δ₁ δ₂ : ℝ} (hδ : δ₁ < δ₂)
    (hRealize :
      ∀ δ, δ₁ < δ → δ < δ₂ → RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) δ)
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u) :
    ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v) := by
  classical
  have hRealize_pair :
      ∀ δ, δ₁ < δ → δ < δ₂ →
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v := by
    intro δ hδ₁ hδ₂
    exact realizesThetaRaw_pair_of_realizesThetaRaw (R := R) (F := F) (d := d) (hd := hd)
      (hRealize δ hδ₁ hδ₂) r0 ry u v
  exact
    flip_implies_baseIndexed_B_witness_pair (R := R) (F := F) (d := d)
      (hd := hd) hδ r0 ry u v huv hRealize_pair h1 h2

end BenV2

/-!
## Circularity made explicit (Ben-v2 vs `BEmptyStrictGapSpec`)

The hypercube/Ben-v2 “boundary collision” argument shows:

`(strictly monotone Θ' realizing ThetaRaw at δ)` ⇒ `BEmptyStrictGapSpec` at δ.

In the main Appendix-A development, the *forward* direction is what one uses to rule out
boundary equalities, but the *reverse* direction is exactly where the k→k+1 step gets stuck:
to build such a strictly monotone Θ' in the mixed-`t` cases, the strict gap spec is assumed.

This lemma does **not** resolve the circularity; it records the implication cleanly so that any
attempted proof can be checked against it.
-/

section Circularity

variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d) [KSSeparation α]

lemma bEmptyStrictGapSpec_of_realizesThetaRaw_chooseδ
    (hReal :
      RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) (chooseδ hk R d hd)) :
    BEmptyStrictGapSpec hk R IH H d hd := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  rcases hReal with ⟨Θ', hΘ'_strict, hΘ'_on_join⟩
  refine
    { A := ?_
      C := ?_ }
  · intro _hB_empty r_old_x r_old_y Δ hΔ hμ_gt hA_base _hB_base
    -- Compare the two extended μ-values: (r_old_x,0) and (r_old_y,Δ).
    have h_between :
        mu (extendAtomFamily F d hd) (joinMulti r_old_x 0) <
          mu (extendAtomFamily F d hd) (joinMulti r_old_y Δ) := by
      have hx0 :
          mu (extendAtomFamily F d hd) (joinMulti r_old_x 0) = mu F r_old_x := by
        simpa [iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_old_x 0)
      have hyΔ :
          mu (extendAtomFamily F d hd) (joinMulti r_old_y Δ) =
            op (mu F r_old_y) (iterate_op d Δ) := by
        simpa using (mu_extend_last F d hd r_old_y Δ)
      have : mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ) := by
        simpa [extensionSetA_base, Set.mem_setOf_eq] using hA_base
      simpa [hx0, hyΔ] using this
    have hΘ_lt :
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x 0),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x 0)⟩ <
          Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y Δ),
                mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y Δ)⟩ :=
      hΘ'_strict h_between
    -- Rewrite with ThetaRaw and divide by Δ.
    have hRaw_lt :
        ThetaRaw (R := R) (F := F) δ r_old_x 0 <
          ThetaRaw (R := R) (F := F) δ r_old_y Δ := by
      simpa [hΘ'_on_join] using hΘ_lt
    -- Unfold ThetaRaw and rearrange.
    have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
    have :
        (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) / Δ < δ := by
      -- From: Θx < Θy + Δ*δ
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (Δ : ℝ) * δ := by
        simpa [ThetaRaw] using hRaw_lt
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
        linarith
      -- Divide by Δ>0 (note `div_lt_iff₀` expects `… < δ * Δ`).
      have hgap' :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < δ * (Δ : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact (div_lt_iff₀ hΔ_pos_real).2 hgap'
    simpa [separationStatistic_base, δ] using this
  · intro _hB_empty r_old_x r_old_y Δ hΔ hμ_lt hC_base _hB_base
    -- Compare the two extended μ-values: (r_old_x,Δ) and (r_old_y,0).
    have h_between :
        mu (extendAtomFamily F d hd) (joinMulti r_old_x Δ) <
          mu (extendAtomFamily F d hd) (joinMulti r_old_y 0) := by
      have hxΔ :
          mu (extendAtomFamily F d hd) (joinMulti r_old_x Δ) =
            op (mu F r_old_x) (iterate_op d Δ) := by
        simpa using (mu_extend_last F d hd r_old_x Δ)
      have hy0 :
          mu (extendAtomFamily F d hd) (joinMulti r_old_y 0) = mu F r_old_y := by
        simpa [iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_old_y 0)
      have : op (mu F r_old_x) (iterate_op d Δ) < mu F r_old_y := by
        simpa [extensionSetC_base, Set.mem_setOf_eq] using hC_base
      simpa [hxΔ, hy0] using this
    have hΘ_lt :
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x Δ),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x Δ)⟩ <
          Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y 0),
                mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y 0)⟩ :=
      hΘ'_strict h_between
    have hRaw_lt :
        ThetaRaw (R := R) (F := F) δ r_old_x Δ <
          ThetaRaw (R := R) (F := F) δ r_old_y 0 := by
      simpa [hΘ'_on_join] using hΘ_lt
    have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
    have :
        δ < (R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩) / Δ := by
      -- From: Θx + Δ*δ < Θy
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (Δ : ℝ) * δ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
        simpa [ThetaRaw] using hRaw_lt
      have : (Δ : ℝ) * δ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
        linarith
      -- Divide by Δ>0 and rearrange (note `lt_div_iff₀` expects `δ * Δ < …`).
      have hgap' :
          δ * (Δ : ℝ) <
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact (lt_div_iff₀ hΔ_pos_real).2 hgap'
    simpa [separationStatistic_base, δ] using this

lemma realizesThetaRaw_chooseδ_of_BEmptyStrictGapSpec
    (hZQ_if : ZQuantized_chooseδ_if_B_nonempty (α := α) hk R d hd)
    (hStrict : BEmptyStrictGapSpec hk R IH H d hd) :
    RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) (chooseδ hk R d hd) := by
  classical
  rcases
      extend_grid_rep_with_atom (α := α) (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
        (hZQ_if := hZQ_if) (hStrict := hStrict) with
    ⟨F', hF'_old, hF'_new, R', hExt⟩
  have hF' : F' = extendAtomFamily F d hd :=
    AtomFamily.eq_extendAtomFamily_of_old_new (F := F) (d := d) (hd := hd) F' hF'_old hF'_new
  cases hF'
  refine ⟨R'.Θ_grid, R'.strictMono, ?_⟩
  intro r_old t
  -- `ThetaRaw` is exactly the `Θ`-extension formula produced by `extend_grid_rep_with_atom`.
  simpa [ThetaRaw] using (hExt r_old t)

theorem realizesThetaRaw_chooseδ_iff_BEmptyStrictGapSpec
    (hZQ_if : ZQuantized_chooseδ_if_B_nonempty (α := α) hk R d hd) :
    RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) (chooseδ hk R d hd) ↔
      BEmptyStrictGapSpec hk R IH H d hd := by
  constructor
  · intro hReal
    exact bEmptyStrictGapSpec_of_realizesThetaRaw_chooseδ (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd) hReal
  · intro hStrict
    exact realizesThetaRaw_chooseδ_of_BEmptyStrictGapSpec (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd) (hZQ_if := hZQ_if) hStrict

end Circularity

/-!
## A “strong-but-clean” interface that would discharge `BEmptyStrictGapSpec`

`BEmptyStrictGapSpec` asks for **strict** base-indexed A/C inequalities at the specific choice
`δ := chooseδ hk R d hd` in the globally `B = ∅` regime (K&S Appendix A.3.4).

A conceptually simpler sufficient condition is that this same `δ` is *already* admissible for **all**
base-indexed comparisons at every base `r0` and level `u>0`:

`AdmissibleDelta_base R d δ r0 u`.

This is stronger than what Appendix A needs, but it cleanly isolates the missing ingredient:
if one can prove `ChooseδBaseAdmissible` from the current `Core/` development, then the strict-gap
blocker disappears immediately.
-/

section ChooseδBase

variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d)
variable [KSSeparation α]

/-- **Strong interface**: the chosen `δ := chooseδ …` is base-admissible for *every* base `r0`
and level `u > 0`.

This is stronger than `BEmptyStrictGapSpec` (which only needs strictness in the “external” base-
indexed cases), but it is a clean sufficient condition and can serve as a focused subgoal for
future work. -/
class ChooseδBaseAdmissible : Prop where
  base :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u),
      AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) (chooseδ hk R d hd) r0 u hu

theorem bEmptyStrictGapSpec_of_chooseδBaseAdmissible
    (h : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
    BEmptyStrictGapSpec hk R IH H d hd := by
  classical
  refine ⟨?_, ?_⟩
  · intro _hB_empty r_old_x r_old_y Δ hΔ _hμ hA_base _hB_base
    exact (h.base r_old_y Δ hΔ).1 r_old_x hA_base
  · intro _hB_empty r_old_x r_old_y Δ hΔ _hμ hC_base _hB_base
    exact (h.base r_old_x Δ hΔ).2 r_old_y hC_base

/-- Convenience wrapper: the inductive extension step follows from the stronger
`ChooseδBaseAdmissible` hypothesis. -/
theorem extend_grid_rep_with_atom_of_chooseδBaseAdmissible
    (IH : GridBridge F) (H : GridComm F)
    (hZQ_if : ZQuantized_chooseδ_if_B_nonempty (α := α) hk R d hd)
    (hBase : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  have hStrict : BEmptyStrictGapSpec hk R IH H d hd :=
    bEmptyStrictGapSpec_of_chooseδBaseAdmissible (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd) hBase
  exact extend_grid_rep_with_atom (α := α) (hk := hk) (R := R) (IH := IH) (H := H) (d := d)
    (hd := hd) (hZQ_if := hZQ_if) (hStrict := hStrict)

end ChooseδBase

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
