import KnuthSkilling.Additive.Representation

/-!
# Regraduation, rational calibration and compatible probability scales

A supplied linearizer is distinct from an existence theorem. Agreement of
the combination law with addition on rational unit values calibrates that
linearizer on the whole unit interval. Multiplication together with ordinary
complement also fixes a normalized monotone probability scale uniquely.
-/

namespace KnuthSkilling.Probability

/-- A supplied strictly increasing linearizer, normalized at zero and one. -/
structure WeakRegraduation (combine_fn : ℝ → ℝ → ℝ) where
  regrade : ℝ → ℝ
  strictMono : StrictMono regrade
  zero : regrade 0 = 0
  one : regrade 1 = 1
  combine_eq_add : ∀ x y, regrade (combine_fn x y) = regrade x + regrade y

/-- A linearizer additionally supplied with global real additivity. -/
structure Regraduation (combine_fn : ℝ → ℝ → ℝ) extends WeakRegraduation combine_fn where
  additive : ∀ x y, regrade (x + y) = regrade x + regrade y

private theorem ratGrid_multiple (f : ℚ → ℝ) (h0 : f 0 = 0)
    (hadd : ∀ r s, 0 ≤ r → 0 ≤ s → r + s ≤ 1 → f (r + s) = f r + f s)
    (n : ℕ) (hn : 0 < n) :
    ∀ k : ℕ, k ≤ n → f (k / n) = (k : ℝ) * f (1 / n) := by
  intro k hk
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hsum : (k : ℚ) / n + 1 / n ≤ 1 := by
      rw [← add_div, div_le_one (by exact_mod_cast hn)]
      exact_mod_cast hk
    rw [show ((k + 1 : ℕ) : ℚ) / n = (k : ℚ) / n + 1 / n by push_cast; ring,
      hadd _ _ (by positivity) (by positivity) hsum, ih (by omega)]
    push_cast
    ring

private theorem ratGrid_unit (f : ℚ → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hadd : ∀ r s, 0 ≤ r → 0 ≤ s → r + s ≤ 1 → f (r + s) = f r + f s)
    (n : ℕ) (hn : 0 < n) : f (1 / n) = (1 : ℝ) / n := by
  have h := ratGrid_multiple f h0 hadd n hn n le_rfl
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [div_self hnq, h1] at h
  apply (eq_div_iff hnr).2
  simpa only [mul_comm] using h.symm

private theorem ratGrid_identity (f : ℚ → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hadd : ∀ r s, 0 ≤ r → 0 ≤ s → r + s ≤ 1 → f (r + s) = f r + f s)
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : f q = q := by
  have hnum : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0)
  have hq : (q.num.toNat : ℚ) / q.den = q := by rw [hnum, Rat.num_div_den]
  have hp : q.num.toNat ≤ q.den := by
    have hle : (q.num.toNat : ℚ) / q.den ≤ 1 := by rw [hq]; exact hq1
    rw [div_le_one (by exact_mod_cast q.den_pos)] at hle
    exact_mod_cast hle
  calc
    f q = f ((q.num.toNat : ℚ) / q.den) := congrArg f hq.symm
    _ = (q.num.toNat : ℝ) * f (1 / q.den) :=
      ratGrid_multiple f h0 hadd q.den q.den_pos _ hp
    _ = (q.num.toNat : ℝ) / q.den := by rw [ratGrid_unit f h0 h1 hadd q.den q.den_pos]; ring
    _ = q := by
      simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun r : ℚ => (r : ℝ)) hq

/-- Monotone unit observations agreeing on rational values agree everywhere. -/
theorem eq_id_on_unit_of_rat (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1))
    (h_rat : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ 1 → f q = q) :
    Set.EqOn f id (Set.Icc 0 1) := by
  intro x hx
  have h0 : f 0 = 0 := by simpa using h_rat 0 (by norm_num) (by norm_num)
  have h1 : f 1 = 1 := by simpa using h_rat 1 (by norm_num) (by norm_num)
  have hb : f x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨h0 ▸ hf (by simp) hx hx.1, h1 ▸ hf hx (by simp) hx.2⟩
  apply le_antisymm
  · by_contra h
    obtain ⟨q, hxq, hqf⟩ := exists_rat_btwn (lt_of_not_ge h)
    have hq := h_rat q (hx.1.trans hxq.le) (hqf.le.trans hb.2)
    have := hf hx ⟨hx.1.trans hxq.le, hqf.le.trans hb.2⟩ hxq.le
    rw [hq] at this
    linarith
  · by_contra h
    obtain ⟨q, hfq, hqx⟩ := exists_rat_btwn (lt_of_not_ge h)
    have hq := h_rat q (hb.1.trans hfq.le) (hqx.le.trans hx.2)
    have := hf ⟨hb.1.trans hfq.le, hqx.le.trans hx.2⟩ hx hqx.le
    rw [hq] at this
    linarith

theorem strictMono_eq_id_of_eq_on_rat
    (φ : ℝ → ℝ) (hφ : StrictMono φ)
    (h_rat : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ 1 → φ q = q) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → φ x = x :=
  fun _x hx0 hx1 => eq_id_on_unit_of_rat φ (hφ.monotone.monotoneOn _) h_rat ⟨hx0, hx1⟩

/-- Rational partial additivity and endpoint calibration determine a monotone unit readout. -/
theorem eq_id_on_unit_of_add_rat (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1))
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hadd : ∀ r s : ℚ, 0 ≤ r → 0 ≤ s → r + s ≤ 1 →
      f ((r + s : ℚ) : ℝ) = f r + f s) : Set.EqOn f id (Set.Icc 0 1) := by
  apply eq_id_on_unit_of_rat f hf
  intro q hq0 hq1
  exact ratGrid_identity (fun q => f q) (by simpa using h0) (by simpa using h1) hadd q (by exact_mod_cast hq0)
    (by exact_mod_cast hq1)

theorem regrade_on_nat (W : WeakRegraduation combine_fn)
    (h_combine_nat : ∀ m n : ℕ, combine_fn (m : ℝ) (n : ℝ) = ((m + n : ℕ) : ℝ)) :
    ∀ n : ℕ, W.regrade (n : ℝ) = n := by
  intro n
  induction n with
  | zero => simpa using W.zero
  | succ n ih =>
    have h := W.combine_eq_add (n : ℝ) 1
    have hn := h_combine_nat n 1
    simp only [Nat.cast_one] at hn
    rw [hn, ih, W.one] at h
    simpa using h

lemma rat_div_cast_eq (k n : ℕ) (_hn : (n : ℚ) ≠ 0) :
    (((k : ℚ) / n) : ℝ) = (k : ℝ) / (n : ℝ) := by push_cast; rfl

lemma rat_one_div_cast_eq (n : ℕ) (_hn : (n : ℚ) ≠ 0) :
    (((1 : ℚ) / n) : ℝ) = (1 : ℝ) / (n : ℝ) := by push_cast; rfl

theorem regrade_add_rat (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
      combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (r s : ℚ) (hr : 0 ≤ (r : ℝ)) (hs : 0 ≤ (s : ℝ)) (hrs : (r : ℝ) + (s : ℝ) ≤ 1) :
    W.regrade ((r + s : ℚ) : ℝ) = W.regrade r + W.regrade s := by
  rw [← h_combine_rat r s hr hs hrs]
  exact W.combine_eq_add r s

lemma combine_fn_unit_fracs {combine_fn : ℝ → ℝ → ℝ}
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) →
      (r : ℝ) + (s : ℝ) ≤ 1 → combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (k n : ℕ) (hn : 0 < n) (hk : k + 1 ≤ n) :
    combine_fn ((k : ℝ) / (n : ℝ)) ((1 : ℝ) / (n : ℝ)) = ((k : ℝ) + 1) / (n : ℝ) := by
  have hsum : (k : ℚ) / n + 1 / n ≤ 1 := by
    rw [← add_div, div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hk
  have h := h_combine_rat ((k : ℚ) / n) (1 / n) (by positivity) (by positivity)
    (by exact_mod_cast hsum)
  simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_one, ← add_div] using h

private theorem regrade_add_rat' (W : WeakRegraduation combine_fn)
    (h : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
      combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ)) :
    ∀ r s : ℚ, 0 ≤ r → 0 ≤ s → r + s ≤ 1 →
      W.regrade ((r + s : ℚ) : ℝ) = W.regrade r + W.regrade s := by
  intro r s hr hs hrs
  exact regrade_add_rat W h r s (by exact_mod_cast hr) (by exact_mod_cast hs)
    (by exact_mod_cast hrs)

theorem regrade_unit_frac (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
      combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (n : ℕ) (hn : 0 < n) : W.regrade ((1 : ℚ) / n) = (1 : ℝ) / n := by
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
    ratGrid_unit (fun q => W.regrade q) (by simpa using W.zero) (by simpa using W.one)
      (regrade_add_rat' W h_combine_rat) n hn

theorem regrade_on_rat (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
      combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ)) :
    ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ 1 → W.regrade q = q := by
  intro q hq0 hq1
  exact ratGrid_identity (fun q => W.regrade q) (by simpa using W.zero) (by simpa using W.one)
    (regrade_add_rat' W h_combine_rat)
    q (by exact_mod_cast hq0) (by exact_mod_cast hq1)

theorem regrade_eq_id_on_unit (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
      combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → W.regrade x = x :=
  strictMono_eq_id_of_eq_on_rat W.regrade W.strictMono (regrade_on_rat W h_combine_rat)

theorem additive_derived (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
      combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hxy : x + y ≤ 1) :
    W.regrade (x + y) = W.regrade x + W.regrade y := by
  rw [regrade_eq_id_on_unit W h_combine_rat x hx.1 hx.2,
    regrade_eq_id_on_unit W h_combine_rat y hy.1 hy.2,
    regrade_eq_id_on_unit W h_combine_rat (x + y) (add_nonneg hx.1 hy.1) hxy]

theorem combine_fn_eq_add_derived (W : WeakRegraduation combine_fn)
    (h_combine_rat : ∀ r s : ℚ, 0 ≤ (r : ℝ) → 0 ≤ (s : ℝ) → (r : ℝ) + (s : ℝ) ≤ 1 →
      combine_fn (r : ℝ) (s : ℝ) = ((r + s : ℚ) : ℝ))
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hxy : x + y ≤ 1) :
    combine_fn x y = x + y :=
  W.strictMono.injective ((W.combine_eq_add x y).trans (additive_derived W h_combine_rat x y hx hy hxy).symm)

/-- Multiplication and ordinary complement calibrate a common normalized unit scale. -/
theorem mul_complement_calibration (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1))
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hmul : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, f (x * y) = f x * f y)
    (hcompl : ∀ x ∈ Set.Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) :
    Set.EqOn f id (Set.Icc 0 1) := by
  have hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ 1 → f (x + y) = f x + f y := by
    intro x y hx hy hxy
    by_cases hz : x + y = 0
    · have hx0 : x = 0 := by linarith
      have hy0 : y = 0 := by linarith
      simp [hx0, hy0, h0]
    · have hs : 0 < x + y := (add_nonneg hx hy).lt_of_ne' hz
      have hp : x / (x + y) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hx hs.le, (div_le_one hs).mpr (by linarith)⟩
      have hq : 1 - x / (x + y) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hp.1, hp.2]
      have hx' := hmul (x + y) ⟨hs.le, hxy⟩ _ hp
      have hy' := hmul (x + y) ⟨hs.le, hxy⟩ _ hq
      rw [show (x + y) * (x / (x + y)) = x by field_simp] at hx'
      rw [show (x + y) * (1 - x / (x + y)) = y by field_simp; ring,
        hcompl _ hp] at hy'
      nlinarith
  apply eq_id_on_unit_of_add_rat f hf h0 h1
  intro r s hr hs hrs
  simpa only [Rat.cast_add] using hadd r s (by exact_mod_cast hr) (by exact_mod_cast hs)
    (by exact_mod_cast hrs)

/-- Squaring preserves multiplication and certainty, but not ordinary complement. -/
theorem square_not_common_scale :
    (∀ x y : ℝ, (x * y) ^ 2 = x ^ 2 * y ^ 2) ∧ (1 : ℝ) ^ 2 = 1 ∧
      (1 - (1 / 2 : ℝ)) ^ 2 ≠ 1 - (1 / 2 : ℝ) ^ 2 :=
  ⟨fun x y => mul_pow x y 2, by norm_num, by norm_num⟩

end KnuthSkilling.Probability
