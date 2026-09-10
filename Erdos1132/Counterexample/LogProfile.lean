import Erdos1132.Counterexample.Constants
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # The explicit logarithmic profile in Section 7.2

Companion note: §2.2, the logarithmic integral estimate.
-/

noncomputable section

open Set MeasureTheory

namespace Erdos1132.Counterexample

def logProfile (t : ℝ) : ℝ := (8 - Real.log t) ^ (-1 / 256 : ℝ)

def logGapFunction (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  if r x = 0 then 0 else logProfile (r x)

theorem logProfile_pos {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : 0 < logProfile t := by
  apply Real.rpow_pos_of_pos
  have hl := Real.log_le_sub_one_of_pos ht
  linarith

theorem logProfile_le_one {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : logProfile t ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have hl := Real.log_le_sub_one_of_pos ht
    linarith
  · norm_num

theorem logProfile_le_logProfile {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (htlog : Real.log t < 8) : logProfile s ≤ logProfile t := by
  apply Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 8 - Real.log t)
    (by linarith [Real.log_le_log hs hst]) (by norm_num)

/-- A fixed multiplicative change of radius costs at most a factor two. -/
theorem logProfile_mul_five_le {s : ℝ} (hs : 0 < s) (hT : 16 ≤ 8 - Real.log s) :
    logProfile (5 * s) ≤ 2 * logProfile s := by
  have hlog : 8 - Real.log (5 * s) = (8 - Real.log s) - Real.log 5 := by
    rw [Real.log_mul (by norm_num) hs.ne']; ring
  have hbase : (7 / 8 : ℝ) * (8 - Real.log s) ≤ 8 - Real.log (5 * s) := by
    rw [hlog]
    linarith [log_five_le_two]
  have hfactor : (7 / 8 : ℝ) ^ (-1 / 256 : ℝ) ≤ 2 := by
    rw [show (-1 / 256 : ℝ) = -(1 / 256 : ℝ) by ring, Real.rpow_neg_eq_inv_rpow]
    norm_num
    linarith [fractional_power_bound]
  have hpos : 0 ≤ logProfile s := Real.rpow_nonneg (by linarith) _
  calc
    logProfile (5 * s) ≤ ((7 / 8 : ℝ) * (8 - Real.log s)) ^ (-1 / 256 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
    _ = (7 / 8 : ℝ) ^ (-1 / 256 : ℝ) * logProfile s := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hpos

/-- The measure contraction absorbs the increase of the far-field profile. -/
theorem logProfile_far_contraction {s : ℝ} (hs : 0 < s) (hT : 16 ≤ 8 - Real.log s) :
    (127 / 128 : ℝ) * (256 / 255 : ℝ) * logProfile (5 * s) ≤
      (1 - 1 / 512 : ℝ) * logProfile s := by
  have hlog : 8 - Real.log (5 * s) = (8 - Real.log s) - Real.log 5 := by
    rw [Real.log_mul (by norm_num) hs.ne']; ring
  have hbase : (7 / 8 : ℝ) * (8 - Real.log s) ≤ 8 - Real.log (5 * s) := by
    rw [hlog]
    linarith [log_five_le_two]
  have hpow : logProfile (5 * s) ≤
      (8 / 7 : ℝ) ^ (1 / 256 : ℝ) * logProfile s := by
    calc
      _ ≤ ((7 / 8 : ℝ) * (8 - Real.log s)) ^ (-1 / 256 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by linarith),
          show (-1 / 256 : ℝ) = -(1 / 256 : ℝ) by ring,
          Real.rpow_neg_eq_inv_rpow]
        norm_num
        simp [logProfile, neg_div]
  have hps : 0 ≤ logProfile s := Real.rpow_nonneg (by linarith) _
  have h := mul_le_mul_of_nonneg_right contraction_factor_bound hps
  have h' := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 254 / 255 by norm_num)
  nlinarith

/-- The ordinary derivative of the positive-radius profile. -/
theorem hasDerivAt_logProfile {t : ℝ} (ht : 0 < t) (htlog : Real.log t < 8) :
    HasDerivAt logProfile (logProfile t / (256 * t * (8 - Real.log t))) t := by
  have hb : 8 - Real.log t ≠ 0 := ne_of_gt (by linarith)
  have h := ((Real.hasDerivAt_log ht.ne').const_sub 8).rpow_const
    (p := (-1 / 256 : ℝ)) (Or.inl hb)
  convert h using 1
  · rfl
  · rw [Real.rpow_sub_one hb]
    unfold logProfile
    field_simp

/-- A uniform derivative bound in the innermost comparison region. -/
theorem logProfile_derivative_bound {s t : ℝ} (hs : 0 < s)
    (hT : 16 ≤ 8 - Real.log s) (ht : t ∈ Icc (s / 2) (3 * s / 2)) :
    |logProfile t / (256 * t * (8 - Real.log t))| ≤ 4 * logProfile s / s := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht5 : t ≤ 5 * s := by linarith [ht.2]
  have hlog5 : Real.log (5 * s) = Real.log 5 + Real.log s :=
    Real.log_mul (by norm_num) hs.ne'
  have hlogt : Real.log t ≤ Real.log (5 * s) := Real.log_le_log ht0 ht5
  have hb : 1 ≤ 8 - Real.log t := by linarith [log_five_le_two]
  have hp : logProfile t ≤ 2 * logProfile s :=
    (logProfile_le_logProfile ht0 ht5 (by linarith [log_five_le_two])).trans
      (logProfile_mul_five_le hs hT)
  have hpt : 0 ≤ logProfile t := Real.rpow_nonneg (by linarith) _
  have hps : 0 ≤ logProfile s := Real.rpow_nonneg (by linarith) _
  have hd : s / 2 ≤ 256 * t * (8 - Real.log t) := by
    nlinarith [ht.1, mul_le_mul_of_nonneg_left hb ht0.le]
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2 * logProfile s) / (s / 2) :=
      div_le_div₀ (by positivity) hp (by positivity) hd
    _ = _ := by ring

/-- The profile is Lipschitz on the near-field range with an explicit constant. -/
theorem logProfile_local_lipschitz {s a b : ℝ} (hs : 0 < s)
    (hT : 16 ≤ 8 - Real.log s)
    (ha : a ∈ Icc (s / 2) (3 * s / 2)) (hb : b ∈ Icc (s / 2) (3 * s / 2)) :
    |logProfile a - logProfile b| ≤ (4 * logProfile s / s) * |a - b| := by
  have hder : ∀ t ∈ Icc (s / 2) (3 * s / 2),
      HasDerivWithinAt logProfile (logProfile t / (256 * t * (8 - Real.log t)))
        (Icc (s / 2) (3 * s / 2)) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlogs := Real.log_le_log ht0 (show t ≤ 5 * s by linarith [ht.2])
    rw [Real.log_mul (by norm_num) hs.ne'] at hlogs
    exact (hasDerivAt_logProfile ht0 (by linarith [log_five_le_two])).hasDerivWithinAt
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (s / 2) (3 * s / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder (fun t ht => by simpa only [Real.norm_eq_abs] using
        logProfile_derivative_bound hs hT ht) hb ha

/-- The power estimate for the integrated far-field profile. -/
theorem profile_primitive_difference_le {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) :
    (A ^ (255 / 256 : ℝ) - B ^ (255 / 256 : ℝ)) / (255 / 256 : ℝ) ≤
      (256 / 255 : ℝ) * A ^ (-1 / 256 : ℝ) * (A - B) := by
  have hA : 0 < A := hB.trans_le hBA
  have hpow : A ^ (-1 / 256 : ℝ) ≤ B ^ (-1 / 256 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hB hBA (by norm_num)
  have hid (t : ℝ) (ht : 0 < t) : t ^ (255 / 256 : ℝ) = t * t ^ (-1 / 256 : ℝ) := by
    rw [show (255 / 256 : ℝ) = 1 + (-1 / 256 : ℝ) by norm_num,
      Real.rpow_add ht, Real.rpow_one]
  rw [hid A hA, hid B hB]
  nlinarith [mul_le_mul_of_nonneg_left hpow hB.le]

/-- The radius chosen in Section 7.3 gives the exact local modulus. -/
theorem logProfile_le_at_cutoff {t : ℝ} {j : ℕ} (hj : 0 < j)
    (ht : 0 < t) (hsmall : t ≤ cutoffRadius j) :
    logProfile t ≤ 1 / (2 * (j : ℝ)) := by
  have hjr : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hlog := Real.log_le_log ht hsmall
  rw [cutoffRadius, Real.log_exp] at hlog
  have hbase : (2 * (j : ℝ)) ^ 256 ≤ 8 - Real.log t := by linarith
  have hp : 0 < (2 * (j : ℝ)) ^ 256 := by positivity
  calc
    logProfile t ≤ ((2 * (j : ℝ)) ^ 256) ^ (-1 / 256 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos hp hbase (by norm_num)
    _ = (2 * (j : ℝ)) ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num
    _ = _ := by rw [Real.rpow_neg_one, one_div]

theorem logGapFunction_nonneg {r : ℝ → ℝ} {x : ℝ}
    (hr : 0 ≤ r x) (hr2 : r x ≤ 2) : 0 ≤ logGapFunction r x := by
  unfold logGapFunction
  split_ifs with h
  · exact le_rfl
  · exact (logProfile_pos (lt_of_le_of_ne hr (Ne.symm h)) hr2).le

theorem logGapFunction_le_one {r : ℝ → ℝ} {x : ℝ}
    (hr : 0 ≤ r x) (hr2 : r x ≤ 2) : logGapFunction r x ≤ 1 := by
  unfold logGapFunction
  split_ifs with h
  · norm_num
  · exact logProfile_le_one (lt_of_le_of_ne hr (Ne.symm h)) hr2

theorem logGapFunction_le_at_cutoff {r : ℝ → ℝ} {x : ℝ} {j : ℕ}
    (hj : 0 < j) (hr : 0 ≤ r x) (hsmall : r x ≤ cutoffRadius j) :
    logGapFunction r x ≤ 1 / (2 * (j : ℝ)) := by
  unfold logGapFunction
  split_ifs with h
  · positivity
  · exact logProfile_le_at_cutoff hj (lt_of_le_of_ne hr (Ne.symm h)) hsmall

theorem measurable_logGapFunction {r : ℝ → ℝ} (hr : Measurable r) :
    Measurable (logGapFunction r) := by
  unfold logGapFunction logProfile
  exact Measurable.ite (measurableSet_eq_fun hr measurable_const) measurable_const
    ((measurable_const.sub hr.log).pow_const _)

end Erdos1132.Counterexample
