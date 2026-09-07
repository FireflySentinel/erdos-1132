import Erdos1132.Counterexample.LogProfile
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The decreasing far-field weight and its exact primitive -/

noncomputable section

open Set MeasureTheory

namespace Erdos1132.Counterexample

def farLog (t : ℝ) : ℝ := 8 - Real.log (5 / 4) - Real.log t

def farWeight (t : ℝ) : ℝ := (farLog t) ^ (-1 / 256 : ℝ) / t

def farPrimitive (t : ℝ) : ℝ := -(256 / 255 : ℝ) * (farLog t) ^ (255 / 256 : ℝ)

theorem farLog_eq {t : ℝ} (ht : 0 < t) :
    farLog t = 8 - Real.log (5 * t / 4) := by
  rw [show 5 * t / 4 = (5 / 4 : ℝ) * t by ring,
    Real.log_mul (by norm_num) ht.ne']
  unfold farLog
  ring

theorem farWeight_eq {t : ℝ} (ht : 0 < t) :
    farWeight t = logProfile (5 * t / 4) / t := by
  rw [farWeight, farLog_eq ht, logProfile]

theorem farLog_lower_bound {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : 6 ≤ farLog t := by
  have hlog := Real.log_le_sub_one_of_pos ht
  have hlogc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  unfold farLog
  linarith

theorem hasDerivAt_farLog {t : ℝ} (ht : 0 < t) :
    HasDerivAt farLog (-1 / t) t := by
  convert! (Real.hasDerivAt_log ht.ne').const_sub (8 - Real.log (5 / 4)) using 1
  simp [neg_div]

theorem hasDerivAt_farPrimitive {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) :
    HasDerivAt farPrimitive (farWeight t) t := by
  have hL : 0 < farLog t := lt_of_lt_of_le (by norm_num) (farLog_lower_bound ht ht2)
  have h := ((hasDerivAt_farLog ht).rpow_const (p := (255 / 256 : ℝ))
    (Or.inl hL.ne')).const_mul (-(256 / 255 : ℝ))
  convert! h using 1
  norm_num
  unfold farWeight
  ring_nf

theorem hasDerivAt_farWeight {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) :
    HasDerivAt farWeight
      ((farLog t) ^ (-1 / 256 : ℝ) / t ^ 2 * (1 / (256 * farLog t) - 1)) t := by
  have hL : 0 < farLog t := lt_of_lt_of_le (by norm_num) (farLog_lower_bound ht ht2)
  have h := ((hasDerivAt_farLog ht).rpow_const (p := (-1 / 256 : ℝ))
    (Or.inl hL.ne')).div (hasDerivAt_id t) ht.ne'
  convert! h using 1
  dsimp
  rw [Real.rpow_sub_one hL.ne']
  field_simp

theorem farWeight_pos {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : 0 < farWeight t := by
  exact div_pos (Real.rpow_pos_of_pos
    (lt_of_lt_of_le (by norm_num) (farLog_lower_bound ht ht2)) _) ht

theorem farWeight_continuousOn {a b : ℝ} (ha : 0 < a) (hb : b ≤ 2) :
    ContinuousOn farWeight (Icc a b) := by
  intro t ht
  exact (hasDerivAt_farWeight (ha.trans_le ht.1) (ht.2.trans hb)).continuousAt.continuousWithinAt

/-- The monotonicity required by the cumulative radial comparison. -/
theorem farWeight_strictAntiOn {a b : ℝ} (ha : 0 < a) (hb : b ≤ 2) :
    StrictAntiOn farWeight (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) (farWeight_continuousOn ha hb)
  intro t ht
  have htI : t ∈ Icc a b := interior_subset ht
  have ht0 := ha.trans_le htI.1
  have ht2 := htI.2.trans hb
  have hL := farLog_lower_bound ht0 ht2
  rw [(hasDerivAt_farWeight ht0 ht2).deriv]
  apply mul_neg_of_pos_of_neg
  · exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (sq_pos_of_pos ht0)
  · apply sub_neg.mpr
    apply (div_lt_one (by linarith : 0 < 256 * farLog t)).mpr
    linarith

/-- Exact integration of the far-field weight. -/
theorem integral_farWeight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ t in a..b, farWeight t) =
      ((farLog a) ^ (255 / 256 : ℝ) - (farLog b) ^ (255 / 256 : ℝ)) / (255 / 256 : ℝ) := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt farPrimitive (farWeight t) t := by
    rw [uIcc_of_le hab]
    intro t ht
    exact hasDerivAt_farPrimitive (ha.trans_le ht.1) (ht.2.trans hb)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((farWeight_continuousOn ha hb).intervalIntegrable_of_Icc hab)]
  unfold farPrimitive
  ring

/-- The logarithmic average bound used on each side of the query point. -/
theorem integral_farWeight_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ t in a..b, farWeight t) ≤
      (256 / 255 : ℝ) * logProfile (5 * a / 4) * Real.log (b / a) := by
  rw [integral_farWeight ha hab hb]
  have hBA : farLog b ≤ farLog a := by
    unfold farLog
    linarith [Real.log_le_log ha hab]
  have hB : 0 < farLog b := lt_of_lt_of_le (by norm_num) (farLog_lower_bound (ha.trans_le hab) hb)
  have h := profile_primitive_difference_le hB hBA
  have heq : farLog a - farLog b = Real.log (b / a) := by
    rw [Real.log_div (ha.trans_le hab).ne' ha.ne']
    unfold farLog
    ring
  rw [heq, farLog_eq ha] at h
  simpa only [farLog_eq ha, logProfile] using h

end Erdos1132.Counterexample
