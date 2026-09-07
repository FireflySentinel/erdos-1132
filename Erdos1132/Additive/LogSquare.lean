import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Local square integrability of the logarithmic kernel

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Interval
namespace Erdos1132

theorem log_sq_le_rpow_bound {t : ℝ} (ht : 0 ≤ t) :
    (Real.log t)^2 ≤ 16 * (t^(1/2 : ℝ) + t^(-1/2 : ℝ)) := by
  by_cases ht0 : t = 0
  · subst t
    norm_num
  have hpow (r : ℝ) : (t^r)^2 = t^(r*2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  by_cases hlog : 0 ≤ Real.log t
  · have hh := Real.log_le_rpow_div ht (show (0 : ℝ) < 1/4 by norm_num)
    have hs := pow_le_pow_left₀ hlog hh 2
    have he : (t^(1/4 : ℝ)/(1/4 : ℝ))^2 = 16*t^(1/2 : ℝ) := by
      rw [div_pow, hpow]
      norm_num
      ring
    rw [he] at hs
    nlinarith [Real.rpow_nonneg ht (-1/2)]
  · have hh := Real.log_le_rpow_div (inv_nonneg.mpr ht) (show (0 : ℝ) < 1/4 by norm_num)
    rw [Real.log_inv, Real.inv_rpow ht, ← Real.rpow_neg ht] at hh
    have hs := pow_le_pow_left₀ (neg_nonneg.mpr (le_of_not_ge hlog)) hh 2
    have he : (t^(-(1/4) : ℝ)/(1/4 : ℝ))^2 = 16*t^(-1/2 : ℝ) := by
      rw [div_pow, hpow]
      norm_num
      ring
    rw [he, neg_sq] at hs
    nlinarith [Real.rpow_nonneg ht (1/2)]

theorem intervalIntegrable_abs_rpow {r a b : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => |x|^r) volume a b := by
  apply intervalIntegrable_of_even (fun x => by rw [abs_neg])
  intro b hb
  apply (intervalIntegrable_rpow' hr (a := 0) (b := b)).congr_uIoo
  intro x hx
  have hx0 : 0 < x := by simpa only [min_eq_left hb.le] using hx.1
  dsimp only
  rw [abs_of_pos hx0]

/-- The logarithmic kernel is square integrable on every bounded interval. -/
theorem intervalIntegrable_log_sq (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume a b := by
  have hb := ((intervalIntegrable_abs_rpow (a := a) (b := b)
    (r := 1/2) (by norm_num)).add
    (intervalIntegrable_abs_rpow (a := a) (b := b) (r := -1/2) (by norm_num))).const_mul 16
  apply hb.mono_fun' ((Real.measurable_log.pow_const 2).aestronglyMeasurable)
  apply ae_of_all
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)), Real.log_abs] using
    log_sq_le_rpow_bound (abs_nonneg x)

theorem integrableOn_log_sq (a b : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.log x)^2) (Icc a b) := by
  by_cases hab : a ≤ b
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (intervalIntegrable_log_sq a b)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

theorem integrableOn_log_sub_sq (a b c : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.log (x-c))^2) (Icc a b) := by
  by_cases hab : a ≤ b
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    simpa only [sub_add_cancel] using
      (intervalIntegrable_log_sq (a-c) (b-c)).comp_sub_right c
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

/-- Translating the singularity within `[-1,1]` leaves a common square-integral
bound on `[-2,2]`. -/
theorem integral_log_sub_sq_le {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    (∫ x in Icc (-2 : ℝ) 2, (Real.log (x-c))^2) ≤
      ∫ x in Icc (-3 : ℝ) 3, (Real.log x)^2 := by
  have heq : (∫ x in Icc (-2 : ℝ) 2, (Real.log (x-c))^2) =
      ∫ x in Icc (-2-c) (2-c), (Real.log x)^2 := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (-2 : ℝ) ≤ 2 by norm_num),
      ← intervalIntegral.integral_of_le (show -2-c ≤ 2-c by linarith)]
    exact intervalIntegral.integral_comp_sub_right (fun x : ℝ => (Real.log x)^2) c
  rw [heq]
  apply setIntegral_mono_set (integrableOn_log_sq (-3) 3)
    (ae_of_all _ fun x => sq_nonneg _) (ae_of_all _ fun x hx => ?_)
  exact ⟨by linarith [hc.2, hx.1], by linarith [hc.1, hx.2]⟩

end Erdos1132
