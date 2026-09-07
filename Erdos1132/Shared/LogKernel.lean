import Erdos1132.Shared.TruncatedPotential
import Mathlib.MeasureTheory.Integral.Prod

/-! # The logarithmic average of Poisson kernels

Paper: Shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set

namespace Erdos1132

def logKernel (h η t : ℝ) : ℝ := (∫ s in Icc η 1, poissonKernel (s - h) t / s) / (-Real.log η)

theorem measurable_poissonKernel : Measurable (fun p : ℝ × ℝ => poissonKernel p.1 p.2) := by
  unfold poissonKernel
  fun_prop

theorem poissonKernel_le {h : ℝ} (hh : 0 < h) (t : ℝ) :
    poissonKernel h t ≤ 1 / (Real.pi * h) := by
  unfold poissonKernel
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Real.pi_pos, sq_nonneg t]

theorem integrableOn_inverse {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun s : ℝ => 1 / s) (Icc η 1) := by
  apply ContinuousOn.integrableOn_Icc
  exact continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt (hη.trans_le hs.1))

theorem integral_inverse_Icc {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (∫ s in Icc η 1, 1 / s) = -Real.log η := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hη1,
    integral_one_div_of_pos hη zero_lt_one]
  simp

theorem integrable_poisson_mixture {h η : ℝ} (hη : 0 < η) (hhη : h < η) :
    Integrable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) p.2 / p.1)
      ((volume.restrict (Icc η 1)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) p.2 / p.1) := by
    unfold poissonKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (integrable_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1)).le).div_const s
  · apply (integrableOn_inverse hη).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hsh : 0 < s - h := sub_pos.mpr (hhη.trans_le hs.1)
    have hs0 : 0 < s := hη.trans_le hs.1
    simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (poissonKernel_pos hsh _).le hs0.le),
      integral_div, integral_poissonKernel hsh]

theorem integrable_logKernel {h η : ℝ} (hη : 0 < η) (hhη : h < η) :
    Integrable (logKernel h η) :=
  (integrable_poisson_mixture hη hhη).integral_prod_right.div_const _

theorem logKernel_nonneg {h η : ℝ} (hη : 0 < η) (hhη : h < η) (hη1 : η < 1) (t : ℝ) :
    0 ≤ logKernel h η t := by
  apply div_nonneg _ (neg_nonneg.mpr (Real.log_nonpos hη.le hη1.le))
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact div_nonneg (poissonKernel_pos (sub_pos.mpr (hhη.trans_le hs.1)) t).le (hη.le.trans hs.1)

theorem logKernel_neg (h η t : ℝ) : logKernel h η (-t) = logKernel h η t := by
  simp only [logKernel, poissonKernel_neg]

theorem integral_logKernel {h η : ℝ} (hη : 0 < η) (hhη : h < η) (hη1 : η < 1) :
    (∫ t, logKernel h η t) = 1 := by
  simp only [logKernel]
  rw [integral_div,
    ← integral_integral_swap (integrable_poisson_mixture hη hhη)]
  have he : (∫ s in Icc η 1, ∫ t, poissonKernel (s - h) t / s) = -Real.log η := by
    rw [← integral_inverse_Icc hη hη1.le]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [integral_div, integral_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1))]
  rw [he, div_self (ne_of_gt (neg_pos.mpr (Real.log_neg hη hη1)))]

theorem poisson_mixture_bound {h η s : ℝ} (hη : 0 < η) (hhη : h < η) (hs : η ≤ s) (t : ℝ) :
    poissonKernel (s - h) t / s ≤ 1 / (Real.pi * (η - h) * η) := by
  have hs0 := hη.trans_le hs
  have hsh := sub_pos.mpr (hhη.trans_le hs)
  calc
    _ ≤ (1 / (Real.pi * (s - h))) / s :=
      div_le_div_of_nonneg_right (poissonKernel_le hsh t) hs0.le
    _ = 1 / (Real.pi * (s - h) * s) := by rw [div_div]
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      · exact hs
      · exact hη.le
      · positivity)

theorem continuous_logKernel {h η : ℝ} (hη : 0 < η) (hhη : h < η) :
    Continuous (logKernel h η) := by
  apply Continuous.div_const
  apply continuous_of_dominated (bound := fun _ => 1 / (Real.pi * (η - h) * η))
  · intro t
    have hm : Measurable (fun s => poissonKernel (s - h) t / s) := by
      unfold poissonKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · intro t
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (poissonKernel_pos (sub_pos.mpr (hhη.trans_le hs.1)) t).le (hη.le.trans hs.1))]
    exact poisson_mixture_bound hη hhη hs.1 t
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (continuous_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1))).div_const s

end Erdos1132
