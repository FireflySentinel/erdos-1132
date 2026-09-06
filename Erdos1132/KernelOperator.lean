import Erdos1132.LogKernel
import Mathlib.Analysis.Convolution

noncomputable section

open MeasureTheory Set Complex

namespace Erdos1132

theorem integrable_poisson_mixture_translate {h η : ℝ} (hη : 0 < η) (hhη : h < η) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) (x - p.2) / p.1)
      ((volume.restrict (Icc η 1)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) (x - p.2) / p.1) := by
    unfold poissonKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ((integrable_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1)).le).comp_sub_left x).div_const s
  · apply (integrableOn_inverse hη).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hsh : 0 < s - h := sub_pos.mpr (hhη.trans_le hs.1)
    have hs0 : 0 < s := hη.trans_le hs.1
    simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (poissonKernel_pos hsh _).le hs0.le),
      integral_div, integral_sub_left_eq_self, integral_poissonKernel hsh]

theorem logKernel_operator {h η : ℝ} (hη : 0 < η) (hhη : h < η) (x : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    (∫ y, logKernel h η (x - y) * f y) =
      (∫ s in Icc η 1, (∫ y, poissonKernel (s - h) (x - y) * f y) / s) / (-Real.log η) := by
  have hbase := integrable_poisson_mixture_translate hη hhη x
  have hint : Integrable (fun p : ℝ × ℝ =>
      poissonKernel (p.1 - h) (x - p.2) / p.1 * f p.2)
      ((volume.restrict (Icc η 1)).prod volume) := by
    apply (hbase.norm.const_mul M).mono'
    · exact (hbase.aestronglyMeasurable.mul (hf.comp measurable_snd).aestronglyMeasurable)
    · apply ae_of_all
      intro p
      rw [norm_mul]
      calc
        _ ≤ ‖poissonKernel (p.1 - h) (x - p.2) / p.1‖ * M :=
          mul_le_mul_of_nonneg_left (hM p.2) (norm_nonneg _)
        _ = _ := mul_comm _ _
  have he (y : ℝ) : logKernel h η (x - y) * f y =
      (∫ s in Icc η 1, poissonKernel (s - h) (x - y) / s * f y) / (-Real.log η) := by
    rw [integral_mul_const, logKernel]
    ring
  simp_rw [he]
  rw [integral_div, ← integral_integral_swap hint]
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with y
  ring

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem continuous_gamma {h : ℝ} (hh : 0 < h) : Continuous (μ.gamma h) := by
  unfold gamma
  apply continuous_finsetSum
  intro i _
  exact continuous_const.div (by fun_prop) (fun x => ne_of_gt (by positivity))

theorem gamma_le_one_div {h : ℝ} (hh : 0 < h) (x : ℝ) : μ.gamma h x ≤ 1 / h := by
  rw [← μ.neg_im_cauchy h x]
  calc
    _ ≤ |(μ.cauchy ((x : ℂ) + h * I)).im| := neg_le_abs _
    _ ≤ ‖μ.cauchy ((x : ℂ) + h * I)‖ := abs_im_le_norm _
    _ ≤ 1 / h := μ.norm_cauchy_le hh (by simp)

theorem truncatedPotential_operator {h η : ℝ} (hh : 0 < h) (hhη : h < η) (hη1 : η < 1) (x : ℝ) :
    μ.truncatedPotential η x =
      (2 / Real.pi) * (-Real.log η) * ∫ y, logKernel h η (x - y) * μ.gamma h y := by
  have hη : 0 < η := hh.trans hhη
  have hm := logKernel_operator hη hhη x (μ.continuous_gamma hh).measurable
    (fun y => by rw [abs_of_pos (μ.gamma_pos hh y)]; exact μ.gamma_le_one_div hh y)
  rw [hm]
  have he : (∫ s in Icc η 1, (∫ y, poissonKernel (s - h) (x - y) * μ.gamma h y) / s) =
      ∫ s in η..1, μ.gamma s x / s := by
    rw [intervalIntegral.integral_of_le hη1.le, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [← μ.gamma_semigroup hh (hhη.trans_le hs.1)]
  rw [he, truncatedPotential]
  have hl : Real.log η ≠ 0 := (Real.log_neg hη hη1).ne
  field_simp

end AtomicProbability
end Erdos1132
