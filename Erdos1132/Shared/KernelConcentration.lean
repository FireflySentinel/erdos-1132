import Erdos1132.Shared.KernelOperator
import Erdos1132.Shared.Scales

/-! # Concentration of Poisson and logarithmic kernels

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos1132

theorem arctan_le_self_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  have hf : Continuous (fun s : ℝ => 1 / (1 + s ^ 2)) :=
    continuous_const.div (by fun_prop) (fun s => ne_of_gt (by positivity))
  have he := integral_one_div_one_add_sq (a := 0) (b := t)
  simp only [Real.arctan_zero, sub_zero] at he
  rw [← he]
  calc
    _ ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on ht (hf.intervalIntegrable 0 t) intervalIntegrable_const
      intro s _
      exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg s])
    _ = t := by simp

theorem poissonKernel_tail_bound {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (∫ t in (Icc (-δ) δ)ᶜ, poissonKernel h t) ≤ 2 * h / (Real.pi * δ) := by
  rw [setIntegral_compl measurableSet_Icc (integrable_poissonKernel hh.le), integral_poissonKernel hh,
    integral_poissonKernel_Icc hh (by linarith)]
  rw [neg_div, Real.arctan_neg]
  have hi := Real.arctan_inv_of_pos (div_pos hδ hh)
  rw [inv_div] at hi
  have hb := arctan_le_self_nonneg (div_nonneg hh.le hδ.le)
  rw [hi] at hb
  have hb' := (le_div_iff₀ hδ).mp hb
  apply (le_div_iff₀ (mul_pos Real.pi_pos hδ)).mpr
  field_simp
  nlinarith

theorem logKernel_setIntegral {h η : ℝ} (hη : 0 < η) (hhη : h < η)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ t in E, logKernel h η t) =
      (∫ s in Icc η 1, (∫ t in E, poissonKernel (s - h) t) / s) / (-Real.log η) := by
  have he := logKernel_operator hη hhη 0 (f := E.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hE) (M := 1) (fun y => by
      by_cases hy : y ∈ E <;> simp [hy])
  simp only [zero_sub, logKernel_neg, poissonKernel_neg] at he
  have hid (f : ℝ → ℝ) : (fun y => f y * E.indicator (fun _ => (1 : ℝ)) y) = E.indicator f := by
    funext y
    by_cases hy : y ∈ E <;> simp [hy]
  simp_rw [hid, integral_indicator hE] at he
  exact he

theorem logKernel_tail_bound {h η δ : ℝ} (hh : 0 ≤ h) (hη : 0 < η)
    (hhη : h < η) (hη1 : η < 1) (hδ : 0 < δ) :
    (∫ t in (Icc (-δ) δ)ᶜ, logKernel h η t) ≤
      (2 / (Real.pi * δ)) / (-Real.log η) := by
  rw [logKernel_setIntegral hη hhη measurableSet_Icc.compl]
  apply div_le_div_of_nonneg_right _ (neg_nonneg.mpr (Real.log_nonpos hη.le hη1.le))
  have hint : IntegrableOn (fun s => (∫ t in (Icc (-δ) δ)ᶜ, poissonKernel (s - h) t) / s)
      (Icc η 1) := by
    have hm := (integrable_poisson_mixture hη hhη).mono_measure
      (μ := (volume.restrict (Icc η 1)).prod (volume.restrict (Icc (-δ) δ)ᶜ))
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hi := hm.integral_prod_left
    change Integrable _ (volume.restrict (Icc η 1))
    simpa only [integral_div] using hi
  calc
    _ ≤ ∫ _ in Icc η 1, 2 / (Real.pi * δ) := by
      apply setIntegral_mono_on hint (integrable_const _) measurableSet_Icc
      intro s hs
      have hs0 := hη.trans_le hs.1
      have hp := poissonKernel_tail_bound (sub_pos.mpr (hhη.trans_le hs.1)) hδ
      calc
        _ ≤ (2 * (s - h) / (Real.pi * δ)) / s := div_le_div_of_nonneg_right hp hs0.le
        _ ≤ 2 / (Real.pi * δ) := by
          apply (div_le_iff₀ hs0).mpr
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (mul_pos Real.pi_pos hδ).le
          linarith
    _ ≤ 2 / (Real.pi * δ) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      have hc : 0 ≤ 2 / (Real.pi * δ) := by positivity
      nlinarith

theorem tendsto_logKernel_tail {a b δ : ℝ} (hb : 0 < b) (hba : b < a)
    (hδ : 0 < δ) :
    Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, logKernel (height a n) (height b n) t)
      atTop (𝓝 0) := by
  have hl : Tendsto (fun n => -Real.log (height b n)) atTop atTop := by
    simp_rw [neg_log_height]
    exact (Real.tendsto_log_atTop.comp tendsto_rowSize).const_mul_atTop hb
  have hu : Tendsto (fun n => (2 / (Real.pi * δ)) / (-Real.log (height b n))) atTop (𝓝 0) :=
    hl.const_div_atTop _
  apply squeeze_zero (fun n => integral_nonneg fun t =>
    logKernel_nonneg (height_pos b n) (height_antitone hba n) (height_lt_one hb n) t)
    (fun n => logKernel_tail_bound (height_pos a n).le (height_pos b n)
      (height_antitone hba n) (height_lt_one hb n) hδ) hu

end Erdos1132
