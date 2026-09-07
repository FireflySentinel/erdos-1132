import Erdos1132.RieszMass
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Uniform logarithmic asymptotics of Riesz convolution -/

noncomputable section
open MeasureTheory Set Real
namespace Erdos1132

def rieszConvolution (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, rieszKernel ε (x-y)*f y

theorem measurable_rieszConvolution {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Measurable f) : Measurable (rieszConvolution ε f) := by
  exact ((((continuous_rieszKernel hε).measurable.comp (measurable_fst.sub measurable_snd)).mul
    (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right').measurable

theorem rieszConvolution_bound {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    |rieszConvolution ε f x| ≤ (1/ε)*(∫ y, |f y|) := by
  calc
    _ ≤ ∫ y, |rieszKernel ε (x-y)*f y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, (1/ε)*|f y| := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun y => abs_nonneg _)) (hf.abs.const_mul _)
      exact ae_of_all _ (fun y => by
        dsimp only
        rw [abs_mul, abs_of_pos (rieszKernel_pos hε _)]
        exact mul_le_mul_of_nonneg_right (rieszKernel_le_diagonal hε _) (abs_nonneg _))
    _ = _ := integral_const_mul _ _

theorem integrable_riesz_self_energy {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f) :
    Integrable (fun x => f x*rieszConvolution ε f x) := by
  apply hf.mul_bdd (measurable_rieszConvolution hε hfm).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using rieszConvolution_bound hε hf x)

theorem rieszKernel_mul_abs_le_one {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    rieszKernel ε t * |t| ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  calc
    _ ≤ (1/|t|)*|t| := mul_le_mul_of_nonneg_right (rieszKernel_le_inverse_distance ht) (abs_nonneg _)
    _ = 1 := by field_simp

theorem integrable_riesz_convolution {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun t => rieszKernel ε t*f (x-t)) := by
  apply (hf.comp_sub_left x).bdd_mul (continuous_rieszKernel hε).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_pos (rieszKernel_pos hε _)]
    exact rieszKernel_le_diagonal hε t)

theorem riesz_convolution_mass_error {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : Integrable f)
    (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) (x : ℝ) :
    |(∫ t, rieszKernel ε t*f (x-t))-f x*(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)| ≤
      2*L+∫ t, |f t| := by
  let I := Icc (-1:ℝ) 1
  have hki : Integrable (I.indicator (rieszKernel ε)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((continuous_rieszKernel hε).continuousOn.integrableOn_compact isCompact_Icc)
  have hfi := integrable_riesz_convolution hε hf x
  let g (t : ℝ) := rieszKernel ε t*f (x-t)-f x*I.indicator (rieszKernel ε) t
  have hgi : Integrable g := hfi.sub (hki.const_mul _)
  have hb (t : ℝ) : |g t| ≤ L*I.indicator (fun _ => (1:ℝ)) t+|f (x-t)| := by
    by_cases ht : t ∈ I
    · dsimp only [g]
      rw [indicator_of_mem ht, indicator_of_mem ht]
      have he : rieszKernel ε t*f (x-t)-f x*rieszKernel ε t =
          rieszKernel ε t*(f (x-t)-f x) := by ring
      rw [he, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
      have hdiff : |f (x-t)-f x| ≤ L*|t| := by
        simpa only [sub_sub_cancel_left, abs_neg] using hlip (x-t) x
      calc
        _ ≤ rieszKernel ε t*(L*|t|) := mul_le_mul_of_nonneg_left hdiff (rieszKernel_pos hε _).le
        _ = L*(rieszKernel ε t*|t|) := by ring
        _ ≤ L*1 := mul_le_mul_of_nonneg_left (rieszKernel_mul_abs_le_one hε t) hL
        _ ≤ _ := by nlinarith [abs_nonneg (f (x-t))]
    · have ht1 : 1 < |t| := lt_of_not_ge (fun h => ht (abs_le.mp h))
      have hk1 : rieszKernel ε t ≤ 1 :=
        (rieszKernel_le_inverse_distance (by intro h; rw [h, abs_zero] at ht1; linarith)).trans
          (by simpa using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) ht1.le))
      dsimp only [g]
      rw [indicator_of_notMem ht, indicator_of_notMem ht]
      simp only [mul_zero, sub_zero, zero_add, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
      simpa using mul_le_mul_of_nonneg_right hk1 (abs_nonneg (f (x-t)))
  have hbint : Integrable (fun t => L*I.indicator (fun _ => (1:ℝ)) t+|f (x-t)|) := by
    exact ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)).const_mul L |>.add
      (hf.comp_sub_left x).abs
  have he : (∫ t, g t) = (∫ t, rieszKernel ε t*f (x-t))-
      f x*(∫ t in I, rieszKernel ε t) := by
    rw [show g = (fun t => rieszKernel ε t*f (x-t)-f x*I.indicator (rieszKernel ε) t) from rfl,
      integral_sub hfi (hki.const_mul _), integral_const_mul, integral_indicator measurableSet_Icc]
  rw [← he]
  calc
    _ ≤ ∫ t, |g t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, L*I.indicator (fun _ => (1:ℝ)) t+|f (x-t)| := integral_mono hgi.abs hbint hb
    _ = _ := by
      rw [integral_add (((integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const isCompact_Icc.measure_ne_top)).const_mul L) (hf.comp_sub_left x).abs,
        integral_const_mul, integral_indicator measurableSet_Icc,
        integral_sub_left_eq_self (fun t => |f t|) volume x]
      simp [I]
      ring

theorem riesz_convolution_log_error {ε M L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Integrable f) (hM : ∀ t, |f t| ≤ M)
    (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) (x : ℝ) :
    |(∫ y, rieszKernel ε (x-y)*f y)-2*Real.log (1/ε)*f x| ≤
      2*L+(∫ t, |f t|)+2*M*Real.log 3 := by
  have he : (∫ y, rieszKernel ε (x-y)*f y) = ∫ t, rieszKernel ε t*f (x-t) := by
    have he := integral_sub_left_eq_self (fun y => rieszKernel ε (x-y)*f y) volume x
    simpa only [sub_sub_cancel] using he.symm
  rw [he]
  have h1 := riesz_convolution_mass_error hε hL hf hlip x
  have h2 := mul_le_mul (hM x) (integral_rieszKernel_unit_error hε hε1)
    (abs_nonneg _) ((abs_nonneg (f 0)).trans (hM 0))
  have hsplit := abs_add_le
    ((∫ t, rieszKernel ε t*f (x-t))-f x*(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t))
    (f x*((∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)-2*Real.log (1/ε)))
  rw [abs_mul] at hsplit
  have hident : ((∫ t, rieszKernel ε t*f (x-t))-f x*(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)) +
      f x*((∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)-2*Real.log (1/ε)) =
      (∫ t, rieszKernel ε t*f (x-t))-2*Real.log (1/ε)*f x := by ring
  rw [hident] at hsplit
  nlinarith

end Erdos1132
