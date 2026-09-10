import Erdos1132.Additive.QuantitativeKernel
import Erdos1132.Additive.PoissonPotential

/-! # Averaging the Poisson kernel between two comparable heights

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Real Filter Complex
namespace Erdos1132

def averagedPoissonKernel (h t : ℝ) : ℝ :=
  (∫ s in Icc h (2*h), poissonKernel s t)/h

theorem integrable_averagedPoisson_product {h : ℝ} (hh : 0 < h) :
    Integrable (fun p : ℝ × ℝ => poissonKernel p.1 p.2)
      ((volume.restrict (Icc h (2*h))).prod volume) := by
  apply (integrable_prod_iff measurable_poissonKernel.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact integrable_poissonKernel (hh.trans_le hs.1).le
  · apply (integrable_const (1 : ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simp only [Real.norm_eq_abs, abs_of_pos (poissonKernel_pos (hh.trans_le hs.1) _),
      integral_poissonKernel (hh.trans_le hs.1)]

theorem integrable_averagedPoissonKernel {h : ℝ} (hh : 0 < h) :
    Integrable (averagedPoissonKernel h) :=
  (integrable_averagedPoisson_product hh).integral_prod_right.div_const h

theorem averagedPoissonKernel_nonneg {h : ℝ} (hh : 0 < h) (t : ℝ) :
    0 ≤ averagedPoissonKernel h t := by
  apply div_nonneg _ hh.le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact (poissonKernel_pos (hh.trans_le hs.1) _).le

theorem averagedPoissonKernel_neg (h t : ℝ) :
    averagedPoissonKernel h (-t) = averagedPoissonKernel h t := by
  simp only [averagedPoissonKernel, poissonKernel_neg]

theorem integral_averagedPoissonKernel {h : ℝ} (hh : 0 < h) :
    (∫ t, averagedPoissonKernel h t) = 1 := by
  unfold averagedPoissonKernel
  rw [integral_div, ← integral_integral_swap (integrable_averagedPoisson_product hh)]
  have he : (∫ s in Icc h (2*h), ∫ t, poissonKernel s t) = h := by
    calc
      _ = ∫ _s in Icc h (2*h), (1 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact integral_poissonKernel (hh.trans_le hs.1)
      _ = h := by simp [Measure.real, Real.volume_Icc, show 2*h-h = h by ring, hh.le]
  rw [he, div_self hh.ne']

theorem averagedPoissonKernel_operator {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, |f t| ≤ M) :
    (∫ t, averagedPoissonKernel h t*f t) =
      (∫ s in Icc h (2*h), ∫ t, poissonKernel s t*f t)/h := by
  have hbase := integrable_averagedPoisson_product hh
  have hi : Integrable (fun p : ℝ × ℝ => poissonKernel p.1 p.2*f p.2)
      ((volume.restrict (Icc h (2*h))).prod volume) :=
    hbase.mul_bdd (hf.comp measurable_snd).aestronglyMeasurable (ae_of_all _ (fun p => hM p.2))
  have he (t : ℝ) : averagedPoissonKernel h t*f t =
      (∫ s in Icc h (2*h), poissonKernel s t*f t)/h := by
    rw [integral_mul_const, averagedPoissonKernel]
    ring
  simp_rw [he]
  rw [integral_div, ← integral_integral_swap hi]

theorem averagedPoissonKernel_setIntegral {h : ℝ} (hh : 0 < h)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ t in E, averagedPoissonKernel h t) =
      (∫ s in Icc h (2*h), ∫ t in E, poissonKernel s t)/h := by
  have he := averagedPoissonKernel_operator hh (measurable_const.indicator hE)
    (M := 1) (f := E.indicator (fun _ => 1)) (fun t => by by_cases ht : t ∈ E <;> simp [ht])
  have hid (g : ℝ → ℝ) : (fun t => g t*E.indicator (fun _ => 1) t) = E.indicator g := by
    ext t
    by_cases ht : t ∈ E <;> simp [ht]
  simp_rw [hid, integral_indicator hE] at he
  exact he

theorem averagedPoissonKernel_tail {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (∫ t in (Icc (-δ) δ)ᶜ, averagedPoissonKernel h t) ≤ 4*h/(Real.pi*δ) := by
  rw [averagedPoissonKernel_setIntegral hh measurableSet_Icc.compl]
  have hi := (integrable_averagedPoisson_product hh).mono_measure
    (μ := (volume.restrict (Icc h (2*h))).prod (volume.restrict (Icc (-δ) δ)ᶜ))
    (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hmono : (∫ s in Icc h (2*h), ∫ t in (Icc (-δ) δ)ᶜ, poissonKernel s t) ≤
      ∫ _s in Icc h (2*h), 4*h/(Real.pi*δ) := by
    apply setIntegral_mono_on hi.integral_prod_left (integrable_const _) measurableSet_Icc
    intro s hs
    exact (poissonKernel_tail_bound (hh.trans_le hs.1) hδ).trans
      (div_le_div_of_nonneg_right (by linarith [hs.2]) (mul_pos Real.pi_pos hδ).le)
  apply (div_le_iff₀ hh).mpr
  have he : (∫ _s in Icc h (2*h), 4*h/(Real.pi*δ)) = h*(4*h/(Real.pi*δ)) := by
    simp [Measure.real, Real.volume_Icc, show 2*h-h = h by ring, hh.le]
  rw [he] at hmono
  nlinarith

/-- The averaged kernel is exactly a difference of logarithmic potentials. -/
theorem averagedPoissonKernel_log {h : ℝ} (hh : 0 < h) (t : ℝ) :
    averagedPoissonKernel h t =
      (Real.log ‖(t : ℂ)+(2*h : ℝ)*I‖-Real.log ‖(t : ℂ)+h*I‖)/(Real.pi*h) := by
  have hd (s : ℝ) (hs : s ∈ Icc h (2*h)) :
      HasDerivAt (fun u => Real.log (t^2+u^2)/(2*Real.pi)) (poissonKernel s t) s := by
    have hs0 := hh.trans_le hs.1
    convert! ((((hasDerivAt_id s).pow 2).const_add (t^2)).log
      (by positivity : t^2+s^2 ≠ 0)).div_const (2*Real.pi) using 1
    unfold poissonKernel
    dsimp
    field_simp
  have hc : ContinuousOn (fun s => poissonKernel s t) (Icc h (2*h)) := by
    apply continuousOn_id.div (by fun_prop)
    intro s hs
    have hs0 := hh.trans_le hs.1
    positivity
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by linarith : h ≤ 2*h)] using hs))
    (hc.intervalIntegrable_of_Icc (by linarith))
  have hlog (s : ℝ) : Real.log (t^2+s^2) = 2*Real.log ‖(t : ℂ)+(s : ℝ)*I‖ := by
    have hs : ‖(t : ℂ)+(s : ℝ)*I‖^2 = t^2+s^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, pow_two]
    rw [← hs, Real.log_pow]
    norm_num
  unfold averagedPoissonKernel
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : h ≤ 2*h), he]
  simp_rw [hlog]
  field_simp

end Erdos1132
