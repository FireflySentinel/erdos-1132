import Erdos1132.BoundaryMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-! # The Poisson extension of a logarithmic singularity -/

noncomputable section
open MeasureTheory Set Filter Complex Metric Real
open scoped Topology
namespace Erdos1132

theorem integrable_cauchy_of_circleIntegrable {f : ℂ → ℝ} {r : ℝ}
    (hf : CircleIntegrable f 0 r) :
    Integrable (fun t => poissonKernel 1 t * f ((r : ℂ) * inverseCayley t)) := by
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_cayleyAngle t).hasDerivWithinAt) injective_cayleyAngle.injOn
    (fun θ => f (circleMap 0 r θ))
  simp only [image_univ, range_cayleyAngle, smul_eq_mul] at hj
  have hcirc : IntegrableOn (fun θ => f (circleMap 0 r θ)) (Ioo 0 (2*Real.pi)) :=
    hf.1.mono_set Ioo_subset_Ioc_self
  have hi := (hj.mp hcirc).const_mul (1/(2*Real.pi))
  rw [Measure.restrict_univ] at hi
  convert hi using 1
  funext t
  rw [circleMap_cayleyAngle_radius, abs_of_pos (show 0 < 2/(1+t^2) by positivity)]
  unfold poissonKernel
  field_simp
  ring

theorem circleAverage_log_norm_linear {A B : ℂ} (hB : B ≠ 0) (hnorm : ‖A‖ = ‖B‖) :
    Real.circleAverage (fun z => Real.log ‖A+B*z‖) 0 1 = Real.log ‖B‖ := by
  have heq : (fun z => Real.log ‖A+B*z‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) 1)]
      (fun z => Real.log ‖B‖ + Real.log ‖z-(-A/B)‖) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (-A/B)] with z hz
    have hzne : z ≠ -A/B := hz
    have hfac : A+B*z = B*(z-(-A/B)) := by field_simp; ring
    rw [hfac, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hB)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzne))]
  have hz : ‖-A/B‖ = 1 := by rw [norm_div, norm_neg, hnorm, div_self (norm_ne_zero_iff.mpr hB)]
  calc
    _ = Real.circleAverage (fun z => Real.log ‖B‖ + Real.log ‖z-(-A/B)‖) 0 1 :=
      Real.circleAverage_congr_codiscreteWithin (by simpa only [abs_one] using heq) one_ne_zero
    _ = _ := by
      rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
        (circleIntegrable_log_norm_sub_const 1), Real.circleAverage_const,
        circleAverage_log_norm_sub_const₁ hz, add_zero]

theorem circleAverage_log_norm_linear_div {A B : ℂ}
    (hB : B ≠ 0) (hnorm : ‖A‖ = ‖B‖) :
    Real.circleAverage (fun z => Real.log ‖(A+B*z)/(1-z)‖) 0 1 = Real.log ‖A‖ := by
  have heq : (fun z => Real.log ‖(A+B*z)/(1-z)‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) 1)]
      (fun z => Real.log ‖A+B*z‖ - Real.log ‖z-1‖) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (-A/B),
      compl_singleton_mem_codiscreteWithin (1 : ℂ)] with z hz hz1
    have hnum : A+B*z ≠ 0 := by
      intro he
      apply hz
      apply (eq_div_iff hB).mpr
      linear_combination he
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hnum)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))), norm_sub_rev (1 : ℂ) z]
  have hnumInt : CircleIntegrable (fun z => Real.log ‖A+B*z‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (fun z _ => by fun_prop)
  calc
    _ = Real.circleAverage (fun z => Real.log ‖A+B*z‖ - Real.log ‖z-1‖) 0 1 :=
      Real.circleAverage_congr_codiscreteWithin (by simpa only [abs_one] using heq) one_ne_zero
    _ = _ := by
      rw [Real.circleAverage_fun_sub hnumInt (circleIntegrable_log_norm_sub_const 1),
        circleAverage_log_norm_linear hB hnorm,
        circleAverage_log_norm_sub_const₁ (norm_one : ‖(1 : ℂ)‖ = 1), sub_zero, hnorm]

def logarithmicCayley (x h a : ℝ) (w : ℂ) : ℂ :=
  (((x-a : ℝ) : ℂ) + h*I + (-((x-a : ℝ) : ℂ) + h*I)*w)/(1-w)

theorem logarithmicCayley_inverse (x h a t : ℝ) :
    logarithmicCayley x h a (inverseCayley t) = (x+h*t-a : ℝ) := by
  unfold logarithmicCayley inverseCayley
  push_cast
  field_simp [inverseCayley_denom_ne_zero t]
  simp
  ring

theorem logarithmicCayley_coefficients {x h a : ℝ} (hh : 0 < h) :
    (-((x-a : ℝ) : ℂ) + h*I) ≠ 0 ∧
      ‖((x-a : ℝ) : ℂ)+h*I‖ = ‖-((x-a : ℝ) : ℂ)+h*I‖ := by
  constructor
  · intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hh.ne' hi
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

theorem integrable_cauchy_log_affine {h : ℝ} (_hh : 0 < h) (x a : ℝ) :
    Integrable (fun t => poissonKernel 1 t * Real.log (x+h*t-a)) := by
  have hmer : MeromorphicOn (logarithmicCayley x h a) (sphere 0 |(1 : ℝ)|) := by
    intro z _
    unfold logarithmicCayley
    fun_prop
  have hi := integrable_cauchy_of_circleIntegrable hmer.circleIntegrable_log_norm
  simpa only [Complex.ofReal_one, one_mul, logarithmicCayley_inverse,
    Complex.norm_real, Real.norm_eq_abs, Real.log_abs] using hi

/-- The Cauchy integral of a real logarithmic singularity, in affine coordinates. -/
theorem integral_cauchy_log_affine {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    (∫ t, poissonKernel 1 t * Real.log (x+h*t-a)) =
      Real.log ‖((x-a : ℝ) : ℂ)+h*I‖ := by
  have he := circleAverage_log_norm_linear_div
    (logarithmicCayley_coefficients (x := x) (a := a) hh).1
    (logarithmicCayley_coefficients (x := x) (a := a) hh).2
  rw [circleAverage_eq_cauchy_integral] at he
  change (∫ t, poissonKernel 1 t * Real.log ‖logarithmicCayley x h a ((1 : ℂ) * inverseCayley t)‖) = _ at he
  simpa only [one_mul,
    logarithmicCayley_inverse, Complex.norm_real, Real.norm_eq_abs, Real.log_abs] using he

/-- The Poisson extension of `log |·-a|` is `log |x+ih-a|`. -/
theorem integral_poisson_log {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    (∫ y, poissonKernel h (y-x) * Real.log (y-a)) =
      Real.log ‖((x-a : ℝ) : ℂ)+h*I‖ := by
  rw [poisson_integral_affine hh]
  exact integral_cauchy_log_affine hh x a

theorem integrable_poisson_affine_iff {h : ℝ} (hh : 0 < h) (x : ℝ) (f : ℝ → ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * f y) ↔
      Integrable (fun t => poissonKernel 1 t * f (x+h*t)) := by
  have hinj : Function.Injective (fun t : ℝ => x+h*t) := by
    intro s t he
    exact (mul_left_cancel₀ hh.ne') (add_left_cancel he)
  have hsurj : Function.Surjective (fun t : ℝ => x+h*t) := by
    intro y
    refine ⟨(y-x)/h, ?_⟩
    field_simp
    ring
  have hd (t : ℝ) : HasDerivAt (fun t => x+h*t) h t := by
    convert! ((hasDerivAt_id t).const_mul h).const_add x using 1
    simp
  have he := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hd t).hasDerivWithinAt) hinj.injOn
    (fun y => poissonKernel h (y-x) * f y)
  simp only [image_univ, hsurj.range_eq, IntegrableOn, Measure.restrict_univ,
    abs_of_pos hh, smul_eq_mul] at he
  convert he using 2
  funext t
  unfold poissonKernel
  field_simp
  ring

theorem integrable_poisson_log {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * Real.log (y-a)) :=
  (integrable_poisson_affine_iff hh x _).mpr (integrable_cauchy_log_affine hh x a)

end Erdos1132
