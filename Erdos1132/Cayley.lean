import Erdos1132.PoissonKernel
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section

open MeasureTheory Filter Complex Metric Set
open scoped Topology

namespace Erdos1132

def cayley (x h : ℝ) (w : ℂ) : ℂ := x + h * I * (1 + w) / (1 - w)

def inverseCayley (t : ℝ) : ℂ := ((t : ℂ) - I) / ((t : ℂ) + I)

theorem cayley_zero (x h : ℝ) : cayley x h 0 = (x : ℂ) + h * I := by
  simp [cayley]

theorem inverseCayley_denom_ne_zero (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro he
  have := congrArg Complex.im he
  norm_num at this

theorem inverseCayley_ne_one (t : ℝ) : inverseCayley t ≠ 1 := by
  rw [inverseCayley, ne_eq, div_eq_one_iff_eq (inverseCayley_denom_ne_zero t)]
  intro he
  have := congrArg Complex.im he
  norm_num at this

theorem norm_inverseCayley (t : ℝ) : ‖inverseCayley t‖ = 1 := by
  rw [inverseCayley, norm_div]
  have hn : ‖(t : ℂ) - I‖ = ‖(t : ℂ) + I‖ := by
    convert! norm_conj ((t : ℂ) + I) using 1
    simp [sub_eq_add_neg]
  rw [hn, div_self (norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero t))]

theorem cayley_inverseCayley (x h t : ℝ) :
    cayley x h (inverseCayley t) = ((x + h * t : ℝ) : ℂ) := by
  unfold cayley inverseCayley
  push_cast
  field_simp [inverseCayley_denom_ne_zero t]
  ring

theorem cayley_im (x h : ℝ) {w : ℂ} :
    (cayley x h w).im = h * (1 - ‖w‖ ^ 2) / normSq (1 - w) := by
  simp [cayley, div_im, normSq_apply, Complex.sq_norm]
  ring

theorem cayley_im_pos (x : ℝ) {h : ℝ} (hh : 0 < h) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayley x h w).im := by
  rw [cayley_im]
  have hn : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hw1 : 1 - w ≠ 0 := by
    intro he
    have : w = 1 := (sub_eq_zero.mp he).symm
    simp [this] at hw
  exact div_pos (mul_pos hh hn) (normSq_pos.mpr hw1)

theorem analyticAt_cayley (x h : ℝ) {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ (cayley x h) w := by
  unfold cayley
  fun_prop (disch := exact sub_ne_zero.mpr hw.symm)

theorem continuous_inverseCayley : Continuous inverseCayley := by
  unfold inverseCayley
  exact (continuous_ofReal.sub continuous_const).div
    (continuous_ofReal.add continuous_const) inverseCayley_denom_ne_zero

theorem cayley_radial_tendsto (x h t : ℝ) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => cayley x h ((r n : ℂ) * inverseCayley t)) atTop
      (𝓝 ((x + h * t : ℝ) : ℂ)) := by
  have hc := (analyticAt_cayley x h (inverseCayley_ne_one t)).continuousAt
  have ht : Tendsto (fun n => (r n : ℂ) * inverseCayley t) atTop
      (𝓝 (inverseCayley t)) := by simpa using (continuous_ofReal.tendsto 1 |>.comp hr).mul_const (inverseCayley t)
  simpa only [cayley_inverseCayley, Function.comp_def] using hc.tendsto.comp ht

def cayleyAngle (t : ℝ) : ℝ := 2 * Real.arctan t + Real.pi

theorem hasDerivAt_cayleyAngle (t : ℝ) :
    HasDerivAt cayleyAngle (2 / (1 + t ^ 2)) t := by
  convert! ((Real.hasDerivAt_arctan t).const_mul 2).add_const Real.pi using 1
  simp [div_eq_mul_inv]

theorem injective_cayleyAngle : Function.Injective cayleyAngle := by
  intro x y h
  apply Real.arctan_injective
  dsimp [cayleyAngle] at h
  linarith

theorem range_cayleyAngle : range cayleyAngle = Ioo 0 (2 * Real.pi) := by
  ext θ
  constructor
  · rintro ⟨t, rfl⟩
    have ht := Real.arctan_mem_Ioo t
    dsimp [cayleyAngle]
    constructor <;> linarith [ht.1, ht.2]
  · intro hθ
    refine ⟨Real.tan ((θ - Real.pi) / 2), ?_⟩
    dsimp [cayleyAngle]
    rw [Real.arctan_tan (by linarith [hθ.1]) (by linarith [hθ.2])]
    ring

theorem circleMap_cayleyAngle (t : ℝ) :
    circleMap 0 1 (cayleyAngle t) = inverseCayley t := by
  have hs : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hc (θ : ℝ) : circleMap 0 1 θ = ⟨Real.cos θ, Real.sin θ⟩ := by
    apply Complex.ext <;> simp [circleMap, Complex.exp_re, Complex.exp_im]
  rw [hc]
  apply Complex.ext <;> simp [cayleyAngle, inverseCayley,
    Complex.div_re, Complex.div_im, Complex.normSq_apply, Real.cos_add_pi,
    Real.sin_add_pi, Real.cos_two_mul, Real.sin_two_mul,
    Real.cos_arctan, Real.sin_arctan]
  · field_simp
    rw [hs]
    ring
  · field_simp
    rw [hs]
    ring

theorem circleMap_cayleyAngle_radius (r t : ℝ) :
    circleMap 0 r (cayleyAngle t) = (r : ℂ) * inverseCayley t := by
  rw [← circleMap_cayleyAngle t]
  simp [circleMap]

/-- Stereographic parametrization expresses a circle mean as a Cauchy integral. -/
theorem circleAverage_eq_cauchy_integral (f : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage f 0 r = ∫ t, poissonKernel 1 t * f ((r : ℂ) * inverseCayley t) := by
  have hpos (t : ℝ) : 0 < 2 / (1 + t ^ 2) := by positivity
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_cayleyAngle t).hasDerivWithinAt) injective_cayleyAngle.injOn
    (fun θ => f (circleMap 0 r θ))
  simp only [image_univ, range_cayleyAngle, Measure.restrict_univ, smul_eq_mul,
    abs_of_pos (hpos _)] at h
  rw [Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (show 0 ≤ 2 * Real.pi by positivity),
    integral_Ioc_eq_integral_Ioo, h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [circleMap_cayleyAngle_radius]
  unfold poissonKernel
  field_simp
  ring

open InnerProductSpace in
/-- Boundary limits of a bounded harmonic function in stereographic coordinates. -/
theorem harmonic_boundary_cauchy {u : ℂ → ℝ} {M : ℝ}
    (hu : HarmonicOnNhd u (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, |u z| ≤ M)
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Ico 0 1) (b : ℝ → ℝ)
    (hl : ∀ᵐ t, Tendsto (fun n => u ((r n : ℂ) * inverseCayley t)) atTop (𝓝 (b t))) :
    (∫ t, poissonKernel 1 t * b t) = u 0 := by
  have hm (n : ℕ) (t : ℝ) : (r n : ℂ) * inverseCayley t ∈ ball (0 : ℂ) 1 := by
    simp [mem_ball, dist_eq_norm, norm_inverseCayley,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr n).1, (hr n).2]
  have hcont (n : ℕ) : Continuous (fun t => u ((r n : ℂ) * inverseCayley t)) :=
    hu.contDiffOn.continuousOn.comp_continuous
      (continuous_const.mul continuous_inverseCayley) (hm n)
  have ht := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n t => poissonKernel 1 t * u ((r n : ℂ) * inverseCayley t))
    (f := fun t => poissonKernel 1 t * b t)
    (fun t => poissonKernel 1 t * M)
    (fun n => ((continuous_poissonKernel (h := 1) (by norm_num)).mul (hcont n)).aestronglyMeasurable)
    ((integrable_poissonKernel (by norm_num : (0 : ℝ) ≤ 1)).mul_const M)
    (fun n => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonKernel_pos (by norm_num) t)]
      exact mul_le_mul_of_nonneg_left (hb _ (hm n t)) (poissonKernel_pos (by norm_num) t).le)
    (by filter_upwards [hl] with t ht; exact tendsto_const_nhds.mul ht)
  have hav (n : ℕ) : (∫ t, poissonKernel 1 t * u ((r n : ℂ) * inverseCayley t)) = u 0 := by
    rw [← circleAverage_eq_cauchy_integral]
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    apply hu.mono
    apply closedBall_subset_ball
    rw [abs_of_nonneg (hr n).1]
    exact (hr n).2
  have he : (fun n => ∫ t, poissonKernel 1 t * u ((r n : ℂ) * inverseCayley t)) =
      fun _ => u 0 := funext hav
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end Erdos1132
