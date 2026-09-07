import Erdos1132.Shared.BoundaryMeasure

/-! # The convolution identity for Poisson kernels

Paper: Shared analytic tools for §§2–6.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter Complex InnerProductSpace Metric

namespace Erdos1132.AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem norm_cauchy_le {z : ℂ} {h : ℝ} (hh : 0 < h) (hz : h ≤ z.im) :
    ‖μ.cauchy z‖ ≤ 1 / h := by
  have hd (i : Fin n) : h ≤ ‖z - (μ.point i : ℂ)‖ := by
    calc
      h ≤ z.im := hz
      _ ≤ |(z - (μ.point i : ℂ)).im| := by simpa using le_abs_self z.im
      _ ≤ ‖z - (μ.point i : ℂ)‖ := Complex.abs_im_le_norm _
  unfold cauchy
  calc
    _ ≤ ∑ i, ‖(μ.mass i : ℂ) / (z - μ.point i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, μ.mass i / h := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (μ.mass_nonneg i)]
      exact div_le_div_of_nonneg_left (μ.mass_nonneg i) hh (hd i)
    _ = 1 / h := by rw [← Finset.sum_div, μ.sum_mass]

theorem gamma_semigroup_add {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (x : ℝ) :
    μ.gamma (h + s) x = ∫ y, poissonKernel s (x - y) * μ.gamma h y := by
  let u : ℂ → ℝ := fun w => -(μ.cauchy (cayley x s w + h * I)).im
  have hu : HarmonicOnNhd u (ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
    have hc := cayley_im_pos x hs hwn
    have hcz : 0 < (cayley x s w + h * I).im := by simpa using add_pos hc hh
    have hw1 : w ≠ 1 := by intro he; simp [he] at hwn
    have hca : AnalyticAt ℂ (fun w => cayley x s w + h * I) w := by
      have ha := analyticAt_cayley x s hw1
      fun_prop
    exact ((μ.analyticAt_cauchy_upper hcz).comp
      (f := fun w => cayley x s w + h * I) hca).harmonicAt_im.neg
  have hb : ∀ w ∈ ball (0 : ℂ) 1, |u w| ≤ 1 / h := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
    have hc := cayley_im_pos x hs hwn
    change |-(μ.cauchy (cayley x s w + h * I)).im| ≤ 1 / h
    rw [abs_neg]
    apply (Complex.abs_im_le_norm _).trans
    apply μ.norm_cauchy_le hh
    simpa using (le_add_of_nonneg_left hc.le : h ≤ (cayley x s w).im + h)
  have hl : ∀ᵐ t, Tendsto (fun j => u ((radialRadius j : ℂ) * inverseCayley t)) atTop
      (𝓝 (μ.gamma h (x + s * t))) := by
    apply ae_of_all
    intro t
    have hz : 0 < (((x + s * t : ℝ) : ℂ) + h * I).im := by simpa using hh
    have ht := (cayley_radial_tendsto x s t tendsto_radialRadius).add_const ((h : ℂ) * I)
    have hc := ((μ.analyticAt_cauchy_upper hz).continuousAt.tendsto.comp ht)
    have hi := (Complex.continuous_im.tendsto _ |>.comp hc).neg
    simpa only [u, Function.comp_def, μ.neg_im_cauchy] using hi
  have he' := harmonic_boundary_cauchy hu hb radialRadius radialRadius_mem
    (fun t => μ.gamma h (x + s * t)) hl
  have hu0 : u 0 = μ.gamma (h + s) x := by
    change -(μ.cauchy (cayley x s 0 + (h : ℂ) * I)).im = μ.gamma (h + s) x
    rw [cayley_zero, show (x : ℂ) + s * I + h * I = (x : ℂ) + (h + s) * I by ring]
    simpa only [Complex.ofReal_add] using μ.neg_im_cauchy (h + s) x
  rw [hu0, ← poisson_integral_affine hs x (μ.gamma h)] at he'
  rw [← he']
  apply integral_congr_ae
  filter_upwards with y
  rw [show x - y = -(y - x) by ring, poissonKernel_neg]

theorem gamma_semigroup {h s : ℝ} (hh : 0 < h) (hs : h < s) (x : ℝ) :
    μ.gamma s x = ∫ y, poissonKernel (s - h) (x - y) * μ.gamma h y := by
  simpa only [show h + (s - h) = s by ring] using μ.gamma_semigroup_add hh (sub_pos.mpr hs) x

end Erdos1132.AtomicProbability
