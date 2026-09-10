import Erdos1132.Shared.CauchyRational
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The boundary harmonic-measure identity

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Filter InnerProductSpace Metric Set Complex
open scoped Topology

namespace Erdos1132

def radialRadius (j : ℕ) : ℝ := 1 - 1 / ((j : ℝ) + 1)

theorem radialRadius_mem (j : ℕ) : radialRadius j ∈ Ico 0 1 := by
  have hp : 0 < (j : ℝ) + 1 := by positivity
  have hd : 1 / ((j : ℝ) + 1) ≤ 1 := (div_le_one hp).mpr
    (by linarith [Nat.cast_nonneg j (α := ℝ)])
  have hd' : 0 < 1 / ((j : ℝ) + 1) := by positivity
  dsimp [radialRadius]
  constructor <;> linarith

theorem tendsto_radialRadius : Tendsto radialRadius atTop (𝓝 1) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  convert! hc.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
  norm_num

theorem poisson_integral_affine {h : ℝ} (hh : 0 < h) (x : ℝ) (f : ℝ → ℝ) :
    (∫ y, poissonKernel h (y - x) * f y) =
      ∫ t, poissonKernel 1 t * f (x + h * t) := by
  have hi : Function.Injective (fun t : ℝ => x + h * t) := by
    intro s t hst
    exact (mul_left_cancel₀ hh.ne') (add_left_cancel hst)
  have hs : Function.Surjective (fun t : ℝ => x + h * t) := by
    intro y
    refine ⟨(y - x) / h, ?_⟩
    field_simp
    ring
  have hd (t : ℝ) : HasDerivAt (fun t => x + h * t) h t := by
    convert! ((hasDerivAt_id t).const_mul h).const_add x using 1
    simp
  have he := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hd t).hasDerivWithinAt) hi.injOn
    (fun y => poissonKernel h (y - x) * f y)
  simp only [image_univ, hs.range_eq, Measure.restrict_univ, abs_of_pos hh,
    smul_eq_mul] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with t
  unfold poissonKernel
  field_simp
  ring

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem boundary_measure_stereographic {a b h : ℝ} (hab : a < b) (hh : 0 < h) (x : ℝ) :
    (∫ t, poissonKernel 1 t *
      (if a < μ.boundary (x + h * t) ∧ μ.boundary (x + h * t) < b then 1 else 0)) =
      intervalHarmonic a b (μ.cauchy ((x : ℂ) + h * I)) := by
  let u : ℂ → ℝ := fun w => intervalHarmonic a b (μ.cauchy (cayley x h w))
  have hu : HarmonicOnNhd u (ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
    have hc : 0 < (cayley x h w).im := cayley_im_pos x hh hwn
    have hw1 : w ≠ 1 := by intro he; simp [he] at hwn
    exact harmonicAt_intervalHarmonic_comp hab
      ((μ.analyticAt_cauchy_upper hc).comp (f := cayley x h) (analyticAt_cayley x h hw1))
      (μ.cauchy_im_neg hc)
  let r := radialRadius
  have hr := radialRadius_mem
  have hrt := tendsto_radialRadius
  have hinj : Function.Injective (fun t : ℝ => x + h * t) := by
    intro s t hst
    exact (mul_left_cancel₀ hh.ne') (add_left_cancel hst)
  have hl : ∀ᵐ t, Tendsto (fun j => u ((r j : ℂ) * inverseCayley t)) atTop
      (𝓝 (if a < μ.boundary (x + h * t) ∧ μ.boundary (x + h * t) < b then 1 else 0)) := by
    filter_upwards [μ.ae_regular_boundary_comp a b hinj] with t ht
    have hc := (μ.analyticAt_cauchy (z := ((x + h * t : ℝ) : ℂ))
      (fun i hi => ht.1 i (Complex.ofReal_injective hi))).continuousAt
    have hlim := hc.tendsto.comp (cayley_radial_tendsto x h t hrt)
    rw [μ.cauchy_ofReal] at hlim
    apply tendsto_intervalHarmonic_real hab ht.2.1 ht.2.2 hlim
    intro j
    apply μ.cauchy_im_neg
    apply cayley_im_pos x hh
    simpa [norm_inverseCayley, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hr j).1] using (hr j).2
  have he := harmonic_boundary_cauchy hu (fun w _ => abs_intervalHarmonic_le_one a b _)
    r hr _ hl
  simpa only [u, cayley_zero] using he

/-- Boundary harmonic measure for a finite positive Cauchy transform. -/
theorem boundary_harmonic_measure {a b h : ℝ} (hab : a < b) (hh : 0 < h) (x : ℝ) :
    (∫ y, poissonKernel h (x - y) *
      (if a < μ.boundary y ∧ μ.boundary y < b then 1 else 0)) =
      intervalHarmonic a b (μ.cauchy ((x : ℂ) + h * I)) := by
  rw [← μ.boundary_measure_stereographic hab hh x,
    ← poisson_integral_affine hh x (fun y => if a < μ.boundary y ∧ μ.boundary y < b then 1 else 0)]
  apply integral_congr_ae
  filter_upwards with y
  rw [show x - y = -(y - x) by ring, poissonKernel_neg]

end AtomicProbability

end Erdos1132
