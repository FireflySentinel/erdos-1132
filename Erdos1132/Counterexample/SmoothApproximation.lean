import Erdos1132.Counterexample.SmoothLowerBound
import Erdos1132.Counterexample.SmoothCutoffs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Smooth cutoff approximations and convergence of the logarithmic operator

Paper: §7.3, smooth positive approximations.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Erdos1132.Counterexample

def cutoffApproximation (χ : ℕ → ℝ → ℝ) (u : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  smoothCutoff (χ j) u (1/((j:ℝ)+1))

theorem smoothCutoff_contDiff {U : Set ℝ} {χ u : ℝ → ℝ} {ε : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ∀ x ∈ U, ContDiffAt ℝ ∞ u x)
    (hzero : ∀ x ∉ U, ∃ d > 0, ∀ y, |x-y| ≤ d → χ y = 0) :
    ContDiff ℝ ∞ (smoothCutoff χ u ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact (hχ.contDiffAt.mul (hu x hx)).add ((contDiffAt_const.sub hχ.contDiffAt).mul contDiffAt_const)
  · obtain ⟨d,hd,hdy⟩ := hzero x hx
    apply (contDiffAt_const (c := ε)).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds x hd] with y hy
    have hdist : |x-y| ≤ d := by have := Metric.mem_ball.mp hy; rw [Real.dist_eq, abs_sub_comm] at this; exact this.le
    simp only [smoothCutoff, hdy y hdist, zero_mul, sub_zero, one_mul, zero_add]

theorem smoothCutoff_bounds {χ u : ℝ → ℝ} {ε x : ℝ}
    (hχ : 0 ≤ χ x ∧ χ x ≤ 1) (hu : 0 ≤ u x ∧ u x ≤ 1) (hε : 0 ≤ ε ∧ ε ≤ 1) :
    0 ≤ smoothCutoff χ u ε x ∧ smoothCutoff χ u ε x ≤ 1 := by
  have hc : 0 ≤ 1-χ x := by linarith [hχ.2]
  have ha := mul_le_mul_of_nonneg_left hu.2 hχ.1
  have hb := mul_le_mul_of_nonneg_left hε.2 hc
  constructor
  · exact add_nonneg (mul_nonneg hχ.1 hu.1) (mul_nonneg hc hε.1)
  · change χ x*u x+(1-χ x)*ε ≤ 1
    nlinarith

theorem smoothCutoff_pos {χ u : ℝ → ℝ} {ε x : ℝ}
    (hχ : 0 ≤ χ x ∧ χ x ≤ 1) (hu : 0 < u x) (hε : 0 < ε) :
    0 < smoothCutoff χ u ε x := by
  by_cases hh : χ x = 1
  · simpa [smoothCutoff,hh] using hu
  · have hc : 0 < 1-χ x := by have := lt_of_le_of_ne hχ.2 hh; linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg hχ.1 hu.le) (mul_pos hc hε)

theorem cutoffApproximation_pointwise {U : Set ℝ} {χ : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hu0 : ∀ x ∉ U, u x = 0)
    (hχ0 : ∀ j x, x ∉ U → χ j x = 0)
    (hχ1 : ∀ x ∈ U, ∀ᶠ j in atTop, χ j x = 1) (x : ℝ) :
    Tendsto (fun j => cutoffApproximation χ u j x) atTop (𝓝 (u x)) := by
  by_cases hx : x ∈ U
  · apply tendsto_const_nhds.congr'
    filter_upwards [hχ1 x hx] with j hj
    simp [cutoffApproximation,smoothCutoff,hj]
  · rw [hu0 x hx]
    convert (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)) using 1
    funext j
    simp [cutoffApproximation,smoothCutoff,hχ0 j x hx]

theorem cutoffApproximation_L1_tendsto {U : Set ℝ} {χ : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hum : Measurable u) (hub : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hχm : ∀ j, Measurable (χ j)) (hχb : ∀ j x, 0 ≤ χ j x ∧ χ j x ≤ 1)
    (hu0 : ∀ x ∉ U, u x = 0) (hχ0 : ∀ j x, x ∉ U → χ j x = 0)
    (hχ1 : ∀ x ∈ U, ∀ᶠ j in atTop, χ j x = 1) :
    Tendsto (fun j => ∫ y in interval, |cutoffApproximation χ u j y-u y|) atTop (𝓝 0) := by
  have hvb : ∀ j x, 0 ≤ cutoffApproximation χ u j x ∧ cutoffApproximation χ u j x ≤ 1 :=
    fun j x => smoothCutoff_bounds (hχb j x) (hub x)
      ⟨by positivity, div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by positivity)⟩
  have hvm : ∀ j, Measurable (cutoffApproximation χ u j) := fun j =>
    ((hχm j).mul hum).add ((measurable_const.sub (hχm j)).mul measurable_const)
  have hh := tendsto_integral_of_dominated_convergence (μ := volume.restrict interval)
    (F := fun j y => |cutoffApproximation χ u j y-u y|) (f := fun _ => (0:ℝ)) (fun _ => (2:ℝ))
    (fun j => (continuous_abs.measurable.comp ((hvm j).sub hum)).aestronglyMeasurable) (integrable_const 2)
    (fun j => Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs,abs_abs]
      apply abs_le.mpr
      constructor <;> linarith [(hvb j y).1,(hvb j y).2,(hub y).1,(hub y).2]))
    (Filter.Eventually.of_forall (fun y => by
      have ht : Tendsto (fun j => cutoffApproximation χ u j y-u y) atTop (𝓝 (u y-u y)) :=
        (cutoffApproximation_pointwise hu0 hχ0 hχ1 y).sub tendsto_const_nhds
      have hab : Tendsto (fun j => |cutoffApproximation χ u j y-u y|) atTop (𝓝 |u y-u y|) := ht.abs
      simpa only [sub_self,abs_zero] using hab))
  simpa only [integral_zero] using hh

theorem smooth_kernel_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {x : ℝ} (hx : x ∈ interval) :
    IntegrableOn (differenceKernel f x) interval := by
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuous_deriv (by simp)).continuousOn
  apply integrable_differenceKernel (K := max K 0) (le_max_right _ _)
    (fun y _ => ((hf.differentiable (by simp)) y).hasDerivAt.hasDerivWithinAt) _ hx
  intro y hy
  have hh : |deriv f y| ≤ K := by simpa only [Real.norm_eq_abs] using hK y hy
  exact hh.trans (le_max_left _ _)

theorem logarithmicOperator_tendsto_of_local_equality {v : ℕ → ℝ → ℝ} {u : ℝ → ℝ} {x r : ℝ}
    (hx : x ∈ interval) (hr : 0 < r)
    (hv : ∀ j, IntegrableOn (differenceKernel (v j) x) interval)
    (hu : IntegrableOn (differenceKernel u x) interval)
    (hvi : ∀ j, IntegrableOn (fun y => v j y-u y) interval)
    (hL1 : Tendsto (fun j => ∫ y in interval, |v j y-u y|) atTop (𝓝 0))
    (heq : ∀ᶠ j in atTop, ∀ y ∈ interval, |x-y| < r → v j y = u y) :
    Tendsto (fun j => logarithmicOperator (v j) x) atTop (𝓝 (logarithmicOperator u x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [heq] with j hj
    simpa only [Real.norm_eq_abs] using logarithmicOperator_local_eq_bound hx hr (hv j) hu (hvi j) hj
  · simpa only [zero_div] using hL1.div_const r

end Erdos1132.Counterexample
