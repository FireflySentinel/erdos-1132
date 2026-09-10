import Erdos1132.Shared.KernelConcentration

/-! # Convergence of approximate identities

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace Erdos1132

/-- Concentration at zero tests against every bounded function continuous at zero. -/
theorem probability_kernel_tendsto {k : ℕ → ℝ → ℝ}
    (hk : ∀ n t, 0 ≤ k n t) (hi : ∀ n, Integrable (k n))
    (hm : ∀ n, ∫ t, k n t = 1)
    (ht : ∀ δ > 0, Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, k n t) atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ t, |f t| ≤ M)
    (hc : ContinuousAt f 0) :
    Tendsto (fun n => ∫ t, k n t * f t) atTop (𝓝 (f 0)) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hb 0)
  have hif (n : ℕ) : Integrable (fun t => k n t * f t) :=
    (hi n).mul_bdd hf.aestronglyMeasurable (ae_of_all _ hb)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (by positivity)
  let d := δ / 2
  have hd0 : 0 < d := by dsimp [d]; positivity
  let B := 2 * M + 1
  have hB : 0 < B := by dsimp [B]; linarith
  filter_upwards [(ht d hd0).eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * B) by positivity))]
    with n hn
  have hid : Integrable (fun t => k n t * (f t - f 0)) :=
    (hif n).sub ((hi n).mul_const (f 0)) |>.congr (ae_of_all _ fun t => by dsimp; ring)
  have hie : Integrable ((Icc (-d) d)ᶜ.indicator (k n)) := (hi n).indicator measurableSet_Icc.compl
  have hbound : ∀ t, ‖k n t * (f t - f 0)‖ ≤
      (ε / 2) * k n t + B * (Icc (-d) d)ᶜ.indicator (k n) t := by
    intro t
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hk n t), Real.norm_eq_abs]
    by_cases ht' : t ∈ Icc (-d) d
    · have hdist : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_lt]
        dsimp [d] at ht'
        constructor <;> linarith [ht'.1, ht'.2]
      have hsmall : |f t - f 0| < ε / 2 := by simpa [Real.dist_eq] using hd hdist
      simp only [indicator_of_notMem (show t ∉ (Icc (-d) d)ᶜ by simpa), mul_zero, add_zero]
      nlinarith [hk n t]
    · have hdif : |f t - f 0| ≤ 2 * M :=
        (abs_sub _ _).trans (by linarith [hb t, hb 0])
      rw [indicator_of_mem (show t ∈ (Icc (-d) d)ᶜ from ht')]
      dsimp only [B]
      nlinarith [hk n t]
  have heq : (∫ t, k n t * (f t - f 0)) = (∫ t, k n t * f t) - f 0 := by
    simp_rw [mul_sub]
    rw [integral_sub (hif n) ((hi n).mul_const _), integral_mul_const, hm, one_mul]
  have he : ‖(∫ t, k n t * f t) - f 0‖ ≤ ε / 2 + B * ∫ t in (Icc (-d) d)ᶜ, k n t := by
    rw [← heq]
    calc
      _ ≤ ∫ t, ‖k n t * (f t - f 0)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (ε / 2) * k n t + B * (Icc (-d) d)ᶜ.indicator (k n) t :=
        integral_mono hid.norm (((hi n).const_mul _).add (hie.const_mul _)) hbound
      _ = _ := by
        rw [integral_add ((hi n).const_mul _) (hie.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator measurableSet_Icc.compl, hm, mul_one]
  rw [dist_eq_norm]
  apply he.trans_lt
  have hn' : B * (∫ t in (Icc (-d) d)ᶜ, k n t) < ε / 2 := by
    have := mul_lt_mul_of_pos_left hn hB
    convert! this using 1; field_simp
  linarith

end Erdos1132
