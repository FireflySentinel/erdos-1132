import Erdos1132.Additive.GaussianEnergy

/-! # Positivity of regularized inverse-distance energy

Paper: §3, derivative-jump energy.
-/

noncomputable section
open Real MeasureTheory Filter
namespace Erdos1132

theorem integrable_weighted_riesz_pair {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {x a : α → ℝ} {y b : β → ℝ} (hx : Measurable x) (ha : Measurable a)
    (hy : Measurable y) (hb : Measurable b) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hab : ∀ u, |a u| ≤ B) (hbb : ∀ v, |b v| ≤ B) :
    Integrable (fun p : α × β => a p.1*b p.2*rieszKernel ε (x p.1-y p.2)) (μ.prod ν) := by
  apply (integrable_const (B^2/ε)).mono'
  · exact (((ha.comp measurable_fst).mul (hb.comp measurable_snd)).mul
      ((continuous_rieszKernel hε).measurable.comp
        ((hx.comp measurable_fst).sub (hy.comp measurable_snd)))).aestronglyMeasurable
  · apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
    calc
      _ ≤ B^2*(1/ε) := mul_le_mul
        (by simpa only [pow_two] using mul_le_mul (hab p.1) (hbb p.2) (abs_nonneg _) hB)
        (rieszKernel_le_diagonal hε _) (rieszKernel_pos hε _).le (sq_nonneg B)
      _ = _ := by ring

theorem riesz_energy_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {x w : α → ℝ}
    (hx : Measurable x) (hw : Measurable w) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε)
    (hxb : ∀ u, |x u| ≤ 1) (hwb : ∀ u, |w u| ≤ B) :
    0 ≤ ∫ p : α × α, w p.1*w p.2*rieszKernel ε (x p.1-x p.2) ∂μ.prod μ := by
  let F (s : ℝ) (p : α × α) := Real.exp (-s^2*ε^2)*
    (w p.1*w p.2*Real.exp (-s^2*(x p.1-x p.2)^2))
  have hFm : Measurable (Function.uncurry F) := by dsimp [F, Function.uncurry]; fun_prop
  have hb (s : ℝ) (p : α × α) : ‖F s p‖ ≤ Real.exp (-ε^2*s^2)*B^2 := by
    have he : Real.exp (-s^2*(x p.1-x p.2)^2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have hh := mul_nonneg (sq_nonneg s) (sq_nonneg (x p.1-x p.2))
        nlinarith)
    have hw' : |w p.1| * |w p.2| ≤ B^2 := by
      simpa only [pow_two] using mul_le_mul (hwb p.1) (hwb p.2) (abs_nonneg _) hB
    dsimp [F]
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    rw [show -s^2*ε^2 = -ε^2*s^2 by ring]
    exact mul_le_mul_of_nonneg_left
      (by simpa using mul_le_mul hw' he (Real.exp_pos _).le (sq_nonneg B)) (Real.exp_pos _).le
  have hi : Integrable (Function.uncurry F) (volume.prod (μ.prod μ)) := by
    have henv := (integrable_exp_neg_mul_sq (sq_pos_of_pos hε)).mul_prod
      (integrable_const (μ := μ.prod μ) (B^2))
    exact henv.mono' hFm.aestronglyMeasurable (ae_of_all _ (fun p => hb p.1 p.2))
  have hnonneg : 0 ≤ ∫ s : ℝ, ∫ p, F s p ∂μ.prod μ := by
    apply integral_nonneg
    intro s
    dsimp only [F]
    rw [integral_const_mul]
    exact mul_nonneg (Real.exp_pos _).le
      (gaussian_energy_nonneg μ hx hw hB (sq_nonneg s) hxb hwb)
  rw [integral_integral_swap hi] at hnonneg
  have hmix (p : α × α) : (∫ s : ℝ, F s p) =
      Real.sqrt Real.pi * (w p.1*w p.2*rieszKernel ε (x p.1-x p.2)) := by
    have he : (fun s : ℝ => F s p) = (fun s => (w p.1*w p.2)*
      (Real.exp (-s^2*ε^2)*Real.exp (-s^2*(x p.1-x p.2)^2))) := by funext s; dsimp [F]; ring
    rw [he, integral_const_mul, rieszKernel_gaussian_mixture hε]
    have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun s => by congr 1 <;> ring)
  simp_rw [hmix] at hnonneg
  rw [integral_const_mul] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg (Real.sqrt_pos.mpr Real.pi_pos)

end Erdos1132
