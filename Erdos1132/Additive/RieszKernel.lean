import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! # The regularized inverse-distance kernel and its Gaussian representation

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Real MeasureTheory
namespace Erdos1132

def rieszKernel (ε t : ℝ) : ℝ := 1/Real.sqrt (t^2+ε^2)

theorem rieszKernel_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < rieszKernel ε t := by
  unfold rieszKernel
  positivity

theorem rieszKernel_even (ε t : ℝ) : rieszKernel ε (-t) = rieszKernel ε t := by
  simp [rieszKernel]

theorem rieszKernel_diagonal {ε : ℝ} (hε : 0 ≤ ε) : rieszKernel ε 0 = 1/ε := by
  simp [rieszKernel, Real.sqrt_sq hε]

theorem rieszKernel_le_diagonal {ε : ℝ} (hε : 0 < ε) (t : ℝ) : rieszKernel ε t ≤ 1/ε := by
  apply one_div_le_one_div_of_le hε
  calc
    ε = Real.sqrt (ε^2) := (Real.sqrt_sq hε.le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

theorem rieszKernel_le_inverse_distance {ε t : ℝ} (ht : t ≠ 0) :
    rieszKernel ε t ≤ 1/|t| := by
  apply one_div_le_one_div_of_le (abs_pos.mpr ht)
  calc
    |t| = Real.sqrt (t^2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

theorem continuous_rieszKernel {ε : ℝ} (hε : 0 < ε) : Continuous (rieszKernel ε) := by
  unfold rieszKernel
  apply continuous_const.div (by fun_prop)
  intro t
  exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t, sq_pos_of_pos hε])).ne'

theorem integrable_riesz_gaussian_mixture {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-s^2*ε^2)*Real.exp (-s^2*t^2)) := by
  have hi := integrable_exp_neg_mul_sq (by nlinarith [sq_nonneg t, sq_pos_of_pos hε] : 0 < t^2+ε^2)
  convert hi using 1
  funext s
  rw [← Real.exp_add]
  congr 1
  ring

/-- Integrating over the real Gaussian parameter avoids a separate Gamma-integral
normalization and gives the exact inverse square-root kernel. -/
theorem rieszKernel_gaussian_mixture {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    rieszKernel ε t = (1/Real.sqrt Real.pi)*
      ∫ s : ℝ, Real.exp (-s^2*ε^2)*Real.exp (-s^2*t^2) := by
  have he : (fun s : ℝ => Real.exp (-s^2*ε^2)*Real.exp (-s^2*t^2)) =
      (fun s => Real.exp (-(t^2+ε^2)*s^2)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  unfold rieszKernel
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

end Erdos1132
