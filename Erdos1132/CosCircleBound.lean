import Erdos1132.Scales
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Uniform cosine bounds on circles of radius an integer multiple of π -/

noncomputable section
open Complex Real Metric Set
namespace Erdos1132

theorem abs_sinh_le_norm_cos (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.cos z‖ := by
  have he := norm_cos_sq z
  nlinarith [sq_abs (Real.sinh z.im), sq_nonneg (Real.cos z.re), norm_nonneg (Complex.cos z)]

theorem abs_cos_re_le_norm_cos (z : ℂ) : |Real.cos z.re| ≤ ‖Complex.cos z‖ := by
  have he := norm_cos_sq z
  nlinarith [sq_abs (Real.cos z.re), sq_nonneg (Real.sinh z.im), norm_nonneg (Complex.cos z)]

theorem exp_im_le_eight_norm_cos {m : ℕ} (hm : 1 ≤ m) {z : ℂ}
    (hz : ‖z‖ = m*Real.pi) : Real.exp |z.im| ≤ 8*‖Complex.cos z‖ := by
  have hR : 2 ≤ (m : ℝ)*Real.pi := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three]
  by_cases hi : 1 ≤ |z.im|
  · have hh := exp_div_four_le_sinh hi
    rw [← Real.abs_sinh] at hh
    have hn := abs_sinh_le_norm_cos z
    nlinarith [norm_nonneg (Complex.cos z)]
  · have hi' : |z.im| ≤ 1 := le_of_lt (lt_of_not_ge hi)
    have hu : |z.re| ≤ (m : ℝ)*Real.pi := hz ▸ Complex.abs_re_le_norm z
    have hs : z.re^2+z.im^2 = ((m : ℝ)*Real.pi)^2 := by
      rw [← hz, Complex.sq_norm, Complex.normSq_apply]
      ring
    let d : ℝ := m*Real.pi-|z.re|
    have hd : 0 ≤ d := sub_nonneg.mpr hu
    have hd2 : d ≤ 1/2 := by
      have hi2 : z.im^2 ≤ 1 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
      have hid : d*((m : ℝ)*Real.pi+|z.re|) = z.im^2 := by
        dsimp [d]
        nlinarith [sq_abs z.re]
      have hp : d*2 ≤ d*((m : ℝ)*Real.pi+|z.re|) :=
        mul_le_mul_of_nonneg_left (by linarith [abs_nonneg z.re]) hd
      linarith
    have hc : 1/2 ≤ |Real.cos d| := by
      have hl := Real.lipschitzWith_cos.dist_le_mul d 0
      simp only [Real.dist_eq, Real.cos_zero, NNReal.coe_one, one_mul, sub_zero,
        abs_of_nonneg hd] at hl
      have h := (abs_le.mp hl).1
      exact le_trans (by linarith : 1/2 ≤ Real.cos d) (le_abs_self _)
    have he : |Real.cos z.re| = |Real.cos d| := by
      have heq : |z.re| = (m : ℝ)*Real.pi-d := by dsimp [d]; ring
      rw [← Real.cos_abs z.re, heq, Real.cos_nat_mul_pi_sub, abs_mul, abs_pow]
      norm_num
    have hn : 1/2 ≤ ‖Complex.cos z‖ := by
      rw [← he] at hc
      exact hc.trans (abs_cos_re_le_norm_cos z)
    have hexp := Real.exp_le_exp.mpr hi'
    linarith [Real.exp_one_lt_three]

end Erdos1132
