import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic

noncomputable section

namespace Erdos1132

open Polynomial.Chebyshev

theorem chebyshev_norm_le_one (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    ‖(T ℂ k).eval (t : ℂ)‖ ≤ 1 := by
  rw [← complex_ofReal_eval_T, Complex.norm_real, Real.norm_eq_abs,
    ← Real.cos_arccos ht.1 ht.2, T_real_cos]
  exact Real.abs_cos_le_one _

private theorem sinh_abs (x : ℝ) : Real.sinh |x| = |Real.sinh x| := by
  by_cases hx : 0 ≤ x
  · simp [abs_of_nonneg hx, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [abs_of_nonpos hx', Real.sinh_neg,
      abs_of_nonpos (Real.sinh_nonpos_iff.mpr hx')]

theorem norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.cosh_ofReal_re, Complex.cos_ofReal_im, Complex.cosh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sinh_ofReal_re, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im,
    Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
    mul_one]
  have h := congrArg (fun a : ℝ => a * Real.sinh z.im ^ 2)
    (Real.sin_sq_add_cos_sq z.re)
  nlinarith [Real.cosh_sq z.im]

theorem sinh_abs_im_le_norm_cos (z : ℂ) :
    Real.sinh |z.im| ≤ ‖Complex.cos z‖ := by
  rw [sinh_abs]
  have h := norm_cos_sq z
  nlinarith [sq_abs (Real.sinh z.im), abs_nonneg (Real.sinh z.im),
    norm_nonneg (Complex.cos z), sq_nonneg (Real.cos z.re)]

theorem abs_im_cos_le_sinh_abs (z : ℂ) :
    |(Complex.cos z).im| ≤ Real.sinh |z.im| := by
  rw [Complex.cos_eq]
  simp only [Complex.sub_im, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.cosh_ofReal_re, Complex.cos_ofReal_im, Complex.cosh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sinh_ofReal_re, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, add_zero, sub_zero, zero_sub, mul_one,
    abs_neg, abs_mul]
  rw [sinh_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)

theorem half_le_arsinh {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) : h / 2 ≤ Real.arsinh h := by
  have hp : 0 < 1 + h := by linarith
  have hs : 1 ≤ Real.sqrt (1 + h ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg h]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hfrac : h / 2 ≤ 1 - (1 + h)⁻¹ := by
    rw [show 1 - (1 + h)⁻¹ = h / (1 + h) by field_simp; ring]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  exact hfrac.trans (hl.trans (Real.log_le_log hp (by linarith)))

/-- Exponential growth off the interval, in the form used for Cauchy cancellation. -/
theorem chebyshev_norm_lower (k : ℕ) {z : ℂ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hz : h ≤ |z.im|) :
    Real.sinh ((k : ℝ) * h / 2) ≤ ‖(T ℂ k).eval z‖ := by
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective z
  have hθ : h / 2 ≤ |θ.im| := by
    apply (half_le_arsinh hh hh1).trans
    rw [← Real.arsinh_sinh |θ.im|]
    exact Real.arsinh_le_arsinh.mpr (hz.trans (abs_im_cos_le_sinh_abs θ))
  rw [T_complex_cos]
  apply le_trans _ (sinh_abs_im_le_norm_cos ((k : ℤ) * θ))
  apply Real.sinh_le_sinh.mpr
  simp only [Int.cast_natCast, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, zero_mul, add_zero, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  nlinarith

end Erdos1132
