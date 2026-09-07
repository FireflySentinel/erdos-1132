import Erdos1132.Additive.RescaledRiesz
import Mathlib.Analysis.Complex.Liouville

/-! # The second derivative bound from local complex growth

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Real Complex Set Metric
namespace Erdos1132

theorem polynomial_second_derivative_bound {p : ℝ[X]} {x ω M r h : ℝ}
    (hω : 0 < ω) (hM : 0 ≤ M) (hr : 1/ω ≤ r) (hh : 1/ω ≤ h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|)) :
    |p.derivative.derivative.eval x| ≤ 2*M*Real.exp 1*ω^2 := by
  have hf : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun z : ℂ => aeval z p) (c := (x : ℂ)) 2 (one_div_pos.mpr hω) hf.diffContOnCl
    (C := M*Real.exp 1) (by
      intro z hz
      have hn : ‖z-(x : ℂ)‖ = 1/ω := by simpa [mem_sphere, dist_eq_norm] using hz
      have hu : |z.re-x| ≤ 1/ω := by
        have ht := Complex.abs_re_le_norm (z-(x : ℂ))
        simpa only [sub_re, ofReal_re, hn] using ht
      have hv : |z.im| ≤ 1/ω := by
        have ht := Complex.abs_im_le_norm (z-(x : ℂ))
        simpa only [sub_im, ofReal_im, sub_zero, hn] using ht
      have hg := hgrowth (z.re-x) z.im (hu.trans hr) (hv.trans hh)
      have he : (((x+(z.re-x) : ℝ) : ℂ)+z.im*I) = z := by
        rw [add_sub_cancel, re_add_im]
      rw [he] at hg
      apply hg.trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hM
      have ht := mul_le_mul_of_nonneg_left hv hω.le
      simpa only [mul_one_div_cancel hω.ne'] using ht)
  have hder : iteratedDeriv 2 (fun z : ℂ => aeval z p) (x : ℂ) =
      ((p.derivative.derivative.eval x : ℝ) : ℂ) := by
    rw [show (2 : ℕ) = 1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have he : deriv (fun z : ℂ => aeval z p) = (fun z : ℂ => aeval z p.derivative) :=
      funext (fun _ => p.deriv_aeval)
    rw [he, Polynomial.deriv_aeval]
    exact real_polynomial_eval₂_real _ _
  rw [hder, Complex.norm_real, Real.norm_eq_abs] at hb
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul, mul_one] at hb
  convert hb using 1 <;> field_simp <;> ring

end Erdos1132
