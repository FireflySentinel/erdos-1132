import Erdos1132.Additive.CosPoles
import Erdos1132.Additive.FiniteResidueFormula

/-! # The local Riesz differentiation formula with an explicit error

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Complex Real Metric Set Finset
open scoped BigOperators
namespace Erdos1132

def rieszSum (m : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ z ∈ cosinePoles m, Complex.sin z*f z/z^2

theorem norm_sin_le_exp_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one]
  norm_num only [Complex.norm_ofNat]
  have he1 : ‖Complex.exp (-z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have he2 : ‖Complex.exp (z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have ht := norm_sub_le (Complex.exp (-z*I)) (Complex.exp (z*I))
  linarith

theorem cosine_residue_formula {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    (∮ z in C(0, (m : ℝ)*Real.pi), f z/(Complex.cos z*z^2)) =
      (2*Real.pi*I)*(deriv f 0-rieszSum m f) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have h := finite_residue_derivative_formula hf Complex.analyticOnNhd_cos hR
    (zero_not_mem_cosinePoles m) (fun a ha => cosinePoles_inside ha)
    (fun z hz => cosinePoles_exact hm hz) (fun a ha => cosinePoles_simple ha)
    Complex.cos_zero (by simp)
  rw [h, sub_eq_add_neg, rieszSum, ← Finset.sum_neg_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro a ha
  rw [Complex.deriv_cos]
  have hs := cosinePoles_sin_sq ha
  have hn : Complex.sin a ≠ 0 := by intro he; simp [he] at hs
  have hdiv : f a/Complex.sin a = Complex.sin a*f a := by
    apply (div_eq_iff hn).mpr
    calc
      f a = f a*(Complex.sin a)^2 := by rw [hs]; ring
      _ = Complex.sin a*f a*Complex.sin a := by ring
  rw [div_neg, hdiv]
  ring

theorem local_riesz_error {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hbound : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi), ‖f z‖ ≤ Real.exp |z.im|) :
    ‖deriv f 0-rieszSum m f‖ ≤ 8/((m : ℝ)*Real.pi) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have hk : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi),
      ‖f z/(Complex.cos z*z^2)‖ ≤ 8/((m : ℝ)*Real.pi)^2 := by
    intro z hz
    have hn : ‖z‖ = (m : ℝ)*Real.pi := by simpa [mem_sphere, dist_eq_norm] using hz
    have hc := exp_im_le_eight_norm_cos hm hn
    have hc0 : 0 < ‖Complex.cos z‖ := by nlinarith [Real.exp_pos |z.im|]
    rw [norm_div, norm_mul, norm_pow, hn]
    apply (div_le_iff₀ (mul_pos hc0 (sq_pos_of_pos hR))).mpr
    have hh : (8/((m : ℝ)*Real.pi)^2)*(‖Complex.cos z‖*((m : ℝ)*Real.pi)^2) =
        8*‖Complex.cos z‖ := by field_simp
    rw [hh]
    exact (hbound z hz).trans hc
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hk
  rw [cosine_residue_formula hm hf, smul_eq_mul, inv_mul_cancel_left₀] at h
  · convert! h using 1 <;> field_simp <;> ring
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

def rieszWeight (z : ℂ) : ℝ := 1/‖z‖^2

theorem rieszWeight_nonneg (z : ℂ) : 0 ≤ rieszWeight z := by
  exact one_div_nonneg.mpr (sq_nonneg _)

theorem rieszWeight_coe {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    (rieszWeight z : ℂ) = 1/z^2 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [cosinePoles_real hz]
  rw [he]
  simp [rieszWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem rieszSum_sin (m : ℕ) :
    rieszSum m Complex.sin = ((∑ z ∈ cosinePoles m, rieszWeight z : ℝ) : ℂ) := by
  rw [rieszSum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← pow_two, cosinePoles_sin_sq hz, rieszWeight_coe hz]

theorem rieszWeight_sum_error {m : ℕ} (hm : 1 ≤ m) :
    |1-∑ z ∈ cosinePoles m, rieszWeight z| ≤ 8/((m : ℝ)*Real.pi) := by
  have h := local_riesz_error hm Complex.analyticOnNhd_sin (fun z _ => norm_sin_le_exp_im z)
  rw [Complex.deriv_sin, Complex.cos_zero, rieszSum_sin, ← ofReal_one, ← ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end Erdos1132
