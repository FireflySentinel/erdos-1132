import Erdos1132.FiniteRiesz

/-! # Sharp local differentiation and the near-equality implication -/

noncomputable section
open Complex Real Metric Set Finset
open scoped BigOperators
namespace Erdos1132

theorem rieszSummand_norm_le {f : ℂ → ℂ} {m : ℕ} {z : ℂ}
    (hz : z ∈ cosinePoles m) (hf : ‖f z‖ ≤ 1) :
    ‖Complex.sin z*f z/z^2‖ ≤ rieszWeight z := by
  rw [norm_div, norm_mul, norm_pow, cosinePoles_sin_norm hz, one_mul]
  exact div_le_div_of_nonneg_right hf (sq_nonneg _)

theorem rieszSum_norm_le {f : ℂ → ℂ} {m : ℕ}
    (hf : ∀ z ∈ cosinePoles m, ‖f z‖ ≤ 1) :
    ‖rieszSum m f‖ ≤ ∑ z ∈ cosinePoles m, rieszWeight z := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun z hz => rieszSummand_norm_le hz (hf z hz)))

theorem local_riesz_derivative_bound {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi), ‖f z‖ ≤ Real.exp |z.im|)
    (hreal : ∀ x : ℝ, |x| < (m : ℝ)*Real.pi → ‖f x‖ ≤ 1) :
    ‖deriv f 0‖ ≤ 1+16/((m : ℝ)*Real.pi) := by
  have herr := local_riesz_error hm hf hcircle
  have hw := (abs_le.mp (rieszWeight_sum_error hm)).1
  have hs := rieszSum_norm_le (m := m) (f := f) (by
    intro z hz
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [cosinePoles_real hz]
    rw [he]
    apply hreal
    have hn := cosinePoles_inside hz
    rw [he] at hn
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hn)
  have ht := norm_add_le (deriv f 0-rieszSum m f) (rieszSum m f)
  rw [sub_add_cancel] at ht
  simp only [div_eq_mul_inv] at *
  linarith

theorem rieszSum_re_deficit {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z ∈ cosinePoles m, ‖f z‖ ≤ 1) :
    (rieszSum m f).re ≤ (∑ z ∈ cosinePoles m, rieszWeight z)-
      (4/Real.pi^2)*(1-(f (Real.pi/2)).re) := by
  let p : ℂ := Real.pi/2
  have hp : p ∈ cosinePoles m := first_rieszPoint_mem hm
  have hs : (rieszSum m f).re =
      ∑ z ∈ cosinePoles m, (Complex.sin z*f z/z^2).re := by
    simp only [rieszSum, Complex.re_sum]
  rw [hs, ← Finset.sum_erase_add _ _ hp,
    ← Finset.sum_erase_add (cosinePoles m) rieszWeight hp]
  have hsum : (∑ z ∈ (cosinePoles m).erase p, (Complex.sin z*f z/z^2).re) ≤
      ∑ z ∈ (cosinePoles m).erase p, rieszWeight z := by
    apply Finset.sum_le_sum
    intro z hz
    have hz' := Finset.mem_of_mem_erase hz
    exact (Complex.re_le_norm _).trans (rieszSummand_norm_le hz' (hf z hz'))
  have hpw : rieszWeight p = 4/Real.pi^2 := by
    dsimp [rieszWeight, p]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_ofNat]
    field_simp
    norm_num
  have hps : (Complex.sin p*f p/p^2).re = (4/Real.pi^2)*(f p).re := by
    have hsin : Complex.sin p = 1 := Complex.sin_pi_div_two
    rw [hsin, one_mul, div_eq_mul_inv, ← one_div, ← rieszWeight_coe hp, hpw]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    ring
  rw [hpw, hps]
  dsimp [p] at *
  linarith

theorem local_riesz_near_equality {f : ℂ → ℂ} {m : ℕ} {δ : ℝ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi), ‖f z‖ ≤ Real.exp |z.im|)
    (hreal : ∀ x : ℝ, |x| < (m : ℝ)*Real.pi → ‖f x‖ ≤ 1)
    (hderiv : 1-δ ≤ (deriv f 0).re) :
    1-(Real.pi^2/4)*(δ+16/((m : ℝ)*Real.pi)) ≤ (f (Real.pi/2)).re := by
  have herr := local_riesz_error hm hf hcircle
  have hre := Complex.re_le_norm (deriv f 0-rieszSum m f)
  rw [sub_re] at hre
  have hw := (abs_le.mp (rieszWeight_sum_error hm)).1
  have hs := rieszSum_re_deficit hm (f := f) (by
    intro z hz
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [cosinePoles_real hz]
    rw [he]
    apply hreal
    have hn := cosinePoles_inside hz
    rw [he] at hn
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hn)
  have hdef : (4/Real.pi^2)*(1-(f (Real.pi/2)).re) ≤
      δ+16/((m : ℝ)*Real.pi) := by
    simp only [div_eq_mul_inv] at *
    linarith
  have hp : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left hdef (show 0 ≤ Real.pi^2/4 by positivity)
  have hc : (Real.pi^2/4)*(4/Real.pi^2) = 1 := by field_simp
  rw [← mul_assoc, hc, one_mul] at hmul
  linarith

end Erdos1132
