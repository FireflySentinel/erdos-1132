import Erdos1132.Shared.PoissonKernel
import Mathlib.Tactic

/-! # Bounds for the exterior Poisson kernel separated from an interval

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Set Real
namespace Erdos1132

/-- A uniform comparison coefficient against the Cauchy kernel at the origin. -/
def exteriorKernelBound (d : ℝ) : ℝ := Real.pi*(2+3/d^2)

theorem exteriorKernelBound_pos {d : ℝ} (hd : 0 < d) : 0 < exteriorKernelBound d := by
  unfold exteriorKernelBound
  positivity

theorem distance_compl_interval {a b d x y : ℝ} (hx : x ∈ Icc (a+d) (b-d))
    (hy : y ∉ Icc a b) : d ≤ |y-x| := by
  rcases not_and_or.mp hy with hya | hyb
  · have hya' : y < a := lt_of_not_ge hya
    have ht := neg_le_abs (y-x)
    linarith [hx.1]
  · have hyb' : b < y := lt_of_not_ge hyb
    have ht := le_abs_self (y-x)
    linarith [hx.2]

theorem exteriorKernel_le_cauchy {d x y : ℝ} (hd : 0 < d)
    (hx : |x| ≤ 1) (hsep : d ≤ |y-x|) (h : ℝ) :
    1/((y-x)^2+h^2) ≤ exteriorKernelBound d * poissonKernel 1 y := by
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hdist : d^2 ≤ (y-x)^2 := by nlinarith [sq_abs (y-x)]
  have hden : 0 < (y-x)^2+h^2 := by nlinarith [sq_nonneg h]
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hy2 : y^2+1 ≤ 2*(y-x)^2+3 := by nlinarith [sq_nonneg (y-2*x)]
  have hp : d^2*(y^2+1) ≤ (2*d^2+3)*((y-x)^2+h^2) := by
    have hmul := mul_le_mul_of_nonneg_left hy2 hd2.le
    nlinarith [sq_nonneg h, mul_nonneg hd2.le (sq_nonneg h)]
  unfold exteriorKernelBound poissonKernel
  norm_num only [one_pow]
  field_simp
  nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hp)]

theorem exteriorKernel_height_difference {d t h : ℝ} (hd : 0 < d)
    (ht : d ≤ |t|) :
    |1/(t^2+h^2)-1/t^2| ≤ (h^2/d^2)*(1/t^2) := by
  have ht2 : 0 < t^2 := by nlinarith [sq_abs t]
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht2
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hden : 0 < t^2+h^2 := by positivity
  have hdle : d^2 ≤ t^2+h^2 := by nlinarith [sq_abs t, sq_nonneg h]
  have hnonpos : 1/(t^2+h^2)-1/t^2 ≤ 0 := by
    apply sub_nonpos.mpr
    exact one_div_le_one_div_of_le ht2 (by nlinarith [sq_nonneg h])
  rw [abs_of_nonpos hnonpos]
  have he : -(1/(t^2+h^2)-1/t^2) = (h^2/(t^2+h^2))*(1/t^2) := by
    field_simp [ht0]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_div_of_nonneg_left (sq_nonneg h) hd2 hdle

theorem exteriorKernel_horizontal_difference {d s t : ℝ} (hd : 0 < d)
    (hs : d ≤ |s|) (ht : d ≤ |t|) :
    |1/s^2-1/t^2| ≤ (|s-t|/d)*(1/s^2+1/t^2) := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs; linarith
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
  have he : |1/s^2-1/t^2| = |s-t| *|s+t|/(s^2*t^2) := by
    rw [div_sub_div _ _ (pow_ne_zero 2 hs0) (pow_ne_zero 2 ht0)]
    rw [abs_div, abs_of_pos (mul_pos (sq_pos_of_ne_zero hs0) (sq_pos_of_ne_zero ht0))]
    congr 1
    simp only [one_mul, mul_one]
    rw [show t^2-s^2 = -(s-t)*(s+t) by ring, abs_mul, abs_neg]
  rw [he]
  have hsum : d*|s+t| ≤ s^2+t^2 := by
    have ha := abs_add_le s t
    have h1 := mul_le_mul_of_nonneg_right hs (abs_nonneg s)
    have h2 := mul_le_mul_of_nonneg_right ht (abs_nonneg t)
    have h3 := mul_le_mul_of_nonneg_left ha hd.le
    nlinarith [sq_abs s, sq_abs t]
  apply (div_le_iff₀ (mul_pos (sq_pos_of_ne_zero hs0) (sq_pos_of_ne_zero ht0))).mpr
  have hre : (|s-t|/d)*(1/s^2+1/t^2)*(s^2*t^2) = |s-t|/d*(s^2+t^2) := by
    field_simp
    ring
  rw [hre, div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (s-t))]

end Erdos1132
