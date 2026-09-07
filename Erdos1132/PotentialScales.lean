import Erdos1132.PotentialNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Explicit choices of scales for the local potential expansion -/

noncomputable section
open Set Filter Real
open scoped Topology
namespace Erdos1132

def potentialErrorSize (n : ℕ) : ℝ := (1+Real.log n)/n

theorem tendsto_potentialErrorSize : Tendsto potentialErrorSize atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have hinv := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  convert! hinv.add hlog using 1
  · ext n
    simp [potentialErrorSize, add_div]
  · simp

def normalizationBound (a b : ℝ) : ℝ :=
  Real.log 2+2+(4+logSquareBound)/(2*(b-a))

theorem normalizationBound_pos {a b : ℝ} (hab : a < b) : 0 < normalizationBound a b := by
  have hB := logSquareBound_nonneg
  unfold normalizationBound
  positivity

theorem potentialErrorSize_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ potentialErrorSize n := by
  unfold potentialErrorSize
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith [Real.log_nonneg hn1]) (Nat.cast_nonneg _)

theorem local_log_error_scale {N : ℝ} (hN : 1 ≤ N) :
    max (Real.log (2*N)) (-Real.log (1/N^5))/N ≤
      (5+Real.log 2)*((1+Real.log N)/N) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne', Real.log_div one_ne_zero (pow_ne_zero _ hN0.ne'),
    Real.log_one, Real.log_pow]
  have hlog := Real.log_nonneg hN
  have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  apply (div_le_iff₀ hN0).mpr
  have he : (5+Real.log 2)*((1+Real.log N)/N)*N = (5+Real.log 2)*(1+Real.log N) := by field_simp
  rw [he]
  apply max_le <;> push_cast <;> nlinarith [mul_nonneg hlog2 hlog]

theorem small_set_error_scale {N A B h : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 1/N ≤ h) :
    (Real.sqrt (2*N*(1/N^5)*B)+A*(2*N*(1/N^5)))/(Real.pi*h) ≤
      ((Real.sqrt (2*B)+2*A)/Real.pi)/N := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hh0 : 0 < h := (one_div_pos.mpr hN0).trans_le hh
  have hnum : 2*N*(1/N^5)*B = (2*B)/(N^2)^2 := by field_simp
  have hnum2 : 2*N*(1/N^5) = 2/N^4 := by field_simp
  rw [hnum, Real.sqrt_div (by positivity : 0 ≤ 2*B), Real.sqrt_sq (sq_nonneg N), hnum2]
  have hpow : N^2 ≤ N^4 := by nlinarith [sq_nonneg (N^2-1)]
  have hnsmall : A*(2/N^4) ≤ 2*A/N^2 := by
    have hb := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
      (sq_pos_of_pos hN0) hpow
    convert! hb using 1 <;> ring
  have hsum : Real.sqrt (2*B)/N^2+A*(2/N^4) ≤ (Real.sqrt (2*B)+2*A)/N^2 := by
    rw [add_div]
    linarith
  have hden : Real.pi/N ≤ Real.pi*h := by
    have hm := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
    simpa only [mul_one_div] using hm
  calc
    _ ≤ ((Real.sqrt (2*B)+2*A)/N^2)/(Real.pi*h) :=
      div_le_div_of_nonneg_right hsum (mul_pos Real.pi_pos hh0).le
    _ ≤ ((Real.sqrt (2*B)+2*A)/N^2)/(Real.pi/N) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos Real.pi_pos hN0) hden
    _ = _ := by field_simp

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem abs_potentialNormalization_le (hn : 0 < n) {a b : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hΛ : ∀ y ∈ Icc a b, X.lebesgue y ≤ n) :
    |X.potentialNormalization| ≤ normalizationBound a b := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlo := X.potentialNormalization_lower hn
  have hhi := X.potentialNormalization_upper hn hab hI hΛ
  have hlog : Real.log (2*n)/n ≤ 2 := by
    apply (div_le_iff₀ hnR).mpr
    exact (Real.log_le_sub_one_of_pos (by positivity : 0 < (2 : ℝ)*n)).trans (by linarith)
  have hC : 0 ≤ (4+logSquareBound)/(2*(b-a)) := by
    have hB := logSquareBound_nonneg
    positivity
  unfold normalizationBound
  apply abs_le.mpr
  constructor <;> linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

end Nodes
end Erdos1132
