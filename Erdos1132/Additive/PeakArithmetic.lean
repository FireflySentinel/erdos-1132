import Erdos1132.Additive.BernsteinError

/-! # Quantitative transfer from a large derivative to the Riesz peak

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Real
namespace Erdos1132

theorem frequency_ratio_lower {ρ c t A K q : ℝ} (hc : 0 < c) (hρ : c ≤ ρ) (ht : 0 < t)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hq : A-K ≤ q) :
    A-K-A/(c*t) ≤ q*(ρ/(ρ+1/t)) := by
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hden : 0 < ρ+1/t := by positivity
  have hθ0 : 0 ≤ ρ/(ρ+1/t) := div_nonneg hρ0.le hden.le
  have hθ1 : ρ/(ρ+1/t) ≤ 1 := (div_le_one hden).mpr (by linarith [one_div_pos.mpr ht])
  have hθ : 1-1/(c*t) ≤ ρ/(ρ+1/t) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right hρ (show 0 ≤ 1/(c*t) by positivity)
    have he : c*(1/(c*t)) = 1/t := by field_simp
    rw [he] at hm
    have hp := mul_nonneg (show 0 ≤ 1/t by positivity) (show 0 ≤ 1/(c*t) by positivity)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hθ hA
  have h2 := mul_le_mul_of_nonneg_left hθ1 hK
  have h3 := mul_le_mul_of_nonneg_right hq hθ0
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem peak_deficit_bound {M A Q ω e K : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (hMA : A ≤ M) (hM1 : M ≤ A+1) (hQ : A-K-1 ≤ Q/ω) (he : M*e ≤ 1) :
    A-(Real.pi^2/4)*(K+3) ≤ M*(1-(Real.pi^2/4)*(1-Q/(ω*M)+e)) := by
  have hid : M*(1-Q/(ω*M)+e) = M-Q/ω+M*e := by field_simp
  have hdef : M*(1-Q/(ω*M)+e) ≤ K+3 := by rw [hid]; linarith
  have hp := mul_le_mul_of_nonneg_left hdef (show 0 ≤ Real.pi^2/4 by positivity)
  nlinarith

end Erdos1132
