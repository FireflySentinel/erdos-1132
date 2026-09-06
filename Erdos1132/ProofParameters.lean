import Erdos1132.Scales

noncomputable section

open Filter
open scoped Topology

namespace Erdos1132

theorem exists_proof_parameters {c : ℝ} (hc : 0 < c) (hcπ : c < 2 / Real.pi) :
    ∃ K b a : ℝ, 1 < K ∧ 0 < b ∧ b < a ∧ a < 1 ∧ Real.pi * c * K / (2 * b) < 1 := by
  have hpc : Real.pi * c < 2 := by
    have := (lt_div_iff₀ Real.pi_pos).mp hcπ
    nlinarith
  have hbound : 1 < 2 / (Real.pi * c) := (lt_div_iff₀ (mul_pos Real.pi_pos hc)).mpr (by simpa)
  obtain ⟨K, hK, hKu⟩ := exists_between hbound
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hprod : Real.pi * c * K / 2 < 1 := by
    have := (lt_div_iff₀ (mul_pos Real.pi_pos hc)).mp hKu
    nlinarith
  obtain ⟨b, hb, hb1⟩ := exists_between hprod
  have hb0 : 0 < b := (by positivity : 0 < Real.pi * c * K / 2).trans hb
  obtain ⟨a, hba, ha1⟩ := exists_between hb1
  refine ⟨K, b, a, hK, hb0, hba, ha1, ?_⟩
  exact (div_lt_one (by positivity)).mpr (by linarith)

def localizationFactor (R a b : ℝ) (n : ℕ) : ℝ := (1 + R * height a n / height b n) ^ 2

def energyCoefficient (c K R a b : ℝ) (n : ℕ) : ℝ :=
  (Real.pi * c * K / (2 * b)) * localizationFactor R a b n

theorem tendsto_localizationFactor (R : ℝ) {a b : ℝ} (hba : b < a) :
    Tendsto (localizationFactor R a b) atTop (𝓝 1) := by
  have he := (((tendsto_height_ratio hba).const_mul R).const_add 1).pow 2
  convert! he using 1
  · funext n
    unfold localizationFactor
    ring
  · norm_num

theorem tendsto_energyCoefficient (c K R : ℝ) {a b : ℝ} (hba : b < a) :
    Tendsto (energyCoefficient c K R a b) atTop (𝓝 (Real.pi * c * K / (2 * b))) := by
  convert! (tendsto_localizationFactor R hba).const_mul (Real.pi * c * K / (2 * b)) using 1
  simp

theorem log_rowSize_pos (n : ℕ) : 0 < Real.log (rowSize n) :=
  Real.log_pos (by linarith [rowSize_ge_two n])

end Erdos1132
