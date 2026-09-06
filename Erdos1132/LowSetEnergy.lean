import Erdos1132.LocalLowBound
import Erdos1132.ProofParameters
import Erdos1132.RatioEnergy

noncomputable section

open MeasureTheory Set Complex

namespace Erdos1132

theorem row_energy_bound (n : ℕ) (X : Nodes (n + 2)) {a b c K q δ R : ℝ}
    (hb : 0 < b) (hba : b < a) (hc : 0 ≤ c) (hK : 0 < K) (hq : 0 < q)
    (hR : 0 < R) (hRt : 2 / (Real.pi * R) < q / 4)
    (hst : ∀ z : ℂ, ‖z + I‖ < δ → (1 + q) / 2 < intervalHarmonic (-K) K z)
    {E : Set ℝ} (hE : MeasurableSet E) (hEint : E ⊆ Icc (-1) 1)
    (hsmall : ∀ x ∈ E, ‖X.signedCauchy ((x : ℂ) + height a n * I)‖ /
      (X.probability (by omega)).gamma (height a n) x < δ)
    (hlow : ∀ y ∈ E, X.lebesgue y ≤ c * Real.log (rowSize n)) :
    kernelEnergy (logKernel (height a n) (height b n))
      (goodSet (poissonKernel (height a n)) E (q / 4)) ≤
    energyCoefficient c K R a b n * volume.real (goodSet (poissonKernel (height a n)) E (q / 4)) := by
  let h := height a n
  let η := height b n
  let μ := X.probability (by omega)
  have hh : 0 < h := height_pos a n
  have hη : 0 < η := height_pos b n
  have hhη : h < η := height_antitone hba n
  have hη1 : η < 1 := height_lt_one hb n
  apply kernelEnergy_le_of_ratio_bound (continuous_logKernel hη hhη) (integrable_logKernel hη hhη)
    (logKernel_nonneg hη hhη hη1) (logKernel_neg h η) (μ.continuous_gamma hh) (μ.gamma_pos hh)
    (fun y => by rw [abs_of_pos (μ.gamma_pos hh y)]; exact μ.gamma_le_one_div hh y)
    (measurable_goodSet (continuous_poissonKernel hh).measurable hE _)
    ((goodSet_subset _ _ _).trans hEint)
  intro x hx
  have hlow' := X.truncatedPotential_low_bound (by omega) hh hhη hη1 hK hq hR hRt
    (mul_nonneg hc (log_rowSize_pos n).le) hst (hsmall x hx.1) hE hlow hx
  rw [μ.truncatedPotential_operator hh hhη hη1 x] at hlow'
  change (2 / Real.pi) * (-Real.log (height b n)) *
    (∫ y, logKernel h η (x - y) * μ.gamma h y) ≤
    (1 + R * h / η) ^ 2 * (c * Real.log (rowSize n)) * K * μ.gamma h x at hlow'
  rw [neg_log_height] at hlow'
  have hd : 0 < (2 / Real.pi) * (b * Real.log (rowSize n)) := by
    have := log_rowSize_pos n
    positivity
  apply (div_le_iff₀ (μ.gamma_pos hh x)).mpr
  calc
    _ ≤ ((1 + R * h / η) ^ 2 * (c * Real.log (rowSize n)) * K * μ.gamma h x) /
        ((2 / Real.pi) * (b * Real.log (rowSize n))) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith [hlow']
    _ = energyCoefficient c K R a b n * μ.gamma h x := by
      have hl := (log_rowSize_pos n).ne'
      unfold energyCoefficient localizationFactor
      dsimp only [h, η]
      field_simp

end Erdos1132
