import Erdos1132.RieszKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Exact local mass of the regularized inverse-distance kernel -/

noncomputable section
open Real MeasureTheory Set
namespace Erdos1132

theorem rieszKernel_rescale {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    rieszKernel ε t = (1/Real.sqrt (1+(t/ε)^2))/ε := by
  have he : t^2+ε^2 = (1+(t/ε)^2)*ε^2 := by field_simp; ring
  rw [rieszKernel, he, Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le]
  ring

theorem hasDerivAt_arsinh_riesz {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arsinh (t/ε)) (rieszKernel ε t) t := by
  have h := (Real.hasDerivAt_arsinh (t/ε)).comp t ((hasDerivAt_id t).div_const ε)
  simpa only [rieszKernel_rescale hε, one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using h

theorem integral_rieszKernel_unit {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Icc (-1:ℝ) 1, rieszKernel ε t) = 2*Real.arsinh (1/ε) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_arsinh_riesz hε t)
      ((continuous_rieszKernel hε).intervalIntegrable _ _)]
  rw [neg_div, Real.arsinh_neg]
  ring

theorem arsinh_inverse_log {ε : ℝ} (hε : 0 < ε) :
    Real.arsinh (1/ε) = Real.log (1/ε) + Real.log (1+Real.sqrt (1+ε^2)) := by
  have hs : Real.sqrt (1+(1/ε)^2) = Real.sqrt (1+ε^2)/ε := by
    have he : 1+(1/ε)^2 = (1+ε^2)/ε^2 := by field_simp; ring
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hε.le]
  rw [Real.arsinh, hs]
  have he : 1/ε+Real.sqrt (1+ε^2)/ε = (1/ε)*(1+Real.sqrt (1+ε^2)) := by ring
  rw [he, Real.log_mul (by positivity) (by positivity)]

theorem integral_rieszKernel_unit_error {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)-2*Real.log (1/ε)| ≤ 2*Real.log 3 := by
  rw [integral_rieszKernel_unit hε, arsinh_inverse_log hε]
  have hs0 := Real.sqrt_nonneg (1+ε^2)
  have hs2 : Real.sqrt (1+ε^2) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith [sq_nonneg ε]
  have hl0 : 0 ≤ Real.log (1+Real.sqrt (1+ε^2)) := Real.log_nonneg (by linarith)
  have hl3 : Real.log (1+Real.sqrt (1+ε^2)) ≤ Real.log 3 :=
    Real.log_le_log (by positivity) (by linarith)
  rw [show 2*(Real.log (1/ε)+Real.log (1+Real.sqrt (1+ε^2)))-2*Real.log (1/ε) =
    2*Real.log (1+Real.sqrt (1+ε^2)) by ring, abs_of_nonneg (by positivity)]
  linarith

end Erdos1132
