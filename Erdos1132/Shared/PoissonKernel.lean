import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

/-! # The Poisson kernel and its mass

Paper: Shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace Erdos1132

def poissonKernel (h t : ℝ) : ℝ := h / (Real.pi * (t ^ 2 + h ^ 2))

theorem poissonKernel_pos {h : ℝ} (hh : 0 < h) (t : ℝ) : 0 < poissonKernel h t := by
  unfold poissonKernel
  positivity

theorem poissonKernel_neg (h t : ℝ) : poissonKernel h (-t) = poissonKernel h t := by
  simp [poissonKernel]

theorem continuous_poissonKernel {h : ℝ} (hh : 0 < h) : Continuous (poissonKernel h) := by
  unfold poissonKernel
  exact continuous_const.div (by fun_prop) (fun t => ne_of_gt (by positivity))

theorem poissonKernel_eq_cauchyPDF {h : ℝ} (hh : 0 ≤ h) :
    poissonKernel h = ProbabilityTheory.cauchyPDFReal 0 ⟨h, hh⟩ := by
  ext t
  change h / (Real.pi * (t ^ 2 + h ^ 2)) =
    Real.pi⁻¹ * h * ((t - 0) ^ 2 + h ^ 2)⁻¹
  simp only [sub_zero, div_eq_mul_inv, mul_inv_rev]
  ring

theorem integrable_poissonKernel {h : ℝ} (hh : 0 ≤ h) : Integrable (poissonKernel h) := by
  rw [poissonKernel_eq_cauchyPDF hh]
  exact ProbabilityTheory.integrable_cauchyPDFReal _

theorem integral_poissonKernel {h : ℝ} (hh : 0 < h) : ∫ t, poissonKernel h t = 1 := by
  rw [poissonKernel_eq_cauchyPDF hh.le]
  apply ProbabilityTheory.integral_cauchyPDFReal_eq_one 0
  change (⟨h, hh.le⟩ : ℝ≥0) ≠ 0
  intro he
  have he' := congrArg (fun a : ℝ≥0 => (a : ℝ)) he
  exact hh.ne' he'

theorem hasDerivAt_poissonPrimitive {h : ℝ} (hh : 0 < h) (x t : ℝ) :
    HasDerivAt (fun y => Real.arctan ((y - x) / h) / Real.pi) (poissonKernel h (t - x)) t := by
  convert! (((((hasDerivAt_id t).sub_const x).div_const h).arctan).div_const Real.pi) using 1
  unfold poissonKernel
  field_simp
  dsimp only [id_eq]
  ring

theorem intervalIntegral_poissonKernel {h : ℝ} (hh : 0 < h) (x a b : ℝ) :
    (∫ t in a..b, poissonKernel h (t - x)) =
      (Real.arctan ((b - x) / h) - Real.arctan ((a - x) / h)) / Real.pi := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_poissonPrimitive hh x t)
    (((continuous_poissonKernel hh).comp (continuous_id.sub continuous_const)).intervalIntegrable a b)]
  ring

theorem integral_poissonKernel_Icc {h : ℝ} (hh : 0 < h) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Icc a b, poissonKernel h t) =
      (Real.arctan (b / h) - Real.arctan (a / h)) / Real.pi := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simpa using intervalIntegral_poissonKernel hh 0 a b

theorem poissonKernel_centered_interval {h : ℝ} (hh : 0 < h) {K : ℝ} (hK : 0 ≤ K) :
    (∫ t in Set.Icc (-K * h) (K * h), poissonKernel h t) =
      2 / Real.pi * Real.arctan K := by
  rw [integral_poissonKernel_Icc hh (by nlinarith)]
  simp only [mul_div_cancel_right₀ _ hh.ne', Real.arctan_neg]
  ring

end Erdos1132
