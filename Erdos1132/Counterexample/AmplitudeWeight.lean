import Erdos1132.Counterexample.AmplitudePhase
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The positive analytic amplitude on the closed real interval

The squared modulus of a real polynomial on the unit circle is a polynomial
in the cosine coordinate. Its reciprocal square root supplies the amplitude
and is analytic at the endpoints as well as in the interior.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Polynomial Finset Set
open scoped ContDiff BigOperators

namespace Erdos1132.Counterexample

def amplitudeSquarePolynomial (h : ℝ[X]) : ℝ[X] :=
  ∑ r ∈ range (h.natDegree + 1), ∑ k ∈ range (h.natDegree + 1),
    C (h.coeff r * h.coeff k) * Polynomial.Chebyshev.T ℝ ((r : ℤ) - k)

def amplitudeWeight (h : ℝ[X]) (x : ℝ) : ℝ :=
  (Real.sqrt ((amplitudeSquarePolynomial h).eval x))⁻¹

theorem amplitudeSquarePolynomial_eval_cos (h : ℝ[X]) (θ : ℝ) :
    (amplitudeSquarePolynomial h).eval (Real.cos θ) =
      ‖(complexPolynomial h).eval (circlePoint θ)‖^2 := by
  have hre : ((complexPolynomial h).eval (circlePoint θ)).re =
      ∑ r ∈ range (h.natDegree + 1), h.coeff r * Real.cos ((r : ℝ)*θ) := by
    rw [complexPolynomial_eval_circlePoint]
    simp [circlePoint, Complex.exp_re, Complex.exp_im]
  have him : ((complexPolynomial h).eval (circlePoint θ)).im =
      ∑ r ∈ range (h.natDegree + 1), h.coeff r * Real.sin ((r : ℝ)*θ) := by
    rw [complexPolynomial_eval_circlePoint]
    simp [circlePoint, Complex.exp_re, Complex.exp_im]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  simp only [amplitudeSquarePolynomial, eval_finsetSum, eval_mul, eval_C,
    Polynomial.Chebyshev.T_real_cos, Int.cast_sub, Int.cast_natCast, sub_mul, Real.cos_sub]
  rw [sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  ring

theorem amplitudeWeight_cos (h : ℝ[X]) (θ : ℝ) :
    amplitudeWeight h (Real.cos θ) = ‖(complexPolynomial h).eval (circlePoint θ)‖⁻¹ := by
  rw [amplitudeWeight, amplitudeSquarePolynomial_eval_cos, Real.sqrt_sq (norm_nonneg _)]

theorem amplitudeSquarePolynomial_pos (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) : 0 < (amplitudeSquarePolynomial h).eval x := by
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  rw [← hcos, amplitudeSquarePolynomial_eval_cos]
  exact sq_pos_of_pos (norm_pos_iff.mpr (hzero _ (by simp)))

theorem amplitudeWeight_pos (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) : 0 < amplitudeWeight h x := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (amplitudeSquarePolynomial_pos h hzero hx))

theorem amplitudeWeight_contDiffAt (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) : ContDiffAt ℝ ⊤ (amplitudeWeight h) x := by
  have hp := amplitudeSquarePolynomial_pos h hzero hx
  have hc : ContDiffAt ℝ ⊤ (fun y => (amplitudeSquarePolynomial h).eval y) x := by
    simpa using ((amplitudeSquarePolynomial h).contDiff_aeval ⊤ (𝕜 := ℝ)).contDiffAt
  exact (hc.sqrt hp.ne').inv
    (Real.sqrt_pos.mpr hp).ne'

end Erdos1132.Counterexample
