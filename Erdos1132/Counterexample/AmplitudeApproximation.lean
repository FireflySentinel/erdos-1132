import Erdos1132.Counterexample.PolynomialAmplitude
import Erdos1132.Counterexample.ReciprocalApproximation

/-!
# Approximating positive C¹ functions by zero-free amplitudes

Approximate the reciprocal by a positive real polynomial and reflect its
Joukowsky polynomial. The logarithmic ratio approximation is uniform on
the full closed interval.
-/

noncomputable section

open Set Polynomial MeasureTheory

namespace Erdos1132.Counterexample

theorem logarithmicOperator_congr_on_interval {f g : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ interval) (hfg : EqOn f g interval) :
    logarithmicOperator f x = logarithmicOperator g x := by
  unfold logarithmicOperator
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  simp only [differenceKernel, hfg hx, hfg hy]

/-- The amplitude approximation used in the construction of Theorem 2,
including actual existence of a zero-free real polynomial. -/
theorem exists_amplitude_logarithmicRatio_approximation {v v' : ℝ → ℝ}
    (hv : ∀ x ∈ interval, HasDerivWithinAt v (v' x) interval x)
    (hc' : ContinuousOn v' interval) (hpos : ∀ x ∈ interval, 0 < v x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ[X], 0 < h.coeff 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0) ∧
      ∀ x ∈ interval,
        |logarithmicOperator (amplitudeWeight h) x/amplitudeWeight h x -
          logarithmicOperator v x/v x| < ε := by
  let f := fun x => (v x)⁻¹
  let f' := fun x => -v' x/(v x)^2
  have hc : ContinuousOn v interval := fun x hx => (hv x hx).continuousWithinAt
  have hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x :=
    fun x hx => (hv x hx).inv (hpos x hx).ne'
  have hfc : ContinuousOn f' interval :=
    hc'.neg.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hpos x hx).ne')
  obtain ⟨p, hp, hratio⟩ := exists_reciprocal_polynomial_ratio_approximation hf hfc
    (fun x hx => inv_pos.mpr (hpos x hx)) hε
  obtain ⟨h, hh0, hhzero, hh⟩ := exists_polynomial_reciprocal_amplitude p hp
  refine ⟨h, hh0, hhzero, ?_⟩
  intro x hx
  rw [logarithmicOperator_congr_on_interval hx (fun y hy => hh y hy), hh x hx]
  simpa only [f, inv_inv] using hratio x hx

end Erdos1132.Counterexample
