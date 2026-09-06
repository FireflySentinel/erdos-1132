import Erdos1132.PoissonLocalization
import Erdos1132.BoundaryEvents
import Erdos1132.ChangingSets

noncomputable section

open MeasureTheory Set Complex

namespace Erdos1132.Nodes

variable {n : ℕ} (X : Nodes n)

theorem absoluteTransform_eq_lebesgue_mul (hn : 0 < n) {y : ℝ} (hy : ∀ i, y ≠ X.point i) :
    X.absoluteTransform y = X.lebesgue y * |X.signedBoundary y| := by
  have hg : X.signedBoundary y ≠ 0 := by
    rw [X.signedBoundary_eq hn hy]
    exact one_div_ne_zero (mul_ne_zero (X.totalWeight_pos hn).ne' (X.nodePolynomial_ne_zero hy))
  have he := X.lebesgue_transform hn hy
  exact ((eq_div_iff (abs_ne_zero.mpr hg)).mp he).symm

theorem truncatedPotential_low_bound (hn : 2 ≤ n) {h η K q δ R L x : ℝ}
    (hh : 0 < h) (hhη : h < η) (hη1 : η < 1) (hK : 0 < K) (hq : 0 < q)
    (hR : 0 < R) (hRt : 2 / (Real.pi * R) < q / 4) (hL : 0 ≤ L)
    (hst : ∀ z : ℂ, ‖z + I‖ < δ → (1 + q) / 2 < intervalHarmonic (-K) K z)
    (hsmall : ‖X.signedCauchy ((x : ℂ) + h * I)‖ /
      (X.probability (by omega)).gamma h x < δ)
    {E : Set ℝ} (hE : MeasurableSet E) (hlow : ∀ y ∈ E, X.lebesgue y ≤ L)
    (hx : x ∈ goodSet (poissonKernel h) E (q / 4)) :
    (X.probability (by omega)).truncatedPotential η x ≤
      (1 + R * h / η) ^ 2 * L * K * (X.probability (by omega)).gamma h x := by
  let μ := X.probability (by omega)
  let γ := μ.gamma h x
  let u := (μ.cauchy ((x : ℂ) + h * I)).re
  have hγ : 0 < γ := μ.gamma_pos hh x
  have hη := hh.trans hhη
  have hev := X.split_event_probabilities hn hK hh hst hsmall
  obtain ⟨y, hyE, hyT, hyP, hyM, hyZ⟩ := exists_in_two_events
    ((integrable_poissonKernel hh.le).comp_sub_left x)
    (fun y => (poissonKernel_pos hh (x - y)).le)
    (by rw [integral_sub_left_eq_self, integral_poissonKernel hh])
    ((X.plusProbability hn).measurable_intervalEvent (u - K * γ) (u + K * γ))
    ((X.minusProbability hn).measurable_intervalEvent (u - K * γ) (u + K * γ)) hE measurableSet_Icc
    (Z := range X.point) ((Set.finite_range X.point).measure_zero volume)
    hev.1 hev.2 hx.2 ((translated_poisson_tail hh hR x).trans_lt hRt) hq.le
  have hyn : ∀ i, y ≠ X.point i := fun i he => hyZ ⟨i, he.symm⟩
  have hg : |X.signedBoundary y| < K * γ := X.signedBoundary_small_on_intersection hn hyP hyM
  have hdist : |x - y| ≤ R * h := abs_le.mpr ⟨by linarith [hyT.2], by linarith [hyT.1]⟩
  have hfac : (1 + |x - y| / η) ^ 2 ≤ (1 + R * h / η) ^ 2 := by
    gcongr
  calc
    μ.truncatedPotential η x ≤ (1 + |x - y| / η) ^ 2 * μ.truncatedPotential η y :=
      μ.truncatedPotential_local hη hη1.le x y
    _ ≤ (1 + R * h / η) ^ 2 * μ.truncatedPotential η y :=
      mul_le_mul_of_nonneg_right hfac (μ.truncatedPotential_nonneg hη hη1.le y)
    _ ≤ (1 + R * h / η) ^ 2 * X.absoluteTransform y :=
      mul_le_mul_of_nonneg_left (μ.truncatedPotential_le_absolute hη hη1.le hyn) (sq_nonneg _)
    _ = (1 + R * h / η) ^ 2 * (X.lebesgue y * |X.signedBoundary y|) := by
      rw [X.absoluteTransform_eq_lebesgue_mul (by omega) hyn]
    _ ≤ (1 + R * h / η) ^ 2 * (L * (K * γ)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul (hlow y hyE) hg.le (abs_nonneg _) hL
    _ = _ := by ring

end Erdos1132.Nodes
