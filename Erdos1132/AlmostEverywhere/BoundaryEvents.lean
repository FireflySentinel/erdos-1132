import Erdos1132.AlmostEverywhere.IntervalProbability

/-! # Boundary events for a positive Cauchy transform

Main paper: §3, Theorem 1(ii), and the positive-measure corollary in §7.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Erdos1132

theorem exists_in_two_events {p : ℝ → ℝ} (hp : Integrable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∫ y, p y = 1) {A B E T Z : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hE : MeasurableSet E) (hT : MeasurableSet T)
    (hZ : volume Z = 0) {q : ℝ}
    (ha : (1 + q) / 2 < ∫ y in A, p y) (hb : (1 + q) / 2 < ∫ y in B, p y)
    (he : (∫ y in Eᶜ, p y) < q / 4) (ht : (∫ y in Tᶜ, p y) < q / 4) (hq : 0 ≤ q) :
    ∃ y, y ∈ E ∧ y ∈ T ∧ y ∈ A ∧ y ∈ B ∧ y ∉ Z := by
  classical
  by_contra hn
  have hi : (∫ y in A, p y) + (∫ y in B, p y) ≤
      1 + (∫ y in Eᶜ, p y) + (∫ y in Tᶜ, p y) := by
    rw [← integral_indicator hA, ← integral_indicator hB, ← integral_indicator hE.compl,
      ← integral_indicator hT.compl, ← hp1,
      ← integral_add (hp.indicator hA) (hp.indicator hB),
      ← integral_add hp (hp.indicator hE.compl),
      ← integral_add (f := fun y => p y + Eᶜ.indicator p y) (hp.add (hp.indicator hE.compl)) (hp.indicator hT.compl)]
    apply integral_mono_ae ((hp.indicator hA).add (hp.indicator hB))
      ((hp.add (hp.indicator hE.compl)).add (hp.indicator hT.compl))
    have hz : ∀ᵐ y : ℝ, y ∉ Z := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hZ
    filter_upwards [hz] with y hy
    have hnot : ¬(y ∈ E ∧ y ∈ T ∧ y ∈ A ∧ y ∈ B) := fun hh => hn ⟨y, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, hy⟩
    by_cases hya : y ∈ A <;> by_cases hyb : y ∈ B <;>
      by_cases hye : y ∈ E <;> by_cases hyt : y ∈ T <;>
      simp [hya, hyb, hye, hyt] at hnot ⊢ <;> linarith [hp0 y]
  linarith

theorem normalized_cauchy_displacement {m g : ℂ} {γ : ℝ} (hγ : 0 < γ) (hm : -m.im = γ) :
    ‖(m + g - (m.re : ℂ)) / γ + I‖ = ‖g‖ / γ := by
  have hc : m = (m.re : ℂ) - γ * I := by
    apply Complex.ext <;> simp; linarith
  have he : (m + g - (m.re : ℂ)) / γ + I = g / γ := by
    have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    rw [hc]
    simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero]
    field_simp
    ring
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

def intervalEvent (u v : ℝ) : Set ℝ := {y | u < μ.boundary y ∧ μ.boundary y < v}

theorem measurable_boundary : Measurable μ.boundary := by
  unfold boundary
  fun_prop

theorem measurable_intervalEvent (u v : ℝ) : MeasurableSet (μ.intervalEvent u v) :=
  (measurableSet_lt measurable_const μ.measurable_boundary).inter
    (measurableSet_lt μ.measurable_boundary measurable_const)

theorem intervalEvent_probability {u v h : ℝ} (huv : u < v) (hh : 0 < h) (x : ℝ) :
    (∫ y in μ.intervalEvent u v, poissonKernel h (x - y)) =
      intervalHarmonic u v (μ.cauchy ((x : ℂ) + h * I)) := by
  rw [← μ.boundary_harmonic_measure huv hh x, ← integral_indicator (μ.measurable_intervalEvent u v)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : u < μ.boundary y ∧ μ.boundary y < v <;> simp [intervalEvent, hy]

end AtomicProbability

namespace Nodes

variable {n : ℕ} (X : Nodes n)

theorem boundary_plus (hn : 2 ≤ n) (y : ℝ) :
    (X.plusProbability hn).boundary y = (X.probability (by omega)).boundary y + X.signedBoundary y := by
  simp [AtomicProbability.boundary, plusProbability, probability, signedBoundary, add_div,
    Finset.sum_add_distrib]

theorem boundary_minus (hn : 2 ≤ n) (y : ℝ) :
    (X.minusProbability hn).boundary y = (X.probability (by omega)).boundary y - X.signedBoundary y := by
  simp [AtomicProbability.boundary, minusProbability, probability, signedBoundary, sub_div,
    Finset.sum_sub_distrib]

theorem signedBoundary_small_on_intersection (hn : 2 ≤ n) {u K γ y : ℝ}
    (hp : y ∈ (X.plusProbability hn).intervalEvent (u - K * γ) (u + K * γ))
    (hm : y ∈ (X.minusProbability hn).intervalEvent (u - K * γ) (u + K * γ)) :
    |X.signedBoundary y| < K * γ := by
  change u - K * γ < _ ∧ _ < u + K * γ at hp hm
  rw [X.boundary_plus hn y] at hp
  rw [X.boundary_minus hn y] at hm
  exact abs_lt.mpr ⟨by linarith [hp.1, hm.2], by linarith [hm.1, hp.2]⟩

theorem split_event_probabilities (hn : 2 ≤ n) {K q δ h x : ℝ}
    (hK : 0 < K) (hh : 0 < h)
    (hst : ∀ z : ℂ, ‖z + I‖ < δ → (1 + q) / 2 < intervalHarmonic (-K) K z)
    (hsmall : ‖X.signedCauchy ((x : ℂ) + h * I)‖ /
      (X.probability (by omega)).gamma h x < δ) :
    let γ := (X.probability (by omega)).gamma h x
    let u := ((X.probability (by omega)).cauchy ((x : ℂ) + h * I)).re
    ((1 + q) / 2 < ∫ y in (X.plusProbability hn).intervalEvent (u - K * γ) (u + K * γ),
      poissonKernel h (x - y)) ∧
    ((1 + q) / 2 < ∫ y in (X.minusProbability hn).intervalEvent (u - K * γ) (u + K * γ),
      poissonKernel h (x - y)) := by
  let μ := X.probability (by omega)
  let m := μ.cauchy ((x : ℂ) + h * I)
  let γ := μ.gamma h x
  have hγ : 0 < γ := μ.gamma_pos hh x
  have hm : -m.im = γ := μ.neg_im_cauchy h x
  have hp := hst ((m + X.signedCauchy ((x : ℂ) + h * I) - m.re) / γ)
    (by rw [normalized_cauchy_displacement hγ hm]; exact hsmall)
  have hm' := hst ((m + (-X.signedCauchy ((x : ℂ) + h * I)) - m.re) / γ)
    (by rw [normalized_cauchy_displacement hγ hm, norm_neg]; exact hsmall)
  have he (z : ℂ) : intervalHarmonic (m.re - K * γ) (m.re + K * γ) z =
      intervalHarmonic (-K) K ((z - m.re) / γ) := by
    simpa only [mul_neg, mul_comm γ, neg_mul, sub_eq_add_neg] using
      intervalHarmonic_affine (-K) K m.re hγ.ne' z
  constructor
  · rw [(X.plusProbability hn).intervalEvent_probability (by nlinarith) hh x,
      he, X.cauchy_plus hn]
    exact hp
  · rw [(X.minusProbability hn).intervalEvent_probability (by nlinarith) hh x,
      he, X.cauchy_minus hn]
    exact hm'

end Nodes
end Erdos1132
