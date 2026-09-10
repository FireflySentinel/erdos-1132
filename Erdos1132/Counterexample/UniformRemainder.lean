import Erdos1132.Counterexample.CoordinateBounds
import Erdos1132.Counterexample.AmplitudeRemainder

/-!
# Uniform quadrature for the actual amplitude remainder

Joint regularity of the inverse coordinates supplies derivative bounds on the
complete angle interval. The resulting variation bound is uniform both in the
interior angle parameter and in all sufficiently large degrees.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Erdos1132.Counterexample

theorem eventually_uniform_amplitudeRemainder_variation
    {ψ v : ℝ → ℝ} {B a b : ℝ}
    (hB : 0 < B) (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0)
    (hv : ∀ y ∈ Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ v y)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ ε : ℝ in 𝓝 0, ∀ s ∈ Icc a b,
      BoundedVariationOn (amplitudeRemainder v (fun t => phaseCoordinate ψ (ε, t)) s)
        (Icc 0 Real.pi) ∧
      IntervalIntegrable (amplitudeRemainder v (fun t => phaseCoordinate ψ (ε, t)) s)
        volume 0 Real.pi ∧
      (eVariationOn (amplitudeRemainder v (fun t => phaseCoordinate ψ (ε, t)) s)
        (Icc 0 Real.pi)).toReal ≤ V := by
  obtain ⟨M, hM2, hM⟩ := exists_uniform_analytic_jet_bound hv 2
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨d, hd, hden⟩ := eventually_uniform_coordinate_slope_bound hB hψ hval hder ha hab hb
  refine ⟨Real.pi*(M^3 + M^2 + 2*M^3/d^2) + 2*(M^2 + M^2/d), by positivity, ?_⟩
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, |ε| * B < 1 :=
    (continuous_abs.mul continuous_const).continuousAt.eventually_lt_const (by simp)
  filter_upwards [hden, hsmall,
    eventually_uniform_coordinate_derivative_bound hB hψ hval hder 1,
    eventually_uniform_coordinate_derivative_bound hB hψ hval hder 2,
    eventually_uniform_coordinate_derivative_bound hB hψ hval hder 3]
    with ε hden hε h1 h2 h3
  intro s hs
  have hs' : s ∈ Ioo 0 Real.pi := ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  apply amplitudeRemainder_variation hM0 hd hs'
    (phaseCoordinate_mem_Ioo hψ hval hder hε h0 hπ hs') hv
  · intro t _
    exact (phaseCoordinate_contDiffAt hψ hval hder hε).comp t
      (contDiffAt_const.prodMk contDiffAt_id)
  · intro t _
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · intro t ht
    exact phaseCoordinate_deriv_nonpos hψ hval hder hε h0 hπ ht
  · exact hden s hs
  · simpa only [iteratedDeriv_zero] using hM 0 (by norm_num)
  · simpa only [iteratedDeriv_one] using hM 1 (by norm_num)
  · exact hM 2 le_rfl
  · intro t ht
    simpa only [iteratedDeriv_one] using (h1 t ht).trans hM2
  · intro t ht
    exact (h2 t ht).trans hM2
  · intro t ht
    exact (h3 t ht).trans hM2

/-- The `C/n` estimate for the concrete remainder in the amplitude lemma (companion §3), with a single
constant for all interior parameters and all sufficiently large degrees. -/
theorem eventually_amplitudeRemainder_midpoint_error
    {ψ v : ℝ → ℝ} {B a b : ℝ}
    (hB : 0 < B) (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0)
    (hv : ∀ y ∈ Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ v y)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ s ∈ Icc a b,
      let X := fun t => phaseCoordinate ψ ((n : ℝ)⁻¹, t)
      |(Real.pi/n) * (∑ k ∈ Finset.range n,
          amplitudeRemainder v X s (((k : ℝ) + 1/2)*(Real.pi/n))) -
        ∫ t in (0 : ℝ)..Real.pi, amplitudeRemainder v X s t| ≤ C/n := by
  obtain ⟨V, hV0, hV⟩ := eventually_uniform_amplitudeRemainder_variation
    hB hψ hval hder h0 hπ hv ha hab hb
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine ⟨Real.pi*V, mul_nonneg Real.pi_pos.le hV0, ?_⟩
  filter_upwards [hinv.eventually hV, eventually_gt_atTop 0] with n hn hn0 s hs
  dsimp only
  have hh := (midpoint_quadrature_error_bound Real.pi_pos.le hn0
    (hn s hs).1 (hn s hs).2.1).trans
    (mul_le_mul_of_nonneg_left (hn s hs).2.2
      (div_nonneg Real.pi_pos.le (Nat.cast_nonneg n)))
  simpa only [div_mul_eq_mul_div] using hh

end Erdos1132.Counterexample
