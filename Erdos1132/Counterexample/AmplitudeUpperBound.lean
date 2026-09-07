import Erdos1132.Counterexample.AmplitudeSumEstimate
import Erdos1132.Counterexample.PhaseSum
import Erdos1132.Counterexample.UniformRemainder
import Erdos1132.Counterexample.CoordinateIntegral
import Erdos1132.Counterexample.AmplitudeWeight

/-!
# The amplitude upper bound on an interior angle interval

The quadrature estimate, exact integral and harmonic bound combine with one
absolute additive constant. Nodes themselves are included in the estimate.
-/

noncomputable section

open Set Filter Polynomial Finset MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Erdos1132.Counterexample

theorem eventually_coordinate_row_upper {ψ v : ℝ → ℝ} {B a : ℝ}
    (hB : 0 < B) (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0)
    (hv : ∀ y ∈ Set.Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ v y)
    (hvpos : ∀ y ∈ Set.Icc (-1 : ℝ) 1, 0 < v y)
    (ha : 0 < a) (haπ : a ≤ Real.pi-a) :
    ∀ᶠ n : ℕ in atTop, ∀ Y : Nodes n,
      (∀ i, Y.point i = phaseCoordinate ψ ((n : ℝ)⁻¹, phaseMidpoint n i)) →
      (∀ s : ℝ, (∀ i, phaseCoordinate ψ ((n : ℝ)⁻¹, s) ≠ Y.point i) →
        let X := fun t => phaseCoordinate ψ ((n : ℝ)⁻¹, t)
        Y.lebesgue (X s) = |Real.cos (n*s)|/(n*v (X s)) *
          ∑ i : Fin n, v (X (phaseMidpoint n i))*|deriv X (phaseMidpoint n i)| /
            |X s - X (phaseMidpoint n i)|) →
      ∀ s ∈ Set.Icc a (Real.pi-a),
        let x := phaseCoordinate ψ ((n : ℝ)⁻¹, s)
        Y.lebesgue x ≤ 2/Real.pi*Real.log n + 3 - logarithmicOperator v x/(Real.pi*v x) := by
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (show (-1 : ℝ) ≤ 1 by norm_num))
    (fun y hy => (hv y hy).continuousAt.continuousWithinAt)
  let m₀ := v z
  have hm₀ : 0 < m₀ := hvpos z hz
  have hminv : ∀ y ∈ Set.Icc (-1 : ℝ) 1, m₀ ≤ v y := hmin
  obtain ⟨M, hM2, hM⟩ := exists_uniform_analytic_jet_bound hv 1
  have hM0 : 0 ≤ M := by linarith
  have hv1 : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |deriv v y| ≤ M := by
    simpa only [iteratedDeriv_one] using hM 1 le_rfl
  let K := 2*M/(Real.pi*m₀)
  have hKbound {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
      logarithmicOperator v y/(Real.pi*v y) ≤ K := by
    have hh := abs_logarithmicOperator_le_of_derivative hM0
      (fun u hu => ((hv u hu).differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt) hv1 hy
    exact div_le_div₀ (by positivity) ((le_abs_self _).trans hh) (mul_pos Real.pi_pos hm₀)
      (mul_le_mul_of_nonneg_left (hminv y hy) Real.pi_pos.le)
  obtain ⟨C, hC, hquad⟩ := eventually_amplitudeRemainder_midpoint_error hB hψ hval hder h0 hπ hv
    ha haπ (by linarith)
  let E₀ := 1/a + 2*B/Real.pi + C/(Real.pi*m₀)
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, |(n : ℝ)⁻¹| * B < 1 := by
    have hh : ∀ᶠ ε : ℝ in 𝓝 0, |ε| * B < 1 :=
      (continuous_abs.mul continuous_const).continuousAt.eventually_lt_const (by simp)
    exact hinv.eventually hh
  have hlog : ∀ᶠ n : ℕ in atTop, K+1 ≤ 2/Real.pi*Real.log n :=
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by positivity : (0 : ℝ) < 2/Real.pi)).eventually (eventually_ge_atTop (K+1))
  have hsize : ∀ᶠ n : ℕ in atTop, max (Real.pi/a) (3*E₀) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hquad, hsmall, hlog, hsize, eventually_gt_atTop 0]
    with n hquad hε hlog hsize hn Y hY hformula s hs
  let X := fun t => phaseCoordinate ψ ((n : ℝ)⁻¹, t)
  have hx : X s ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hvs : 0 < v (X s) := hvpos _ hx
  have hlead : 1 ≤ 2/Real.pi*Real.log n - logarithmicOperator v (X s)/(Real.pi*v (X s)) := by
    linarith [hKbound hx]
  have hbkt : 0 ≤ 2/Real.pi*Real.log n - logarithmicOperator v (X s)/(Real.pi*v (X s)) + 2/Real.pi := by
    have : (0 : ℝ) < 2/Real.pi := by positivity
    linarith
  dsimp only
  change Y.lebesgue (X s) ≤ 2/Real.pi*Real.log n + 3 -
    logarithmicOperator v (X s)/(Real.pi*v (X s))
  by_cases hnode : ∃ i, X s = Y.point i
  · obtain ⟨i, hi⟩ := hnode
    rw [hi, Y.lebesgue_at_node]
    rw [hi] at hlead
    linarith
  · push Not at hnode
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hna : Real.pi ≤ (n : ℝ)*a :=
      (div_le_iff₀ ha).mp ((le_max_left _ _).trans hsize)
    have hleft : 1 ≤ (n : ℝ)*s/Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      nlinarith [hs.1]
    have hright : (n : ℝ)*s/Real.pi ≤ n-1 := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      nlinarith [hs.2]
    have hmid : ∀ i : Fin n, s ≠ phaseMidpoint n i := by
      intro i hi
      apply hnode i
      rw [hi, hY]
    obtain ⟨m, hm, hmn, t, ht, heq⟩ := exists_interior_phase_split hleft hright hmid
    have hΛ := lebesgue_coordinate_sum_decomposition hn hvs (hformula s hnode)
    let Q := (Real.pi/n)*∑ i : Fin n, amplitudeRemainder v X s (phaseMidpoint n i)
    let q := 1 - (n : ℝ)⁻¹*deriv ψ (phaseInverse ψ (n : ℝ)⁻¹ s)
    have hqpos : 0 < q := by
      have hh := (le_abs_self ((n : ℝ)⁻¹*deriv ψ (phaseInverse ψ (n : ℝ)⁻¹ s))).trans
        ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hder _) (abs_nonneg _)))
      dsimp [q]
      linarith
    have hqbound : q ≤ 1+B/n := by
      have hh := (neg_le_abs (deriv ψ (phaseInverse ψ (n : ℝ)⁻¹ s))).trans (hder _)
      have hmul := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hnR.le)
      have hhdiv : -((n : ℝ)⁻¹ * deriv ψ (phaseInverse ψ (n : ℝ)⁻¹ s)) ≤ B/n := by
        simpa only [mul_neg, div_eq_mul_inv, mul_comm] using hmul
      dsimp [q]
      linarith
    have hI := integral_phaseCoordinate_remainder hψ hval hder hε h0 hπ
      (show s ∈ Set.Ioo 0 Real.pi from ⟨ha.trans_le hs.1, by linarith [hs.2]⟩) hv
    have hQ : |Q - (-logarithmicOperator v (X s) +
        v (X s)*(2*Real.log q - Real.log (s*(Real.pi-s))))| ≤ C/n := by
      have hh := hquad s hs
      dsimp only at hh hI
      rw [hI] at hh
      simpa only [Q, phaseMidpoint, Fin.sum_univ_eq_sum_range
        (fun k : ℕ => amplitudeRemainder v X s (((k : ℝ)+1/2)*(Real.pi/n))) n] using hh
    have hupper := amplitude_sum_upper_bound hn hm hmn ha hs.1 (by linarith [hs.2])
      ht heq hvs hqpos hqbound hQ hΛ
    have hEbound : 1/(n*a) + 2*B/(Real.pi*n) + (C/n)/(Real.pi*v (X s)) ≤ E₀/n := by
      have hcdiv : (C/n)/(Real.pi*v (X s)) ≤ (C/n)/(Real.pi*m₀) :=
        div_le_div_of_nonneg_left (div_nonneg hC hnR.le) (mul_pos Real.pi_pos hm₀)
          (mul_le_mul_of_nonneg_left (hminv _ hx) Real.pi_pos.le)
      calc
        _ ≤ 1/(n*a) + 2*B/(Real.pi*n) + (C/n)/(Real.pi*m₀) := add_le_add le_rfl hcdiv
        _ = _ := by dsimp [E₀]; ring
    have hEthird : E₀/n ≤ 1/3 := by
      apply (div_le_iff₀ hnR).mpr
      have hh := (le_max_right _ _).trans hsize
      linarith
    have hb : |Real.cos (n*s)| ≤ 1 := Real.abs_cos_le_one _
    have hterm := mul_le_mul_of_nonneg_left hEbound (abs_nonneg (Real.cos (n*s)))
    have hterm' := mul_le_mul_of_nonneg_right hb (div_nonneg hE₀ hnR.le)
    have hmain := mul_le_mul_of_nonneg_right hb hbkt
    have hpi : 2/Real.pi ≤ (2/3 : ℝ) :=
      (div_le_iff₀ Real.pi_pos).mpr (by nlinarith [Real.pi_gt_three])
    linarith

end Erdos1132.Counterexample
