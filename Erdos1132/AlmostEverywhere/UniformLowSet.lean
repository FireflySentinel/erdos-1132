import Erdos1132.AlmostEverywhere.LowSetEnergy

/-! # The null-set contradiction and the set corollary

Main paper: §3, Theorem 1(ii), and the positive-measure corollary in §7.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

namespace Erdos1132

/-- No positive-measure set supports a uniform bound below the sharp constant infinitely often. -/
theorem uniform_low_set_null (X : ∀ n, Nodes (n + 2)) {c : ℝ}
    (hc : 0 < c) (hcπ : c < 2 / Real.pi) {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : E ⊆ Icc (-1) 1)
    (hlow : ∃ᶠ n in atTop, ∀ x ∈ E, (X n).lebesgue x ≤ c * Real.log (rowSize n)) :
    volume E = 0 := by
  by_contra hpos
  have hEfin := interval_subset_finite hEint
  have hEpos : 0 < volume.real E := ENNReal.toReal_pos hpos hEfin
  obtain ⟨K, b, a, hK, hb, hba, ha1, hcoef⟩ := exists_proof_parameters hc hcπ
  have ha : 0 < a := hb.trans hba
  have hK0 : 0 < K := zero_lt_one.trans hK
  obtain ⟨q, hq, δ, hδ, hstable⟩ := centered_probability_stable hK
  obtain ⟨R, hR, hRt⟩ := exists_localization_radius hq
  let F (n : ℕ) := goodSet (poissonKernel (height a n)) E (q / 4)
  let k (n : ℕ) := logKernel (height a n) (height b n)
  have hFm : ∀ n, MeasurableSet (F n) := fun n =>
    measurable_goodSet (continuous_poissonKernel (height_pos a n)).measurable hE _
  have hFE : ∀ n, F n ⊆ E := fun n => goodSet_subset _ _ _
  have hsmall : Tendsto (fun n => volume.real (E \ F n)) atTop (𝓝 0) :=
    measure_badSet_tendsto
      (fun n => (continuous_poissonKernel (height_pos a n)).measurable)
      (fun n t => (poissonKernel_pos (height_pos a n) t).le)
      (fun n => integrable_poissonKernel (height_pos a n).le)
      (fun n => integral_poissonKernel (height_pos a n))
      (fun δ hδ => tendsto_poissonKernel_tail ha hδ) hE hEfin (by positivity)
  have hmeasure := measure_subsets_tendsto hEfin hFm hFE hsmall
  have henergy : Tendsto (fun n => kernelEnergy (k n) (F n)) atTop (𝓝 (volume.real E)) :=
    changing_kernelEnergy_tendsto
      (fun n => continuous_logKernel (height_pos b n) (height_antitone hba n))
      (fun n => logKernel_nonneg (height_pos b n) (height_antitone hba n) (height_lt_one hb n))
      (fun n => integrable_logKernel (height_pos b n) (height_antitone hba n))
      (fun n => logKernel_neg _ _)
      (fun n => integral_logKernel (height_pos b n) (height_antitone hba n) (height_lt_one hb n))
      (fun δ hδ => tendsto_logKernel_tail hb hba hδ) hE hEint hFm hFE hsmall
  have hcoeflim := (tendsto_energyCoefficient c K R hba).mul hmeasure
  have he : ∃ᶠ n in atTop, kernelEnergy (k n) (F n) ≤
      energyCoefficient c K R a b n * volume.real (F n) := by
    apply (hlow.and_eventually ((eventually_cancellation_bound ha ha1).and
      ((tendsto_cancellationError ha1).eventually (gt_mem_nhds hδ)))).mono
    rintro n ⟨hnlow, hn, hδn⟩
    apply row_energy_bound n (X n) hb hba hc.le hK0 hq hR hRt hstable hE hEint _ hnlow
    intro x hx
    exact (hn (X n) x (hEint hx)).trans_lt hδn
  have hcontr := le_of_tendsto_of_tendsto_of_frequently henergy hcoeflim he
  nlinarith

/-- Every positive-measure set contains a point above the lower bound in every sufficiently large row. -/
theorem eventually_exists_lower_bound (X : ∀ n, Nodes (n + 2)) {c : ℝ}
    (hc : 0 < c) (hcπ : c < 2 / Real.pi) {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : E ⊆ Icc (-1) 1) (hEpos : 0 < volume E) :
    ∀ᶠ n in atTop, ∃ x ∈ E, c * Real.log (rowSize n) < (X n).lebesgue x := by
  by_contra hnot
  have hlow : ∃ᶠ n in atTop, ∀ x ∈ E, (X n).lebesgue x ≤ c * Real.log (rowSize n) := by
    simpa only [not_eventually, not_exists, not_and, not_lt] using hnot
  exact (ne_of_gt hEpos) (uniform_low_set_null X hc hcπ hE hEint hlow)

end Erdos1132
