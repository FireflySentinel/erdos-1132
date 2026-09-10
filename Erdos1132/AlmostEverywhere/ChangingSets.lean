import Erdos1132.AlmostEverywhere.EnergyComparison

/-! # Kernel energies on changing measurable sets

Main paper: §3, Theorem 1(ii), and the positive-measure corollary in §7.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos1132

def goodSet (k : ℝ → ℝ) (E : Set ℝ) (d : ℝ) : Set ℝ := E ∩ {x | kernelLeakage k E x < d}

theorem goodSet_subset (k : ℝ → ℝ) (E : Set ℝ) (d : ℝ) : goodSet k E d ⊆ E := inter_subset_left

theorem measurable_goodSet {k : ℝ → ℝ} (hk : Measurable k) {E : Set ℝ} (hE : MeasurableSet E) (d : ℝ) :
    MeasurableSet (goodSet k E d) :=
  hE.inter (measurableSet_lt (measurable_kernelLeakage hk E) measurable_const)

theorem measure_badSet_le {k : ℝ → ℝ} (hk : Measurable k) (hi : Integrable k) (hk0 : ∀ t, 0 ≤ k t)
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) {d : ℝ} (hd : 0 < d) :
    volume.real (E \ goodSet k E d) ≤ (∫ x in E, kernelLeakage k E x) / d := by
  have hl : Integrable (kernelLeakage k E) (volume.restrict E) :=
    integrableOn_kernel_section hi hEfin hE.compl
  have hmark : d * (volume.restrict E).real {x | d ≤ kernelLeakage k E x} ≤
      ∫ x in E, kernelLeakage k E x := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (volume.restrict E) fun x => integral_nonneg fun y => hk0 (x - y)) hl d
  have he : (volume.restrict E).real {x | d ≤ kernelLeakage k E x} =
      volume.real (E \ goodSet k E d) := by
    simp only [Measure.real]
    rw [Measure.restrict_apply
      (measurableSet_le measurable_const (measurable_kernelLeakage hk E))]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, goodSet, not_and, not_lt]
    tauto
  rw [he] at hmark
  exact (le_div_iff₀ hd).mpr (by simpa [mul_comm] using hmark)

theorem measure_badSet_tendsto {k : ℕ → ℝ → ℝ} (hkm : ∀ n, Measurable (k n))
    (hk : ∀ n t, 0 ≤ k n t) (hi : ∀ n, Integrable (k n))
    (hm : ∀ n, ∫ t, k n t = 1)
    (ht : ∀ δ > 0, Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, k n t) atTop (𝓝 0))
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n => volume.real (E \ goodSet (k n) E d)) atTop (𝓝 0) := by
  have he := (kernelLeakage_tendsto hk hi hm ht hE hEfin).div_const d
  apply squeeze_zero (fun n => measureReal_nonneg) (fun n =>
    measure_badSet_le (hkm n) (hi n) (hk n) hE hEfin hd)
  simpa using he

theorem measure_subsets_tendsto {E : Set ℝ} (hEfin : volume E ≠ ⊤) {F : ℕ → Set ℝ}
    (hF : ∀ n, MeasurableSet (F n)) (hFE : ∀ n, F n ⊆ E)
    (ht : Tendsto (fun n => volume.real (E \ F n)) atTop (𝓝 0)) :
    Tendsto (fun n => volume.real (F n)) atTop (𝓝 (volume.real E)) := by
  have he := ht.const_sub (volume.real E)
  convert! he using 1
  · funext n
    rw [measureReal_sdiff (hFE n) (hF n) hEfin]
    ring
  · simp

theorem changing_kernelEnergy_tendsto {k : ℕ → ℝ → ℝ}
    (hc : ∀ n, Continuous (k n)) (hk : ∀ n t, 0 ≤ k n t) (hi : ∀ n, Integrable (k n))
    (hs : ∀ n t, k n (-t) = k n t) (hm : ∀ n, ∫ t, k n t = 1)
    (ht : ∀ δ > 0, Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, k n t) atTop (𝓝 0))
    {E : Set ℝ} (hE : MeasurableSet E) (hEint : E ⊆ Icc (-1) 1) {F : ℕ → Set ℝ}
    (hF : ∀ n, MeasurableSet (F n)) (hFE : ∀ n, F n ⊆ E)
    (hsmall : Tendsto (fun n => volume.real (E \ F n)) atTop (𝓝 0)) :
    Tendsto (fun n => kernelEnergy (k n) (F n)) atTop (𝓝 (volume.real E)) := by
  have hdiff : Tendsto (fun n => kernelEnergy (k n) (F n) - kernelEnergy (k n) E) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hsmall.const_mul 2)
    simpa only [Real.norm_eq_abs, abs_sub_comm] using
      kernelEnergy_change_bound (hc n) (hi n) (hk n) (hs n) (hm n) hE (hF n) hEint (hFE n)
  have he := hdiff.add (kernelEnergy_tendsto hk hi hm ht hE (interval_subset_finite hEint))
  simpa using he

end Erdos1132
