import Erdos1132.AlmostEverywhere.SetOverlap

/-! # Kernel energies and leakage from measurable sets

Paper: §6, Theorem 1(ii) and the positive-measure argument used in §8.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos1132

def kernelEnergy (k : ℝ → ℝ) (E : Set ℝ) : ℝ := ∫ x in E, ∫ y in E, k (x - y)

def kernelLeakage (k : ℝ → ℝ) (E : Set ℝ) (x : ℝ) : ℝ := ∫ y in Eᶜ, k (x - y)

theorem measurable_kernelLeakage {k : ℝ → ℝ} (hk : Measurable k) (E : Set ℝ) :
    Measurable (kernelLeakage k E) := by
  exact (hk.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem integral_kernel_indicator {k : ℝ → ℝ} {F : Set ℝ} (hF : MeasurableSet F) (x : ℝ) :
    (∫ y in F, k (x - y)) = ∫ t, k t * F.indicator (fun _ => (1 : ℝ)) (x - t) := by
  have he := integral_sub_left_eq_self
    (fun t => k t * F.indicator (fun _ => (1 : ℝ)) (x - t)) volume x
  simp only [sub_sub_cancel] at he
  rw [← he, ← integral_indicator hF]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ F <;> simp [hy]

theorem integrable_kernel_indicator {k : ℝ → ℝ} (hk : Integrable k)
    {E F : Set ℝ} (hEfin : volume E ≠ ⊤) (hF : MeasurableSet F) :
    Integrable (fun p : ℝ × ℝ => k p.2 * F.indicator (fun _ => (1 : ℝ)) (p.1 - p.2))
      ((volume.restrict E).prod volume) := by
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hEfin
  apply (hk.comp_snd (volume.restrict E)).mul_bdd (c := 1)
  · exact ((measurable_const.indicator hF).comp
      (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  · apply ae_of_all
    intro p
    by_cases hp : p.1 - p.2 ∈ F <;> simp [hp]

theorem kernelEnergy_eq_overlap {k : ℝ → ℝ} (hk : Integrable k)
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    kernelEnergy k E = ∫ t, k t * setOverlap E t := by
  unfold kernelEnergy
  simp_rw [integral_kernel_indicator hE]
  rw [integral_integral_swap (integrable_kernel_indicator hk hEfin hE)]
  simp only [integral_const_mul, setOverlap]

theorem integrableOn_kernel_section {k : ℝ → ℝ} (hk : Integrable k)
    {E F : Set ℝ} (hEfin : volume E ≠ ⊤) (hF : MeasurableSet F) :
    IntegrableOn (fun x => ∫ y in F, k (x - y)) E := by
  change Integrable _ (volume.restrict E)
  have hi := (integrable_kernel_indicator hk hEfin hF).integral_prod_left
  simpa only [← integral_kernel_indicator hF] using hi

theorem integral_kernelLeakage {k : ℝ → ℝ} (hk : Integrable k) (hm : ∫ t, k t = 1)
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    (∫ x in E, kernelLeakage k E x) = volume.real E - kernelEnergy k E := by
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hEfin
  have he (x : ℝ) : kernelLeakage k E x = 1 - ∫ y in E, k (x - y) := by
    rw [kernelLeakage, setIntegral_compl hE (hk.comp_sub_left x), integral_sub_left_eq_self, hm]
  simp_rw [he]
  rw [integral_sub (integrable_const _) (integrableOn_kernel_section hk hEfin hE)]
  simp [kernelEnergy]

theorem kernelEnergy_tendsto {k : ℕ → ℝ → ℝ}
    (hk : ∀ n t, 0 ≤ k n t) (hi : ∀ n, Integrable (k n))
    (hm : ∀ n, ∫ t, k n t = 1)
    (ht : ∀ δ > 0, Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, k n t) atTop (𝓝 0))
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    Tendsto (fun n => kernelEnergy (k n) E) atTop (𝓝 (volume.real E)) := by
  simp_rw [kernelEnergy_eq_overlap (hi _) hE hEfin]
  rw [← setOverlap_zero hE]
  exact probability_kernel_tendsto hk hi hm ht (measurable_setOverlap hE)
    (fun t => by rw [abs_of_nonneg (setOverlap_nonneg E t)]; exact setOverlap_le hE hEfin t)
    (continuousAt_setOverlap_zero hE hEfin)

theorem kernelLeakage_tendsto {k : ℕ → ℝ → ℝ}
    (hk : ∀ n t, 0 ≤ k n t) (hi : ∀ n, Integrable (k n))
    (hm : ∀ n, ∫ t, k n t = 1)
    (ht : ∀ δ > 0, Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, k n t) atTop (𝓝 0))
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    Tendsto (fun n => ∫ x in E, kernelLeakage (k n) E x) atTop (𝓝 0) := by
  simp_rw [integral_kernelLeakage (hi _) (hm _) hE hEfin]
  simpa using (kernelEnergy_tendsto hk hi hm ht hE hEfin).const_sub (volume.real E)

end Erdos1132
