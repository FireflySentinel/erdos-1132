import Erdos1132.AlmostEverywhere.SetEnergy
import Erdos1132.AlmostEverywhere.SymmetricEnergy

/-! # Comparison of the ratio energy and set energy

Main paper: §3, Theorem 1(ii), and the positive-measure corollary in §7.
-/

noncomputable section

open MeasureTheory Set

namespace Erdos1132

theorem integrable_on_interval_product {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {E F : Set ℝ} (hE : E ⊆ Icc (-1) 1) (hF : F ⊆ Icc (-1) 1) :
    Integrable f ((volume.restrict E).prod (volume.restrict F)) := by
  have hi : IntegrableOn f ((Icc (-1) 1 : Set ℝ) ×ˢ Icc (-1) 1) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuousOn
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  exact hi.mono_measure (Measure.prod_mono (Measure.restrict_mono hE le_rfl)
    (Measure.restrict_mono hF le_rfl))

theorem interval_subset_finite {E : Set ℝ} (hE : E ⊆ Icc (-1) 1) : volume E ≠ ⊤ :=
  measure_ne_top_of_subset hE isCompact_Icc.measure_ne_top

theorem cross_energy_swap {k : ℝ → ℝ} (hc : Continuous k) (hs : ∀ t, k (-t) = k t)
    {E F : Set ℝ} (hE : E ⊆ Icc (-1) 1) (hF : F ⊆ Icc (-1) 1) :
    (∫ x in E, ∫ y in F, k (x - y)) = ∫ y in F, ∫ x in E, k (y - x) := by
  have hc' : Continuous (fun p : ℝ × ℝ => k (p.1 - p.2)) := hc.comp (continuous_fst.sub continuous_snd)
  rw [integral_integral_swap (integrable_on_interval_product hc' hE hF)]
  congr 1
  funext y
  congr 1
  funext x
  rw [show x - y = -(y - x) by ring, hs]

theorem kernel_section_le_one {k : ℝ → ℝ} (hi : Integrable k) (hk : ∀ t, 0 ≤ k t)
    (hm : ∫ t, k t = 1) (E : Set ℝ) (x : ℝ) : (∫ y in E, k (x - y)) ≤ 1 := by
  have he := setIntegral_le_integral (s := E) (hi.comp_sub_left x) (ae_of_all _ fun y => hk (x - y))
  simpa only [integral_sub_left_eq_self, hm] using he

theorem cross_energy_le_measure {k : ℝ → ℝ} (hi : Integrable k) (hk : ∀ t, 0 ≤ k t)
    (hm : ∫ t, k t = 1) {E F : Set ℝ} (hEfin : volume E ≠ ⊤) (hF : MeasurableSet F) :
    (∫ x in E, ∫ y in F, k (x - y)) ≤ volume.real E := by
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hEfin
  calc
    _ ≤ ∫ _ in E, (1 : ℝ) := integral_mono
      (integrableOn_kernel_section hi hEfin hF) (integrable_const _) (kernel_section_le_one hi hk hm F)
    _ = _ := by simp

theorem kernelEnergy_change_bound {k : ℝ → ℝ} (hc : Continuous k) (hi : Integrable k)
    (hk : ∀ t, 0 ≤ k t) (hs : ∀ t, k (-t) = k t) (hm : ∫ t, k t = 1)
    {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEint : E ⊆ Icc (-1) 1) (hFE : F ⊆ E) :
    |kernelEnergy k E - kernelEnergy k F| ≤ 2 * volume.real (E \ F) := by
  have hEfin := interval_subset_finite hEint
  have hFfin := measure_ne_top_of_subset hFE hEfin
  have hDfin := measure_ne_top_of_subset (sdiff_subset : E \ F ⊆ E) hEfin
  have hFint := hFE.trans hEint
  have hDint := (sdiff_subset : E \ F ⊆ E).trans hEint
  have hsplit₁ := integral_inter_add_sdiff hF (integrableOn_kernel_section hi hEfin hE)
  rw [inter_eq_right.mpr hFE] at hsplit₁
  have hsplit₂ : (∫ x in F, ∫ y in F, k (x - y)) + (∫ x in F, ∫ y in E \ F, k (x - y)) =
      ∫ x in F, ∫ y in E, k (x - y) := by
    rw [← integral_add (integrableOn_kernel_section hi hFfin hF)
      (integrableOn_kernel_section hi hFfin (hE.diff hF))]
    apply integral_congr_ae
    filter_upwards with x
    simpa only [inter_eq_right.mpr hFE] using integral_inter_add_sdiff (s := E) hF (hi.comp_sub_left x).integrableOn
  have h₁ := cross_energy_le_measure hi hk hm hDfin hE
  have h₂ : (∫ x in F, ∫ y in E \ F, k (x - y)) ≤ volume.real (E \ F) := by
    rw [cross_energy_swap hc hs hFint hDint]
    exact cross_energy_le_measure hi hk hm hDfin hF
  have hn₁ : 0 ≤ ∫ x in E \ F, ∫ y in E, k (x - y) :=
    integral_nonneg fun x => integral_nonneg fun y => hk _
  have hn₂ : 0 ≤ ∫ x in F, ∫ y in E \ F, k (x - y) :=
    integral_nonneg fun x => integral_nonneg fun y => hk _
  unfold kernelEnergy
  apply abs_le.mpr
  constructor <;> linarith

end Erdos1132
