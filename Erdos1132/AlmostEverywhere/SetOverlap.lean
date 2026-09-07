import Erdos1132.Shared.ApproximateIdentity
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-! # Translation overlap of finite-measure sets

Paper: §6, Theorem 1(ii) and the positive-measure argument used in §8.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology symmDiff ENNReal

namespace Erdos1132

def setOverlap (E : Set ℝ) (t : ℝ) : ℝ := ∫ y in E, E.indicator (fun _ => (1 : ℝ)) (y - t)

def translateMap (t : ℝ) : C(ℝ, ℝ) := ⟨fun y => y - t, by fun_prop⟩

theorem continuous_translateMap : Continuous translateMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × ℝ => p.2 - p.1)
  fun_prop

theorem measurePreserving_translateMap (t : ℝ) : MeasurePreserving (translateMap t) volume volume := by
  simpa only [translateMap, ContinuousMap.coe_mk, sub_eq_add_neg] using measurePreserving_add_right volume (-t)

theorem measurable_setOverlap {E : Set ℝ} (hE : MeasurableSet E) : Measurable (setOverlap E) := by
  have hm : Measurable (fun p : ℝ × ℝ => E.indicator (fun _ => (1 : ℝ)) (p.2 - p.1)) :=
    (measurable_const.indicator hE).comp (measurable_snd.sub measurable_fst)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem setOverlap_eq {E : Set ℝ} (hE : MeasurableSet E) (t : ℝ) :
    setOverlap E t = volume.real (E ∩ (translateMap t ⁻¹' E)) := by
  have he : (fun y => E.indicator (fun _ => (1 : ℝ)) (y - t)) =
      (translateMap t ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases hy : y - t ∈ E <;> simp [translateMap, hy]
  rw [setOverlap, he, setIntegral_indicator (hE.preimage (translateMap t).continuous.measurable)]
  simp

theorem setOverlap_zero {E : Set ℝ} (hE : MeasurableSet E) : setOverlap E 0 = volume.real E := by
  rw [setOverlap_eq hE]
  simp [translateMap]

theorem setOverlap_nonneg (E : Set ℝ) (t : ℝ) : 0 ≤ setOverlap E t := by
  apply integral_nonneg
  intro y
  exact indicator_nonneg (fun _ _ => zero_le_one) _

theorem setOverlap_le {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) (t : ℝ) :
    setOverlap E t ≤ volume.real E := by
  rw [setOverlap_eq hE]
  exact measureReal_mono inter_subset_left hfin

theorem continuousAt_setOverlap_zero {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) :
    ContinuousAt (setOverlap E) 0 := by
  have ht := tendsto_measure_symmDiff_preimage_nhds_zero
    (continuous_translateMap.tendsto 0) (.of_forall measurePreserving_translateMap)
    (measurePreserving_translateMap 0) hE.nullMeasurableSet hfin
  have ht' : Tendsto (fun t => volume.real ((translateMap t ⁻¹' E) ∆ E)) (𝓝 0) (𝓝 0) := by
    have he := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp ht
    simpa [Measure.real, translateMap, Function.comp_def] using he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun t => norm_nonneg _) _ ht'
  intro t
  have hpre : MeasurableSet (translateMap t ⁻¹' E) := hE.preimage (translateMap t).continuous.measurable
  have hpfin : volume (translateMap t ⁻¹' E) ≠ ⊤ := by
    rwa [(measurePreserving_translateMap t).measure_preimage hE.nullMeasurableSet]
  have hdsfin : volume ((translateMap t ⁻¹' E) ∆ E) ≠ ⊤ :=
    measure_ne_top_of_subset symmDiff_subset_union (measure_union_lt_top hpfin.lt_top hfin.lt_top).ne
  rw [Real.norm_eq_abs, setOverlap_zero hE, setOverlap_eq hE]
  calc
    _ ≤ volume.real ((E ∩ (translateMap t ⁻¹' E)) ∆ E) :=
      abs_measureReal_sub_le_measureReal_symmDiff' (hE.inter hpre).nullMeasurableSet
        hE.nullMeasurableSet (measure_ne_top_of_subset inter_subset_left hfin) hfin
    _ ≤ _ := measureReal_mono (by intro y hy; simp only [mem_symmDiff, mem_inter_iff] at *; tauto) hdsfin

end Erdos1132
