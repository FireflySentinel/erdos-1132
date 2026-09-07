import Erdos1132.AlmostEverywhere.EnergyComparison

/-! # The positive Cauchy-transform ratio energy

Paper: §6, Theorem 1(ii) and the positive-measure argument used in §8.
-/

noncomputable section

open MeasureTheory Set

namespace Erdos1132

theorem kernelEnergy_le_of_ratio_bound {k w : ℝ → ℝ}
    (hc : Continuous k) (hi : Integrable k) (hk : ∀ t, 0 ≤ k t)
    (hs : ∀ t, k (-t) = k t) (hwc : Continuous w) (hw : ∀ x, 0 < w x)
    {M : ℝ} (hM : ∀ x, |w x| ≤ M) {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : E ⊆ Icc (-1) 1) {θ : ℝ}
    (hb : ∀ x ∈ E, (∫ y, k (x - y) * w y) / w x ≤ θ) :
    kernelEnergy k E ≤ θ * volume.real E := by
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr (interval_subset_finite hEint)
  have hkc : Continuous (fun p : ℝ × ℝ => k (p.1 - p.2)) := hc.comp (continuous_fst.sub continuous_snd)
  have hrc : Continuous (fun p : ℝ × ℝ => k (p.1 - p.2) * (w p.2 / w p.1)) :=
    hkc.mul ((hwc.comp continuous_snd).div (hwc.comp continuous_fst) (fun p => (hw p.1).ne'))
  have hik := integrable_on_interval_product hkc hEint hEint
  have hir := integrable_on_interval_product hrc hEint hEint
  have he := symmetric_ratio_energy (volume.restrict E) (fun x y => k (x - y)) w
    (fun x y => hk (x - y)) (fun x y => by rw [show x - y = -(y - x) by ring, hs]) hw hik hir
  rw [integral_prod _ hik, integral_prod _ hir] at he
  apply he.trans
  have hbound : ∀ x ∈ E, (∫ y in E, k (x - y) * (w y / w x)) ≤ θ := by
    intro x hx
    have hiy : Integrable (fun y => k (x - y) * w y) :=
      (hi.comp_sub_left x).mul_bdd hwc.aestronglyMeasurable (ae_of_all _ hM)
    have hnon : ∀ y, 0 ≤ k (x - y) * w y := fun y => mul_nonneg (hk _) (hw y).le
    have hsub := setIntegral_le_integral (s := E) hiy (ae_of_all _ hnon)
    calc
      _ = (∫ y in E, k (x - y) * w y) / w x := by
        rw [← integral_div]
        apply integral_congr_ae
        filter_upwards with y
        ring
      _ ≤ (∫ y, k (x - y) * w y) / w x := div_le_div_of_nonneg_right hsub (hw x).le
      _ ≤ θ := hb x hx
  calc
    _ ≤ ∫ _ in E, θ := by
      apply setIntegral_mono_on hir.integral_prod_left (integrable_const _) hE
      exact hbound
    _ = _ := by simp [mul_comm]

end Erdos1132
