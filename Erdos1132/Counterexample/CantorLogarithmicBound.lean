import Erdos1132.Counterexample.CantorRadius
import Erdos1132.Counterexample.LogIntegralLowerBound

/-! # The logarithmic lower bound for the constructed Cantor radius -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Erdos1132.Counterexample

theorem cantorRadius_ne_zero_set {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    {y | cantorRadius ρ y ≠ 0} = cantorOpen ρ := by
  ext y
  constructor
  · intro hn
    exact (cantorRadius_pos_iff hρ hρ4).mp (lt_of_le_of_ne (cantorRadius_nonneg hρ hρ4 y) hn.symm)
  · exact fun hy => ((cantorRadius_pos_iff hρ hρ4).mpr hy).ne'

theorem cantor_ball_measure_comparison {ρ x t : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hx : x ∈ cantorOpen ρ) (ht : 4*cantorRadius ρ x ≤ t) (ht2 : t ≤ 2) :
    ((volume.restrict interval).restrict (cantorOpen ρ)) {y | |x-y| ≤ t} ≤
      ENNReal.ofReal (127/128 : ℝ)*(volume.restrict interval) {y | |x-y| ≤ t} := by
  let B : Set ℝ := {y | |x-y| ≤ t}
  have hBm : MeasurableSet B := (isClosed_le (continuous_const.sub continuous_id).abs continuous_const).measurableSet
  have ht0 : 0 < t := by have := (cantorRadius_pos_iff hρ hρ4).mpr hx; linarith
  obtain ⟨z, hz, hzx⟩ := exists_nearby_cantor_endpoint hρ hρ4 hx
  have hsub : cantorSet ρ ∩ Icc (z-t/2) (z+t/2) ⊆ B ∩ cantorSet ρ := by
    intro y hy
    refine ⟨?_,hy.1⟩
    have hyz : |z-y| ≤ t/2 := abs_le.mpr ⟨by linarith [hy.2.2],by linarith [hy.2.1]⟩
    have hd := abs_sub_le x z y
    change |x-y| ≤ t
    linarith
  have hden := cantor_uniform_density hρ hρ4 hz (show 0 < t/2 by linarith) (show t/2 ≤ 1 by linarith)
  have hFbound : ENNReal.ofReal (t/64) ≤ volume (B ∩ cantorSet ρ) := by
    have hh := hden.trans (measure_mono hsub)
    simpa only [show t/2/32 = t/64 by ring] using hh
  have hFfin : volume (B ∩ cantorSet ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_cantorSet ρ).measure_ne_top (measure_mono inter_subset_right)
  have hI : volume (B ∩ interval) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [interval, Real.volume_Icc]) (measure_mono inter_subset_right)
  have hUI : cantorOpen ρ ⊆ interval := fun _ hy => ⟨hy.1.1.le,hy.1.2.le⟩
  have hU : volume (B ∩ cantorOpen ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top hI (measure_mono (inter_subset_inter subset_rfl hUI))
  have hFreal : t/64 ≤ volume.real (B ∩ cantorSet ρ) := by
    have hh := ENNReal.toReal_mono hFfin hFbound
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ t/64)] using hh
  have hIreal : volume.real (B ∩ interval) ≤ 2*t := by
    have hh := interval_ball_measure_le x ht0.le
    rwa [measureReal_restrict_apply hBm] at hh
  have hdiff : B ∩ cantorOpen ρ = (B ∩ interval) \ (B ∩ cantorSet ρ) := by
    rw [cantorOpen_eq_diff hρ hρ4]
    ext y
    simp only [mem_inter_iff, Set.mem_sdiff, interval]
    tauto
  have hUreal : volume.real (B ∩ cantorOpen ρ) ≤ (127/128 : ℝ)*volume.real (B ∩ interval) := by
    rw [hdiff, measureReal_sdiff (inter_subset_inter subset_rfl (cantorSet_subset_interval ρ))
      (hBm.inter (isClosed_cantorSet ρ).measurableSet) hI]
    linarith
  rw [Measure.restrict_apply hBm, Measure.restrict_apply (hBm.inter (isOpen_cantorOpen ρ).measurableSet),
    Measure.restrict_apply hBm]
  have he : B ∩ cantorOpen ρ ∩ interval = B ∩ cantorOpen ρ := by
    apply inter_eq_left.mpr
    exact fun _ hy => ⟨hy.2.1.1.le,hy.2.1.2.le⟩
  rw [he, ← ENNReal.ofReal_toReal hU, ← ENNReal.ofReal_toReal hI, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 127/128)]
  exact ENNReal.ofReal_le_ofReal hUreal

theorem cantor_logarithmic_integral_lower_bound {A x : ℝ} (hA : 1 < A)
    (hx : x ∈ cantorOpen (gapScale A)) :
    (1/512 : ℝ)*Real.log (1/(4*cantorRadius (gapScale A) x))-32 ≤
      logarithmicOperator (logGapFunction (cantorRadius (gapScale A))) x /
        logGapFunction (cantorRadius (gapScale A)) x := by
  have hρ : 0 < gapScale A := Real.exp_pos _
  have hρ4 := gapScale_le_quarter hA
  have hs := (cantorRadius_pos_iff hρ hρ4).mpr hx
  have hb := cantorRadius_bound hρ hρ4 x
  have hT := gapScale_log_parameter hA hs (show cantorRadius (gapScale A) x ≤ gapScale A/2 by linarith)
  rw [Real.log_div (Real.exp_pos 8).ne' hs.ne', Real.log_exp] at hT
  apply logarithmic_integral_lower_bound (cantorRadius_continuous hρ hρ4).measurable
    ⟨hx.1.1.le,hx.1.2.le⟩ hs (by linarith) hT rfl
  · intro y _
    exact ⟨cantorRadius_nonneg hρ hρ4 y, by linarith [cantorRadius_bound hρ hρ4 y]⟩
  · intro y _
    simpa only [abs_sub_comm] using cantorRadius_lipschitz_bound hρ hρ4 y x
  · rw [cantorRadius_ne_zero_set hρ hρ4]
    intro t ht
    exact cantor_ball_measure_comparison hρ hρ4 hx ht.1 ht.2

theorem cantor_logarithmicRatio_gt {A x : ℝ} (hA : 1 < A)
    (hx : x ∈ cantorOpen (gapScale A)) :
    A+2 < logarithmicOperator (logGapFunction (cantorRadius (gapScale A))) x /
      logGapFunction (cantorRadius (gapScale A)) x := by
  have hρ : 0 < gapScale A := Real.exp_pos _
  have hρ4 := gapScale_le_quarter hA
  exact (gapScale_lower_bound hA ((cantorRadius_pos_iff hρ hρ4).mpr hx)
    (by linarith [cantorRadius_bound hρ hρ4 x])).trans_le (cantor_logarithmic_integral_lower_bound hA hx)

end Erdos1132.Counterexample
