import Erdos1132.Counterexample.LogarithmicOperator
import Erdos1132.Counterexample.FarProfile
import Erdos1132.Counterexample.RadialComparison
import Erdos1132.Counterexample.RadialIntervals
import Erdos1132.Counterexample.InverseDistance

/-! # The explicit logarithmic integral lower bound on an open gap

Companion note: §2.2, the logarithmic integral estimate.
-/

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1132.Counterexample

theorem interval_radius_le_two {x y : ℝ} (hx : x ∈ interval) (hy : y ∈ interval) :
    |x - y| ≤ 2 := by
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem measurableSet_intervalRadialTail (x a : ℝ) : MeasurableSet (intervalRadialTail x a) :=
  measurableSet_Icc.inter
    (isClosed_le continuous_const (continuous_const.sub continuous_id).abs).measurableSet

theorem inverse_continuousOn {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => 1 / t) (Icc a 2) :=
  continuousOn_const.div continuousOn_id (fun _ ht => (ha.trans_le ht.1).ne')

/-- The exact one-dimensional profile estimates apply on both sides of `x`. -/
theorem integral_farWeight_radial_le {x a : ℝ} (hx : x ∈ interval)
    (ha : 0 < a) (ha2 : a ≤ 2) :
    (∫ y in intervalRadialTail x a, farWeight |x - y|) ≤
      ((256 / 255 : ℝ) * logProfile (5 * a / 4)) *
        ∫ y in intervalRadialTail x a, 1 / |x - y| := by
  apply integral_intervalRadialTail_le hx ha ha2 (farWeight_continuousOn ha le_rfl)
    (inverse_continuousOn ha)
  intro b hb
  rw [integral_one_div_of_pos ha (ha.trans_le hb.1)]
  exact integral_farWeight_le ha hb.1 hb.2

/-- At least one side of a point in `[-1,1]` has length at least one. -/
theorem integral_radial_inverse_lower {x a : ℝ} (hx : x ∈ interval)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.log (1 / a) ≤ ∫ y in intervalRadialTail x a, 1 / |x - y| := by
  have hi := integrableOn_intervalRadialTail hx (inverse_continuousOn ha)
  have hnn : 0 ≤ᵐ[volume.restrict (intervalRadialTail x a)]
      (fun y => 1 / |x - y|) := Eventually.of_forall fun y => by positivity
  by_cases hxp : 0 ≤ x
  · have hS : Icc (x - 1) (x - a) ⊆ intervalRadialTail x a := by
      intro y hy
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · linarith [hy.1]
      · linarith [hy.2, hx.2]
      · change a ≤ |x - y|
        rw [abs_of_pos (by linarith [hy.2])]
        linarith [hy.2]
    have h := setIntegral_mono_set (s := Icc (x - 1) (x - a)) hi hnn (Eventually.of_forall hS)
    rw [integral_inverseDistance_left ha ha1] at h
    exact h
  · have hS : Icc (x + a) (x + 1) ⊆ intervalRadialTail x a := by
      intro y hy
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · linarith [hy.1, hx.1]
      · linarith [hy.2]
      · change a ≤ |x - y|
        rw [abs_of_neg (by linarith [hy.1])]
        linarith [hy.1]
    have h := setIntegral_mono_set (s := Icc (x + a) (x + 1)) hi hnn (Eventually.of_forall hS)
    rw [integral_inverseDistance_right ha ha1] at h
    exact h

theorem interval_ball_measure_le (x : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (volume.restrict interval).real {y | |x - y| ≤ a} ≤ 2 * a := by
  have hm : MeasurableSet {y | |x - y| ≤ a} :=
    (isClosed_le (continuous_const.sub continuous_id).abs continuous_const).measurableSet
  rw [measureReal_restrict_apply hm]
  have hs : {y | |x - y| ≤ a} ∩ interval ⊆ Icc (x - a) (x + a) := by
    intro y hy
    change (|x - y| ≤ a) ∧ y ∈ interval at hy
    obtain ⟨hl, hu⟩ := abs_le.mp hy.1
    exact ⟨by linarith, by linarith⟩
  have h := measureReal_mono (μ := volume) hs (by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top)
  rw [Real.volume_real_Icc] at h
  have he : max (x + a - (x - a)) 0 = 2 * a := by
    rw [show x + a - (x - a) = 2 * a by ring, max_eq_left (by positivity)]
  rwa [he] at h

/-- Cumulative gap measure estimates control the complete negative far-field term. -/
theorem far_radial_bound {U : Set ℝ} {x s : ℝ} (hx : x ∈ interval)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hT : 16 ≤ 8 - Real.log s)
    (hball : ∀ t ∈ Icc (4 * s) 2,
      ((volume.restrict interval).restrict U) {y | |x - y| ≤ t} ≤
        ENNReal.ofReal (127 / 128 : ℝ) * (volume.restrict interval) {y | |x - y| ≤ t}) :
    (∫ y in {y | 4 * s ≤ |x - y|}, farWeight |x - y|
      ∂((volume.restrict interval).restrict U)) ≤
      4 * logProfile s + (1 - 1 / 512 : ℝ) * logProfile s *
        ∫ y in intervalRadialTail x (4 * s), 1 / |x - y| := by
  let ν : Measure ℝ := volume.restrict interval
  let μ : Measure ℝ := ν.restrict U
  have ha : 0 < 4 * s := by positivity
  have ha2 : 4 * s ≤ 2 := by linarith
  have hν : ∀ᵐ y ∂ν, |x - y| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact interval_radius_le_two hx hy
  have hμ : ∀ᵐ y ∂μ, |x - y| ≤ 2 := ae_restrict_of_ae hν
  have hcap : ContinuousOn (fun y => farWeight (max (4 * s) |x - y|)) interval := by
    apply (farWeight_continuousOn ha le_rfl).comp
      (continuous_const.max (continuous_const.sub continuous_id).abs).continuousOn
    intro y hy
    change max (4 * s) |x - y| ∈ Icc (4 * s) 2
    exact ⟨le_max_left _ _, max_le ha2 (interval_radius_le_two hx hy)⟩
  have hiν : Integrable (fun y => farWeight (max (4 * s) |x - y|)) ν :=
    hcap.integrableOn_Icc
  have hiμ : Integrable (fun y => farWeight (max (4 * s) |x - y|)) μ :=
    hiν.mono_measure Measure.restrict_le_self
  have hraw := integral_radial_tail_le μ ν (fun y => |x - y|)
    (continuous_const.sub continuous_id).abs.measurable ha2
    (show (0 : ℝ) ≤ 127 / 128 by norm_num) hμ hν
    (farWeight_continuousOn ha le_rfl) (farWeight_strictAntiOn ha le_rfl)
    (fun t ht => (farWeight_pos (ha.trans_le ht.1) ht.2).le) hiμ hiν hball
  have hstrict : (∫ y in {y | 4 * s < |x - y|}, farWeight |x - y| ∂ν) ≤
      ∫ y in intervalRadialTail x (4 * s), farWeight |x - y| := by
    have hm : MeasurableSet {y | 4 * s < |x - y|} :=
      (isOpen_lt continuous_const (continuous_const.sub continuous_id).abs).measurableSet
    change (∫ y, farWeight |x - y| ∂((volume.restrict interval).restrict _)) ≤ _
    rw [Measure.restrict_restrict hm]
    apply setIntegral_mono_set (s := {y | 4 * s < |x - y|} ∩ interval)
      (integrableOn_intervalRadialTail hx (farWeight_continuousOn ha le_rfl))
    · filter_upwards [ae_restrict_mem (measurableSet_intervalRadialTail x (4 * s))] with y hy
      exact (farWeight_pos (ha.trans_le hy.2) (interval_radius_le_two hx hy.1)).le
    · apply Eventually.of_forall
      intro y hy
      change (4 * s < |x - y|) ∧ y ∈ interval at hy
      exact ⟨hy.2, hy.1.le⟩
  have hJ := integral_farWeight_radial_le hx ha ha2
  have hmeasure := interval_ball_measure_le x ha.le
  have hfa : 0 ≤ farWeight (4 * s) := (farWeight_pos ha ha2).le
  have hboundary := mul_le_mul_of_nonneg_left hmeasure hfa
  have hfaid : farWeight (4 * s) * (2 * (4 * s)) = 2 * logProfile (5 * s) := by
    rw [farWeight_eq ha, show 5 * (4 * s) / 4 = 5 * s by ring]
    field_simp
  rw [hfaid] at hboundary
  rw [show 5 * (4 * s) / 4 = 5 * s by ring] at hJ
  have hps0 : 0 ≤ logProfile s := Real.rpow_nonneg (by linarith) _
  have hps5 := logProfile_mul_five_le hs hT
  have hB : (127 / 128 : ℝ) *
      (farWeight (4 * s) * ν.real {y | |x - y| ≤ 4 * s}) ≤ 4 * logProfile s := by
    have h := mul_le_mul_of_nonneg_left hboundary (show (0 : ℝ) ≤ 127 / 128 by norm_num)
    change (127 / 128 : ℝ) *
      (farWeight (4 * s) * (volume.restrict interval).real {y | |x - y| ≤ 4 * s}) ≤ _
    linarith
  have hH0 : 0 ≤ ∫ y in intervalRadialTail x (4 * s), 1 / |x - y| :=
    integral_nonneg (fun _ => by positivity)
  have hF := mul_le_mul_of_nonneg_left (hstrict.trans hJ)
    (show (0 : ℝ) ≤ 127 / 128 by norm_num)
  have hC := mul_le_mul_of_nonneg_right (logProfile_far_contraction hs hT) hH0
  change _ ≤ _ at hraw
  nlinarith

/-- The derivative bound controls the singular difference quotient near the query point. -/
theorem gap_differenceKernel_near {r : ℝ → ℝ} {x y s : ℝ}
    (hs : 0 < s) (hT : 16 ≤ 8 - Real.log s) (hrx : r x = s)
    (hLip : |r y - s| ≤ |x - y|) (hnear : |x - y| ≤ s / 2) :
    |differenceKernel (logGapFunction r) x y| ≤ 4 * logProfile s / s := by
  have hry : r y ∈ Icc (s / 2) (3 * s / 2) := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hLip.trans hnear)
    constructor <;> linarith
  have hry0 : 0 < r y := by linarith [hry.1]
  have hps : 0 ≤ logProfile s := Real.rpow_nonneg (by linarith) _
  have hK : 0 ≤ 4 * logProfile s / s := by positivity
  apply abs_differenceKernel_le hK
  have h := logProfile_local_lipschitz hs hT
    (show s ∈ Icc (s / 2) (3 * s / 2) by constructor <;> linarith) hry
  have hL : |s - r y| ≤ |x - y| := by simpa only [abs_sub_comm] using hLip
  have h' := h.trans (mul_le_mul_of_nonneg_left hL hK)
  simpa only [logGapFunction, hrx, if_neg hs.ne', if_neg hry0.ne'] using h'

theorem integrableOn_gap_differenceKernel {r : ℝ → ℝ} {x s : ℝ}
    (hrm : Measurable r) (hx : x ∈ interval) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hT : 16 ≤ 8 - Real.log s) (hrx : r x = s)
    (hr : ∀ y ∈ interval, 0 ≤ r y ∧ r y ≤ 2)
    (hLip : ∀ y ∈ interval, |r y - s| ≤ |x - y|) :
    IntegrableOn (differenceKernel (logGapFunction r) x) interval := by
  have hum := measurable_logGapFunction hrm
  have hm : Measurable (differenceKernel (logGapFunction r) x) :=
    (measurable_const.sub hum).div (continuous_const.sub continuous_id).abs.measurable
  have hi : IntegrableOn (fun _ : ℝ => 4 / s) interval := continuous_const.integrableOn_Icc
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs]
  by_cases hnear : |x - y| ≤ s / 2
  · have h := gap_differenceKernel_near hs hT hrx (hLip y hy) hnear
    exact h.trans (div_le_div_of_nonneg_right (by
      have hp := logProfile_le_one hs (show s ≤ 2 by linarith)
      linarith) hs.le)
  · have hx0 := logGapFunction_nonneg (hr x hx).1 (hr x hx).2
    have hx1 := logGapFunction_le_one (hr x hx).1 (hr x hx).2
    have hy0 := logGapFunction_nonneg (hr y hy).1 (hr y hy).2
    have hy1 := logGapFunction_le_one (hr y hy).1 (hr y hy).2
    have habs : |logGapFunction r x - logGapFunction r y| ≤ 1 := by
      apply abs_le.mpr; constructor <;> linarith
    rw [differenceKernel, abs_div, abs_abs]
    calc
      _ ≤ 1 / (s / 2) := div_le_div₀ (by norm_num) habs (by positivity) (le_of_not_ge hnear)
      _ ≤ 4 / s := by rw [div_le_div_iff₀ (by positivity) hs]; linarith

/-- On the far region the explicit profile is bounded by the decreasing radial weight. -/
theorem gap_negative_far_le {r : ℝ → ℝ} {x s : ℝ}
    (hrm : Measurable r) (hx : x ∈ interval) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hr : ∀ y ∈ interval, 0 ≤ r y ∧ r y ≤ 2)
    (hLip : ∀ y ∈ interval, |r y - s| ≤ |x - y|) :
    (∫ y in intervalRadialTail x (4 * s), logGapFunction r y / |x - y|) ≤
      ∫ y in {y | 4 * s ≤ |x - y|}, farWeight |x - y|
        ∂((volume.restrict interval).restrict {y | r y ≠ 0}) := by
  let U : Set ℝ := {y | r y ≠ 0}
  let F := intervalRadialTail x (4 * s)
  have hUm : MeasurableSet U := (measurableSet_eq_fun hrm measurable_const).compl
  have hFm := measurableSet_intervalRadialTail x (4 * s)
  have ha : 0 < 4 * s := by positivity
  have hfi := integrableOn_intervalRadialTail hx (inverse_continuousOn ha)
  have hni : IntegrableOn (fun y => logGapFunction r y / |x - y|) F := by
    apply hfi.mono' ((measurable_logGapFunction hrm).div
      (continuous_const.sub continuous_id).abs.measurable).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hFm] with y hy
    change ‖logGapFunction r y / |x - y|‖ ≤ 1 / |x - y|
    have h0 := logGapFunction_nonneg (hr y hy.1).1 (hr y hy.1).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (logGapFunction_le_one (hr y hy.1).1 (hr y hy.1).2)
      (abs_nonneg _)
  have hwi := (integrableOn_intervalRadialTail hx
    (farWeight_continuousOn ha (show (2 : ℝ) ≤ 2 by rfl))).indicator hUm
  have hpt : ∀ y ∈ F, logGapFunction r y / |x - y| ≤
      U.indicator (fun y => farWeight |x - y|) y := by
    intro y hy
    by_cases hz : r y = 0
    · rw [Set.indicator_of_notMem (show y ∉ U from fun h => h hz)]
      simp [logGapFunction, hz]
    · rw [Set.indicator_of_mem (show y ∈ U from hz), farWeight_eq (ha.trans_le hy.2)]
      have hry0 : 0 < r y := lt_of_le_of_ne (hr y hy.1).1 (Ne.symm hz)
      have hry : r y ≤ 5 * |x - y| / 4 := by
        have h := (abs_le.mp (hLip y hy.1)).2
        have hfar : 4 * s ≤ |x - y| := hy.2
        linarith
      have hlog := farLog_lower_bound (ha.trans_le hy.2) (interval_radius_le_two hx hy.1)
      rw [farLog_eq (ha.trans_le hy.2)] at hlog
      have hp := logProfile_le_logProfile hry0 hry (by linarith)
      simpa only [logGapFunction, if_neg hz] using
        div_le_div_of_nonneg_right hp (abs_nonneg (x - y))
  have h := setIntegral_mono_on hni hwi hFm hpt
  have hm : MeasurableSet {y | 4 * s ≤ |x - y|} :=
    (isClosed_le continuous_const (continuous_const.sub continuous_id).abs).measurableSet
  rw [integral_indicator hUm, Measure.restrict_restrict hUm] at h
  change _ ≤ ∫ y, farWeight |x - y|
    ∂(((volume.restrict interval).restrict U).restrict {y | 4 * s ≤ |x - y|})
  rw [Measure.restrict_restrict hUm, Measure.restrict_restrict hm]
  have heq : U ∩ F = {y | 4 * s ≤ |x - y|} ∩ (U ∩ interval) := by
    ext y
    simp only [F, intervalRadialTail, mem_inter_iff]
    tauto
  rw [heq] at h
  exact h

theorem gap_near_integral_lower {r : ℝ → ℝ} {x s : ℝ} {S : Set ℝ}
    (hs : 0 < s) (hT : 16 ≤ 8 - Real.log s) (hrx : r x = s)
    (hLip : ∀ y ∈ S, |r y - s| ≤ |x - y|)
    (hnear : ∀ y ∈ S, |x - y| ≤ s / 2) :
    -4 * logProfile s ≤ ∫ y in S, differenceKernel (logGapFunction r) x y := by
  have hsub : S ⊆ Icc (x - s / 2) (x + s / 2) := by
    intro y hy
    obtain ⟨hl, hu⟩ := abs_le.mp (hnear y hy)
    exact ⟨by linarith, by linarith⟩
  have hfin : volume S < ⊤ := lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top
  have hmeasure := measureReal_mono (μ := volume) hsub measure_Icc_lt_top.ne
  rw [Real.volume_real_Icc] at hmeasure
  have heq : max (x + s / 2 - (x - s / 2)) 0 = s := by
    rw [show x + s / 2 - (x - s / 2) = s by ring, max_eq_left hs.le]
  rw [heq] at hmeasure
  have hps : 0 ≤ logProfile s := Real.rpow_nonneg (by linarith) _
  have hK : 0 ≤ 4 * logProfile s / s := by positivity
  have h := norm_setIntegral_le_of_norm_le_const (f := differenceKernel (logGapFunction r) x)
    (C := 4 * logProfile s / s) hfin (fun y hy => by
    simpa only [Real.norm_eq_abs] using gap_differenceKernel_near hs hT hrx (hLip y hy) (hnear y hy))
  have hmeasure' := mul_le_mul_of_nonneg_left hmeasure hK
  have hc : (4 * logProfile s / s) * s = 4 * logProfile s := by field_simp
  rw [hc] at hmeasure'
  rw [Real.norm_eq_abs] at h
  have hlow := (abs_le.mp h).1
  nlinarith

theorem gap_middle_integral_lower {r : ℝ → ℝ} {x s : ℝ} {S : Set ℝ}
    (hs : 0 < s) (hT : 16 ≤ 8 - Real.log s) (hrx : r x = s)
    (hSm : MeasurableSet S)
    (hr : ∀ y ∈ S, 0 ≤ r y)
    (hLip : ∀ y ∈ S, |r y - s| ≤ |x - y|)
    (hmid : ∀ y ∈ S, s / 2 < |x - y| ∧ |x - y| < 4 * s)
    (hi : IntegrableOn (differenceKernel (logGapFunction r) x) S) :
    -18 * logProfile s ≤ ∫ y in S, differenceKernel (logGapFunction r) x y := by
  have hps : 0 ≤ logProfile s := Real.rpow_nonneg (by linarith) _
  have hsub : S ⊆ radialAnnulus x (s / 2) (4 * s) := fun y hy =>
    ⟨(hmid y hy).1.le, (hmid y hy).2.le⟩
  have hInv := (integrableOn_inverseDistance_annulus (show 0 < s / 2 by positivity)).mono_set hsub
  have hpt : ∀ y ∈ S, (-3 * logProfile s) * (1 / |x - y|) ≤
      differenceKernel (logGapFunction r) x y := by
    intro y hy
    have hu : logGapFunction r y ≤ 2 * logProfile s := by
      unfold logGapFunction
      split_ifs with hz
      · positivity
      · have hry0 : 0 < r y := lt_of_le_of_ne (hr y hy) (Ne.symm hz)
        have hry : r y ≤ 5 * s := by
          have h := (abs_le.mp (hLip y hy)).2
          linarith [(hmid y hy).2]
        have hlog : Real.log (5 * s) < 8 := by
          rw [Real.log_mul (by norm_num) hs.ne']
          linarith [log_five_le_two]
        exact (logProfile_le_logProfile hry0 hry hlog).trans (logProfile_mul_five_le hs hT)
    have hnum : -3 * logProfile s ≤ logProfile s - logGapFunction r y := by linarith
    have h := div_le_div_of_nonneg_right hnum (abs_nonneg (x - y))
    simpa only [differenceKernel, logGapFunction, hrx, if_neg hs.ne', mul_one_div] using h
  have h := setIntegral_mono_on (hInv.const_mul (-3 * logProfile s)) hi hSm hpt
  rw [integral_const_mul] at h
  have hInvBound := integral_inverseDistance_le (show 0 < s / 2 by positivity)
    (show s / 2 ≤ 4 * s by linarith) hsub
  rw [show (4 * s) / (s / 2) = 8 by field_simp; norm_num] at hInvBound
  have hlog8 : Real.log 8 ≤ 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2 ⊢
    linarith
  have hmult := mul_le_mul_of_nonneg_left hInvBound (show 0 ≤ 3 * logProfile s by positivity)
  have hmult' := mul_le_mul_of_nonneg_left hlog8 (show 0 ≤ 6 * logProfile s by positivity)
  nlinarith

/-- The explicit logarithmic integral bound, assuming the geometric cumulative
measure comparison and the distance control for `r`. -/
theorem logarithmic_integral_lower_bound {r : ℝ → ℝ} {x s : ℝ}
    (hrm : Measurable r) (hx : x ∈ interval) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hT : 16 ≤ 8 - Real.log s) (hrx : r x = s)
    (hr : ∀ y ∈ interval, 0 ≤ r y ∧ r y ≤ 2)
    (hLip : ∀ y ∈ interval, |r y - s| ≤ |x - y|)
    (hball : ∀ t ∈ Icc (4 * s) 2,
      ((volume.restrict interval).restrict {y | r y ≠ 0}) {y | |x - y| ≤ t} ≤
        ENNReal.ofReal (127 / 128 : ℝ) * (volume.restrict interval) {y | |x - y| ≤ t}) :
    (1 / 512 : ℝ) * Real.log (1 / (4 * s)) - 32 ≤
      logarithmicOperator (logGapFunction r) x / logGapFunction r x := by
  let N : Set ℝ := interval ∩ {y | |x - y| ≤ s / 2}
  let M : Set ℝ := interval ∩ {y | s / 2 < |x - y| ∧ |x - y| < 4 * s}
  let F := intervalRadialTail x (4 * s)
  have hNm : MeasurableSet N := measurableSet_Icc.inter
    (isClosed_le (continuous_const.sub continuous_id).abs continuous_const).measurableSet
  have hMm : MeasurableSet M := measurableSet_Icc.inter
    ((isOpen_lt continuous_const (continuous_const.sub continuous_id).abs).measurableSet.inter
      (isOpen_lt (continuous_const.sub continuous_id).abs continuous_const).measurableSet)
  have hFm : MeasurableSet F := measurableSet_intervalRadialTail x (4 * s)
  have hNI : N ⊆ interval := inter_subset_left
  have hMI : M ⊆ interval := inter_subset_left
  have hFI : F ⊆ interval := inter_subset_left
  have hNM : Disjoint N M := by
    apply Set.disjoint_left.mpr
    intro y hn hm
    have hn' : |x - y| ≤ s / 2 := hn.2
    have hm' : s / 2 < |x - y| := hm.2.1
    linarith
  have hNF : Disjoint (N ∪ M) F := by
    apply Set.disjoint_left.mpr
    intro y hnm hf
    have hf' : 4 * s ≤ |x - y| := hf.2
    rcases hnm with hn | hm
    · have hn' : |x - y| ≤ s / 2 := hn.2
      linarith
    · have hm' : |x - y| < 4 * s := hm.2.2
      linarith
  have hcover : (N ∪ M) ∪ F = interval := by
    ext y
    simp only [N, M, F, intervalRadialTail, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hy
      by_cases hn : |x - y| ≤ s / 2
      · exact Or.inl (Or.inl ⟨hy, hn⟩)
      · by_cases hm : |x - y| < 4 * s
        · exact Or.inl (Or.inr ⟨hy, lt_of_not_ge hn, hm⟩)
        · exact Or.inr ⟨hy, le_of_not_gt hm⟩
  have hki := integrableOn_gap_differenceKernel hrm hx hs hs4 hT hrx hr hLip
  have hkn := hki.mono_set hNI
  have hkm := hki.mono_set hMI
  have hkf := hki.mono_set hFI
  have hsum : logarithmicOperator (logGapFunction r) x =
      (∫ y in N, differenceKernel (logGapFunction r) x y) +
      (∫ y in M, differenceKernel (logGapFunction r) x y) +
      ∫ y in F, differenceKernel (logGapFunction r) x y := by
    unfold logarithmicOperator
    rw [← hcover, setIntegral_union hNF hFm (hkn.union hkm) hkf,
      setIntegral_union hNM hMm hkn hkm]
  have hN := gap_near_integral_lower (S := N) hs hT hrx
    (fun y hy => hLip y hy.1) (fun y hy => hy.2)
  have hM := gap_middle_integral_lower hs hT hrx hMm
    (fun y hy => (hr y hy.1).1) (fun y hy => hLip y hy.1) (fun y hy => hy.2) hkm
  have hpx : logGapFunction r x = logProfile s := by
    simp only [logGapFunction, hrx, if_neg hs.ne']
  have hker : differenceKernel (logGapFunction r) x =
      fun y => logProfile s * (1 / |x - y|) - logGapFunction r y / |x - y| := by
    funext y
    rw [differenceKernel, hpx]
    ring
  have hInv : IntegrableOn (fun y => 1 / |x - y|) F :=
    integrableOn_intervalRadialTail hx (inverse_continuousOn (show 0 < 4 * s by positivity))
  have hNeg : IntegrableOn (fun y => logGapFunction r y / |x - y|) F := by
    have h := (hInv.const_mul (logProfile s)).sub hkf
    apply h.congr
    apply Eventually.of_forall
    intro y
    change logProfile s * (1 / |x - y|) - differenceKernel (logGapFunction r) x y = _
    rw [hker]
    ring
  have hfarid : (∫ y in F, differenceKernel (logGapFunction r) x y) =
      logProfile s * (∫ y in F, 1 / |x - y|) -
        ∫ y in F, logGapFunction r y / |x - y| := by
    rw [hker, integral_sub (hInv.const_mul (logProfile s)) hNeg, integral_const_mul]
  have hfar := (gap_negative_far_le hrm hx hs hs4 hr hLip).trans
    (far_radial_bound hx hs hs4 hT hball)
  have hH := integral_radial_inverse_lower hx (show 0 < 4 * s by positivity)
    (show 4 * s ≤ 1 by linarith)
  have hps : 0 < logProfile s := logProfile_pos hs (show s ≤ 2 by linarith)
  rw [hpx]
  apply (le_div_iff₀ hps).mpr
  have hH' := mul_le_mul_of_nonneg_left hH (show 0 ≤ logProfile s / 512 by positivity)
  change -4 * logProfile s ≤ ∫ y in N, differenceKernel (logGapFunction r) x y at hN
  change _ ≤ 4 * logProfile s + (1 - 1 / 512 : ℝ) * logProfile s *
    ∫ y in F, 1 / |x - y| at hfar
  change (logProfile s / 512) * Real.log (1 / (4 * s)) ≤
    (logProfile s / 512) * ∫ y in F, 1 / |x - y| at hH'
  nlinarith

/-- The explicit scale `ρ` makes the gap quotient strictly larger than `A+2`. -/
theorem logarithmic_integral_lower_bound_at_scale {r : ℝ → ℝ} {A x s : ℝ}
    (hA : 1 < A) (hrm : Measurable r) (hx : x ∈ interval) (hs : 0 < s)
    (hsmall : s ≤ gapScale A / 2) (hrx : r x = s)
    (hr : ∀ y ∈ interval, 0 ≤ r y ∧ r y ≤ 2)
    (hLip : ∀ y ∈ interval, |r y - s| ≤ |x - y|)
    (hball : ∀ t ∈ Icc (4 * s) 2,
      ((volume.restrict interval).restrict {y | r y ≠ 0}) {y | |x - y| ≤ t} ≤
        ENNReal.ofReal (127 / 128 : ℝ) * (volume.restrict interval) {y | |x - y| ≤ t}) :
    A + 2 < logarithmicOperator (logGapFunction r) x / logGapFunction r x := by
  have hs4 : s ≤ 1 / 4 := by linarith [gapScale_le_half hA]
  have hT := gapScale_log_parameter hA hs hsmall
  rw [Real.log_div (Real.exp_pos 8).ne' hs.ne', Real.log_exp] at hT
  exact (gapScale_lower_bound hA hs hsmall).trans_le
    (logarithmic_integral_lower_bound hrm hx hs hs4 hT hrx hr hLip hball)

end Erdos1132.Counterexample
