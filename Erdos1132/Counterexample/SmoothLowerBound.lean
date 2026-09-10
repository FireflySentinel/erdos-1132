import Erdos1132.Counterexample.LogarithmicOperator
import Erdos1132.Counterexample.InverseDistance
import Erdos1132.Counterexample.Constants
import Erdos1132.Counterexample.LogProfile

/-!
# The cutoff estimate on the compact set

For `v = χ u + (1-χ) ε` and `χ(x)=0`, the logarithmic integral equals
`ε A - W`. A local modulus bound for `u` and the exact logarithmic tail
estimate control `W`; the explicit cutoff index supplies the lower bound.

Companion note: §2.3, smooth positive approximations.
-/

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1132.Counterexample

def smoothCutoff (χ u : ℝ → ℝ) (ε : ℝ) (y : ℝ) : ℝ :=
  χ y * u y + (1 - χ y) * ε

/-- A cutoff that vanishes near the query point makes the inverse-distance
weight integrable. -/
theorem integrableOn_cutoff_inverseDistance {χ : ℝ → ℝ} {x δ : ℝ}
    (hχm : Measurable χ) (hδ : 0 < δ)
    (hχ : ∀ y ∈ interval, 0 ≤ χ y ∧ χ y ≤ 1)
    (hzero : ∀ y ∈ interval, |x - y| ≤ δ → χ y = 0) :
    IntegrableOn (fun y => χ y / |x - y|) interval := by
  have hmeas : Measurable (fun y => χ y / |x - y|) :=
    hχm.div (continuous_const.sub continuous_id).abs.measurable
  have hconst : IntegrableOn (fun _ : ℝ => 1 / δ) interval := continuous_const.integrableOn_Icc
  apply hconst.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hχ y hy).1 (abs_nonneg _))]
  by_cases hnear : |x - y| ≤ δ
  · rw [hzero y hy hnear, zero_div]
    positivity
  · exact div_le_div₀ (by norm_num) (hχ y hy).2 hδ (le_of_not_ge hnear)

/-- The exact logarithmic-integral identity at a point where the cutoff vanishes. -/
theorem logarithmicOperator_smoothCutoff {χ u : ℝ → ℝ} {ε x : ℝ}
    (hx : χ x = 0)
    (hA : IntegrableOn (fun y => χ y / |x - y|) interval)
    (hW : IntegrableOn (fun y => χ y * u y / |x - y|) interval) :
    logarithmicOperator (smoothCutoff χ u ε) x =
      ε * (∫ y in interval, χ y / |x - y|) -
        ∫ y in interval, χ y * u y / |x - y| := by
  unfold logarithmicOperator
  have hid : differenceKernel (smoothCutoff χ u ε) x =
      fun y => ε * (χ y / |x - y|) - χ y * u y / |x - y| := by
    funext y
    simp only [differenceKernel, smoothCutoff, hx, zero_mul, sub_zero, one_mul]
    ring
  rw [hid, integral_sub (hA.const_mul ε) hW, integral_const_mul]

/-- A local upper bound for `u` controls its cutoff-weighted singular integral. -/
theorem cutoff_weighted_integral_le {χ u : ℝ → ℝ} {ε x d : ℝ}
    (hx : x ∈ interval) (hε : 0 ≤ ε) (hd : 0 < d) (hd2 : d ≤ 2)
    (hχ : ∀ y ∈ interval, 0 ≤ χ y ∧ χ y ≤ 1)
    (hu : ∀ y ∈ interval, u y ≤ 1)
    (hnear : ∀ y ∈ interval, |x - y| ≤ d → u y ≤ ε / 2)
    (hA : IntegrableOn (fun y => χ y / |x - y|) interval)
    (hW : IntegrableOn (fun y => χ y * u y / |x - y|) interval) :
    (∫ y in interval, χ y * u y / |x - y|) ≤
      ε / 2 * (∫ y in interval, χ y / |x - y|) + 2 * Real.log (2 / d) := by
  let S : Set ℝ := interval ∩ {y | d < |x - y|}
  have hSm : MeasurableSet S := measurableSet_Icc.inter
    (isOpen_lt continuous_const (continuous_const.sub continuous_id).abs).measurableSet
  have hS : S ⊆ radialAnnulus x d 2 := by
    intro y hy
    refine ⟨hy.2.le, ?_⟩
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1.1, hy.1.2]
  have hiS := ((integrableOn_inverseDistance_annulus hd).mono_set hS).integrable_indicator hSm
  have hpt : ∀ y ∈ interval,
      χ y * u y / |x - y| ≤ ε / 2 * (χ y / |x - y|) +
        S.indicator (fun y => 1 / |x - y|) y := by
    intro y hy
    by_cases hfar : d < |x - y|
    · rw [Set.indicator_of_mem (show y ∈ S from ⟨hy, hfar⟩)]
      have hχu : χ y * u y ≤ 1 :=
        (mul_le_mul_of_nonneg_left (hu y hy) (hχ y hy).1).trans (by simpa using (hχ y hy).2)
      have hquot := div_le_div_of_nonneg_right hχu (abs_nonneg (x - y))
      have hnonneg : 0 ≤ ε / 2 * (χ y / |x - y|) := by positivity [(hχ y hy).1]
      linarith
    · rw [Set.indicator_of_notMem (show y ∉ S from fun h => hfar h.2), add_zero]
      have hprod := mul_le_mul_of_nonneg_left (hnear y hy (le_of_not_gt hfar)) (hχ y hy).1
      have hquot := div_le_div_of_nonneg_right hprod (abs_nonneg (x - y))
      calc
        _ ≤ (χ y * (ε / 2)) / |x - y| := hquot
        _ = _ := by ring
  have hint := integral_mono_ae hW ((hA.const_mul (ε / 2)).add hiS.integrableOn)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy; exact hpt y hy)
  simp only [Pi.add_apply] at hint
  rw [integral_add (hA.const_mul (ε / 2)) hiS.integrableOn, integral_const_mul] at hint
  have heq : (∫ y in interval, S.indicator (fun y => 1 / |x - y|) y) =
      ∫ y in S, 1 / |x - y| := by
    rw [integral_indicator hSm, Measure.restrict_restrict hSm]
    have hSI : S ∩ interval = S := inter_eq_left.mpr inter_subset_left
    rw [hSI]
  rw [heq] at hint
  exact hint.trans (add_le_add le_rfl (integral_inverseDistance_le hd hd2 hS))

/-- The explicit cutoff gives the lower bound on `F` from the cumulative gap
estimate and the local modulus of `u`. -/
theorem smoothCutoff_lower_bound {χ u : ℝ → ℝ} {A x : ℝ} {j : ℕ}
    (hj : 0 < j) (hx : x ∈ interval) (hχx : χ x = 0)
    (hχ : ∀ y ∈ interval, 0 ≤ χ y ∧ χ y ≤ 1)
    (hu : ∀ y ∈ interval, u y ≤ 1)
    (hnear : ∀ y ∈ interval, |x - y| ≤ cutoffRadius j → u y ≤ 1 / (2 * (j : ℝ)))
    (hAi : IntegrableOn (fun y => χ y / |x - y|) interval)
    (hWi : IntegrableOn (fun y => χ y * u y / |x - y|) interval)
    (hA : (cutoffIndex A j : ℝ) / 16 ≤ ∫ y in interval, χ y / |x - y|) :
    (A + 1) * smoothCutoff χ u (1 / j) x ≤
      logarithmicOperator (smoothCutoff χ u (1 / j)) x := by
  have hjr : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hnear' : ∀ y ∈ interval, |x - y| ≤ cutoffRadius j → u y ≤ (1 / (j : ℝ)) / 2 := by
    intro y hy hd
    simpa only [div_div, mul_comm (j : ℝ) 2] using hnear y hy hd
  have hW := cutoff_weighted_integral_le hx (by positivity : (0 : ℝ) ≤ 1 / j)
    (cutoffRadius_pos j) (cutoffRadius_le_two hj) hχ hu hnear' hAi hWi
  have htail := cutoffRadius_tail_bound j
  have hscale := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ 1 / (2 * j) by positivity)
  have hmargin := cutoffIndex_margin A hj
  rw [logarithmicOperator_smoothCutoff hχx hAi hWi]
  simp only [smoothCutoff, hχx, zero_mul, sub_zero, one_mul]
  have halgebra : (1 / (2 * (j : ℝ))) * ((cutoffIndex A j : ℝ) / 16) =
      (cutoffIndex A j : ℝ) / (32 * j) := by ring
  rw [halgebra] at hscale
  have hhalf : (1 / (j : ℝ)) / 2 = 1 / (2 * j) := by ring
  rw [hhalf] at hW
  simp only [zero_add, mul_one_div]
  have hdouble : (1 / (j : ℝ)) * (∫ y in interval, χ y / |x - y|) =
      2 * ((1 / (2 * j)) * (∫ y in interval, χ y / |x - y|)) := by ring
  rw [hdouble]
  linarith

/-- The lower bound with explicit `u=p(r)` and cutoff indices.
The geometric input is the cumulative cutoff integral bound at `x`. -/
theorem explicit_smoothCutoff_lower_bound {χ r : ℝ → ℝ} {A x δ : ℝ} {j : ℕ}
    (hj : 0 < j) (hx : x ∈ interval)
    (hχm : Measurable χ) (hrm : Measurable r) (hδ : 0 < δ)
    (hχ : ∀ y ∈ interval, 0 ≤ χ y ∧ χ y ≤ 1)
    (hzero : ∀ y ∈ interval, |x - y| ≤ δ → χ y = 0)
    (hr : ∀ y ∈ interval, 0 ≤ r y ∧ r y ≤ 2)
    (hdist : ∀ y ∈ interval, r y ≤ |x - y|)
    (hA : (cutoffIndex A j : ℝ) / 16 ≤ ∫ y in interval, χ y / |x - y|) :
    (A + 1) * smoothCutoff χ (logGapFunction r) (1 / j) x ≤
      logarithmicOperator (smoothCutoff χ (logGapFunction r) (1 / j)) x := by
  have hχx : χ x = 0 := hzero x hx (by simpa using hδ.le)
  have hAi := integrableOn_cutoff_inverseDistance hχm hδ hχ hzero
  have hum := measurable_logGapFunction hrm
  have hWi : IntegrableOn (fun y => χ y * logGapFunction r y / |x - y|) interval := by
    apply hAi.mono' ((hχm.mul hum).div
      (continuous_const.sub continuous_id).abs.measurable).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    change ‖χ y * logGapFunction r y / |x - y|‖ ≤ χ y / |x - y|
    have hu0 := logGapFunction_nonneg (hr y hy).1 (hr y hy).2
    have hu1 := logGapFunction_le_one (hr y hy).1 (hr y hy).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [(hχ y hy).1])]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 (hχ y hy).1
  apply smoothCutoff_lower_bound hj hx hχx hχ
    (fun y hy => logGapFunction_le_one (hr y hy).1 (hr y hy).2) _ hAi hWi hA
  intro y hy hnear
  exact logGapFunction_le_at_cutoff hj (hr y hy).1 ((hdist y hy).trans hnear)

end Erdos1132.Counterexample
