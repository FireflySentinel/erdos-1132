import Erdos1132.Counterexample.CantorLogarithmicBound
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Regularity and bounds for the logarithmic Cantor profile

Paper: §7.2, the logarithmic integral estimate.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Erdos1132.Counterexample

def cantorProfile (ρ : ℝ) : ℝ → ℝ := logGapFunction (cantorRadius ρ)

theorem cantorProfile_measurable {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    Measurable (cantorProfile ρ) := measurable_logGapFunction (cantorRadius_continuous hρ hρ4).measurable

theorem cantorProfile_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (x : ℝ) :
    0 ≤ cantorProfile ρ x ∧ cantorProfile ρ x ≤ 1 := by
  have hn := cantorRadius_nonneg hρ hρ4 x
  have hb : cantorRadius ρ x ≤ 2 := by linarith [cantorRadius_bound hρ hρ4 x]
  exact ⟨logGapFunction_nonneg hn hb, logGapFunction_le_one hn hb⟩

theorem cantorProfile_zero {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∉ cantorOpen ρ) :
    cantorProfile ρ x = 0 := by simp [cantorProfile, logGapFunction, cantorRadius_zero hρ hρ4 hx]

theorem cantorProfile_pos {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∈ cantorOpen ρ) :
    0 < cantorProfile ρ x := by
  have hp := (cantorRadius_pos_iff hρ hρ4).mpr hx
  simp only [cantorProfile, logGapFunction, if_neg hp.ne']
  exact logProfile_pos hp (by linarith [cantorRadius_bound hρ hρ4 x])

theorem cantorRadius_contDiffAt {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∈ cantorOpen ρ) :
    ContDiffAt ℝ ∞ (cantorRadius ρ) x := by
  obtain ⟨b,c,_,_,he⟩ := cantorRadius_locally_polynomial hρ hρ4 hx
  have hp : ContDiff ℝ ∞ (gapRadius b c) :=
    (((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id)).div_const (c-b))
  exact hp.contDiffAt.congr_of_eventuallyEq he

theorem cantorProfile_contDiffAt {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∈ cantorOpen ρ) :
    ContDiffAt ℝ ∞ (cantorProfile ρ) x := by
  have hr := cantorRadius_contDiffAt hρ hρ4 hx
  have hp := (cantorRadius_pos_iff hρ hρ4).mpr hx
  have hb : cantorRadius ρ x ≤ 2 := by linarith [cantorRadius_bound hρ hρ4 x]
  have hlog : Real.log (cantorRadius ρ x) < 8 := by
    have hh := Real.log_le_sub_one_of_pos hp
    linarith
  have hf : ContDiffAt ℝ ∞ (fun y => logProfile (cantorRadius ρ y)) x :=
    (contDiffAt_const.sub (hr.log hp.ne')).rpow_const_of_ne (by linarith)
  apply hf.congr_of_eventuallyEq
  filter_upwards [(isOpen_cantorOpen ρ).mem_nhds hx] with y hy
  have hp' := (cantorRadius_pos_iff hρ hρ4).mpr hy
  simp only [cantorProfile, logGapFunction, if_neg hp'.ne']

theorem cantorProfile_integrable {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    IntegrableOn (cantorProfile ρ) interval := by
  apply (integrable_const (1:ℝ)).mono' (cantorProfile_measurable hρ hρ4).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (cantorProfile_bounds hρ hρ4 y).1]
    exact (cantorProfile_bounds hρ hρ4 y).2)

theorem cantorProfile_kernel_integrable {A x : ℝ} (hA : 1 < A) (hx : x ∈ cantorOpen (gapScale A)) :
    IntegrableOn (differenceKernel (cantorProfile (gapScale A)) x) interval := by
  have hρ : 0 < gapScale A := Real.exp_pos _
  have hρ4 := gapScale_le_quarter hA
  have hs := (cantorRadius_pos_iff hρ hρ4).mpr hx
  have hb := cantorRadius_bound hρ hρ4 x
  have hT := gapScale_log_parameter hA hs (show cantorRadius (gapScale A) x ≤ gapScale A/2 by linarith)
  rw [Real.log_div (Real.exp_pos 8).ne' hs.ne', Real.log_exp] at hT
  apply integrableOn_gap_differenceKernel (cantorRadius_continuous hρ hρ4).measurable
    ⟨hx.1.1.le,hx.1.2.le⟩ hs (by linarith) hT rfl
  · intro y _
    exact ⟨cantorRadius_nonneg hρ hρ4 y, by linarith [cantorRadius_bound hρ hρ4 y]⟩
  · intro y _
    simpa only [abs_sub_comm] using cantorRadius_lipschitz_bound hρ hρ4 y x

end Erdos1132.Counterexample
