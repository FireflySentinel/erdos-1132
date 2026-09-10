import Erdos1132.Counterexample.AmplitudeRemainder
import Erdos1132.Counterexample.LogarithmicOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The finite-part identity as a proper integral

The singular terms cancel pointwise. The remaining divided-difference term
is a logarithmic derivative, whose integral is evaluated on the two sides
of the interior parameter.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

theorem integral_jump_mul {f : ℝ → ℝ} {l s r : ℝ}
    (hs : s ∈ Ioo l r) (hf : ContinuousOn f (Icc l r)) :
    (∫ t in l..r, jumpSign s t * f t) =
      (∫ t in s..r, f t) - ∫ t in l..s, f t := by
  have hab := hs.1.le.trans hs.2.le
  have hi := jump_mul_intervalIntegrable (s := s) hab hf
  have hl : IntervalIntegrable (fun t => jumpSign s t * f t) volume l s := by
    apply hi.mono_set
    rw [uIcc_of_le hs.1.le, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hs.2.le
  have hr : IntervalIntegrable (fun t => jumpSign s t * f t) volume s r := by
    apply hi.mono_set
    rw [uIcc_of_le hs.2.le, uIcc_of_le hab]
    exact Icc_subset_Icc hs.1.le le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr]
  have heql : (∫ t in l..s, jumpSign s t * f t) = -(∫ t in l..s, f t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le hs.1.le
    intro t ht
    simp [jumpSign, ht.2]
  have heqr : (∫ t in s..r, jumpSign s t * f t) = ∫ t in s..r, f t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hs.2.le
    intro t ht
    simp [jumpSign, ht.1, not_lt.mpr ht.1.le]
  rw [heql, heqr]
  ring

theorem integral_jump_derivative {f f' : ℝ → ℝ} {l s r : ℝ}
    (hs : s ∈ Ioo l r)
    (hf : ∀ t ∈ Icc l r, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Icc l r)) :
    (∫ t in l..r, jumpSign s t * f' t) = f l + f r - 2*f s := by
  rw [integral_jump_mul hs hc]
  have hr : (∫ t in s..r, f' t) = f r - f s := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hs.2.le] at ht
      exact hf t ⟨hs.1.le.trans ht.1, ht.2⟩
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs.2.le]
      exact hc.mono (Icc_subset_Icc hs.1.le le_rfl)
  have hl : (∫ t in l..s, f' t) = f s - f l := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hs.1.le] at ht
      exact hf t ⟨ht.1, ht.2.trans hs.2.le⟩
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs.1.le]
      exact hc.mono (Icc_subset_Icc le_rfl hs.2.le)
  rw [hr, hl]
  ring

theorem jump_dslope_eq_differenceKernel {v X : ℝ → ℝ} {s t : ℝ}
    (hD : dslope X s t < 0) :
    jumpSign s t * dslope v (X s) (X t) = differenceKernel v (X s) (X t) := by
  by_cases hts : t = s
  · subst t
    simp [jumpSign, differenceKernel]
  · have hX : X t - X s = (t - s) * dslope X s t := by
      simpa only [smul_eq_mul] using (sub_smul_dslope X s t).symm
    have hxne : X t ≠ X s := sub_ne_zero.mp (hX ▸ mul_ne_zero (sub_ne_zero.mpr hts) hD.ne)
    rw [dslope_of_ne _ hxne, slope_def_field, differenceKernel, jumpSign_eq_div_abs,
      abs_sub_comm (X s) (X t), hX, abs_mul, abs_of_neg hD]
    field_simp [sub_ne_zero.mpr hts, hD.ne]
    ring

/-- The integral of the regular remainder, expressed through endpoint and
diagonal values of the coordinate divided difference. -/
theorem integral_amplitudeRemainder {v X : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Ioo 0 Real.pi)
    (hv : ∀ y ∈ Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ v y)
    (hX : ∀ t ∈ Icc 0 Real.pi, ContDiffAt ℝ ⊤ X t)
    (hmap : MapsTo X (Icc 0 Real.pi) (Icc (-1) 1))
    (h0 : X 0 = 1) (hπ : X Real.pi = -1)
    (hneg : ∀ t ∈ Icc 0 Real.pi, deriv X t ≤ 0)
    (hD : ∀ t ∈ Icc 0 Real.pi, dslope X s t < 0) :
    (∫ t in (0 : ℝ)..Real.pi, amplitudeRemainder v X s t) =
      -logarithmicOperator v (X s) + v (X s) *
        (Real.log (dslope X s 0) + Real.log (dslope X s Real.pi) -
          2*Real.log (deriv X s)) := by
  let F : ℝ → ℝ := fun t => dslope v (X s) (X t) * deriv X t
  let G : ℝ → ℝ := fun t => deriv (dslope X s) t / dslope X s t
  have hcF : ContinuousOn F (Icc 0 Real.pi) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact (((contDiffAt_dslope (hv _ (hmap ht)) (X s)).continuousAt.comp
      (hX t ht).continuousAt).mul
      ((hX t ht).derivWithin (m := 1) (by simp)).continuousAt)
  have hcG : ContinuousOn G (Icc 0 Real.pi) := by
    intro t ht
    exact (((contDiffAt_dslope (hX t ht) s).derivWithin (m := 1) (by simp)).continuousAt.div
      (contDiffAt_dslope (hX t ht) s).continuousAt (hD t ht).ne).continuousWithinAt
  have hiF := jump_mul_intervalIntegrable (s := s) Real.pi_pos.le hcF
  have hiG := jump_mul_intervalIntegrable (s := s) Real.pi_pos.le hcG
  have heq : EqOn (amplitudeRemainder v X s)
      (fun t => jumpSign s t * F t + v (X s) * (jumpSign s t * G t)) (Icc 0 Real.pi) := by
    intro t ht
    rw [amplitudeRemainder_eq_jump_mul ((hX t ht).differentiableAt (by simp))
      (hneg t ht) (hD t ht)]
    dsimp only [regularRemainder, F, G]
    ring
  have hif : (∫ t in (0 : ℝ)..Real.pi, jumpSign s t * F t) =
      -logarithmicOperator v (X s) := by
    calc
      _ = ∫ t in (0 : ℝ)..Real.pi, differenceKernel v (X s) (X t) * deriv X t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le Real.pi_pos.le] at ht
        dsimp only [F]
        rw [← mul_assoc, jump_dslope_eq_differenceKernel (hD t ht)]
      _ = ∫ y in X 0..X Real.pi, differenceKernel v (X s) y := by
        apply intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
          (f := X) (f' := deriv X) (g := differenceKernel v (X s))
        · rw [uIcc_of_le Real.pi_pos.le]
          exact fun t ht => (hX t ht).continuousAt.continuousWithinAt
        · intro t ht
          simp only [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at ht
          exact ((hX t ⟨ht.1.le, ht.2.le⟩).differentiableAt (by simp)).hasDerivAt
        · intro t ht
          simp only [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at ht
          exact hneg t ⟨ht.1.le, ht.2.le⟩
      _ = _ := by
        rw [h0, hπ, intervalIntegral.integral_symm]
        rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        simp only [logarithmicOperator, interval, integral_Icc_eq_integral_Ioc]
  have hig : (∫ t in (0 : ℝ)..Real.pi, jumpSign s t * G t) =
      Real.log (dslope X s 0) + Real.log (dslope X s Real.pi) -
        2*Real.log (deriv X s) := by
    simpa only [dslope_same] using integral_jump_derivative hs
      (fun t ht => ((contDiffAt_dslope (hX t ht) s).differentiableAt
        (by simp)).hasDerivAt.log (hD t ht).ne) hcG
  calc
    _ = ∫ t in (0 : ℝ)..Real.pi,
        jumpSign s t * F t + v (X s) * (jumpSign s t * G t) := by
      apply intervalIntegral.integral_congr
      simpa only [uIcc_of_le Real.pi_pos.le] using heq
    _ = _ := by
      rw [intervalIntegral.integral_add hiF (hiG.const_mul _),
        intervalIntegral.integral_const_mul, hif, hig]

end Erdos1132.Counterexample
