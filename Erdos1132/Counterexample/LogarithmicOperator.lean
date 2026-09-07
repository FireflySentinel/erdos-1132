import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# The logarithmic difference operator in Section 7

This file proves the analytic estimate (7.1), including absolute integrability,
and quantitative stability of the quotient `L f / f`.
-/

noncomputable section

open MeasureTheory Set

namespace Erdos1132.Counterexample

abbrev interval : Set ℝ := Icc (-1) 1

def differenceKernel (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (f x - f y) / |x - y|

def logarithmicOperator (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in interval, differenceKernel f x y

theorem abs_differenceKernel_le {f : ℝ → ℝ} {K x y : ℝ}
    (hK : 0 ≤ K) (h : |f x - f y| ≤ K * |x - y|) :
    |differenceKernel f x y| ≤ K := by
  by_cases hxy : x = y
  · simp [differenceKernel, hxy, hK]
  · rw [differenceKernel, abs_div, abs_abs]
    exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy))).mpr h

theorem differenceKernel_bound_of_derivative {f f' : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x)
    (hbound : ∀ x ∈ interval, |f' x| ≤ K)
    {x y : ℝ} (hx : x ∈ interval) (hy : y ∈ interval) :
    |differenceKernel f x y| ≤ K := by
  apply abs_differenceKernel_le hK
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      hf (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ht) hy hx

theorem abs_logarithmicOperator_le {f : ℝ → ℝ} {K x : ℝ}
    (hbound : ∀ y ∈ interval, |differenceKernel f x y| ≤ K) :
    |logarithmicOperator f x| ≤ 2 * K := by
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict interval)
    (f := differenceKernel f x) (C := K) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      simpa only [Real.norm_eq_abs] using hbound y hy)
  norm_num [logarithmicOperator, interval, Real.norm_eq_abs,
    measureReal_restrict_apply_univ, Real.volume_real_Icc, mul_comm] at h ⊢
  exact h

/-- Equation (7.1), expressed pointwise with an arbitrary derivative bound. -/
theorem abs_logarithmicOperator_le_of_derivative {f f' : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x)
    (hbound : ∀ x ∈ interval, |f' x| ≤ K)
    {x : ℝ} (hx : x ∈ interval) :
    |logarithmicOperator f x| ≤ 2 * K :=
  abs_logarithmicOperator_le (fun _ hy =>
    differenceKernel_bound_of_derivative hK hf hbound hx hy)

theorem integrable_differenceKernel {f f' : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x)
    (hbound : ∀ x ∈ interval, |f' x| ≤ K)
    {x : ℝ} (hx : x ∈ interval) :
    IntegrableOn (differenceKernel f x) interval := by
  have hcont : ContinuousOn f interval := fun y hy => (hf y hy).continuousWithinAt
  have hm : AEStronglyMeasurable (differenceKernel f x) (volume.restrict interval) := by
    apply AEMeasurable.aestronglyMeasurable
    exact (aemeasurable_const.sub (hcont.aemeasurable measurableSet_Icc)).div
      ((continuous_const.sub continuous_id).abs.measurable.aemeasurable)
  apply (integrable_const K).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  simpa only [Real.norm_eq_abs] using
    differenceKernel_bound_of_derivative hK hf hbound hx hy

theorem logarithmicOperator_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : IntegrableOn (differenceKernel f x) interval)
    (hg : IntegrableOn (differenceKernel g x) interval) :
    logarithmicOperator (fun t => f t - g t) x =
      logarithmicOperator f x - logarithmicOperator g x := by
  unfold logarithmicOperator
  rw [← integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [differenceKernel]
  ring

/-- Uniform control of derivative errors controls the operator error. -/
theorem logarithmicOperator_sub_bound {f g f' g' : ℝ → ℝ} {Kf Kg ε : ℝ}
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hε : 0 ≤ ε)
    (hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x)
    (hg : ∀ x ∈ interval, HasDerivWithinAt g (g' x) interval x)
    (hbf : ∀ x ∈ interval, |f' x| ≤ Kf)
    (hbg : ∀ x ∈ interval, |g' x| ≤ Kg)
    (hclose : ∀ x ∈ interval, |f' x - g' x| ≤ ε)
    {x : ℝ} (hx : x ∈ interval) :
    |logarithmicOperator f x - logarithmicOperator g x| ≤ 2 * ε := by
  rw [← logarithmicOperator_sub
    (integrable_differenceKernel hKf hf hbf hx)
    (integrable_differenceKernel hKg hg hbg hx)]
  exact abs_logarithmicOperator_le_of_derivative hε
    (fun y hy => (hf y hy).sub (hg y hy)) hclose hx

/-- A quantitative form of stability of the quotient under C¹ perturbations.
Both denominators have the explicitly stated positive lower bound `m`. -/
theorem logarithmicRatio_sub_bound {f g f' g' : ℝ → ℝ} {Kf Kg ε δ m : ℝ}
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hm : 0 < m)
    (hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x)
    (hg : ∀ x ∈ interval, HasDerivWithinAt g (g' x) interval x)
    (hbf : ∀ x ∈ interval, |f' x| ≤ Kf)
    (hbg : ∀ x ∈ interval, |g' x| ≤ Kg)
    (hclose : ∀ x ∈ interval, |f' x - g' x| ≤ ε)
    (hval : ∀ x ∈ interval, |f x - g x| ≤ δ)
    (hposf : ∀ x ∈ interval, m ≤ f x)
    (hposg : ∀ x ∈ interval, m ≤ g x)
    {x : ℝ} (hx : x ∈ interval) :
    |logarithmicOperator f x / f x - logarithmicOperator g x / g x| ≤
      2 * ε / m + 2 * Kg * δ / (m * m) := by
  have hfx : 0 < f x := hm.trans_le (hposf x hx)
  have hgx : 0 < g x := hm.trans_le (hposg x hx)
  have herr := logarithmicOperator_sub_bound hKf hKg hε hf hg hbf hbg hclose hx
  have hLg := abs_logarithmicOperator_le_of_derivative hKg hg hbg hx
  have hid : logarithmicOperator f x / f x - logarithmicOperator g x / g x =
      (logarithmicOperator f x - logarithmicOperator g x) / f x +
      logarithmicOperator g x * (g x - f x) / (f x * g x) := by
    field_simp
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_div, abs_of_pos hfx]
    exact div_le_div₀ (by positivity) herr hm (hposf x hx)
  · rw [abs_div, abs_mul, abs_sub_comm (g x), abs_of_pos (mul_pos hfx hgx)]
    apply div_le_div₀ (by positivity)
      (mul_le_mul hLg (hval x hx) (abs_nonneg _) (by positivity))
      (mul_pos hm hm)
    exact mul_le_mul (hposf x hx) (hposg x hx) hm.le hfx.le

/-- The local-equality / L¹-tail estimate used in Section 7.3. It applies to
the nonsmooth limiting function as well as to smooth approximations. -/
theorem logarithmicOperator_local_eq_bound {f g : ℝ → ℝ} {x r : ℝ}
    (hx : x ∈ interval) (hr : 0 < r)
    (hf : IntegrableOn (differenceKernel f x) interval)
    (hg : IntegrableOn (differenceKernel g x) interval)
    (hfg : IntegrableOn (fun y => f y - g y) interval)
    (hlocal : ∀ y ∈ interval, |x - y| < r → f y = g y) :
    |logarithmicOperator f x - logarithmicOperator g x| ≤
      (∫ y in interval, |f y - g y|) / r := by
  have hxeq : f x = g x := hlocal x hx (by simpa using hr)
  rw [← logarithmicOperator_sub hf hg]
  have hbound : ∀ y ∈ interval,
      ‖differenceKernel (fun t => f t - g t) x y‖ ≤ |f y - g y| / r := by
    intro y hy
    by_cases hnear : |x - y| < r
    · simp [differenceKernel, hxeq, hlocal y hy hnear]
    · simp only [differenceKernel, hxeq, sub_self, zero_sub, Real.norm_eq_abs,
        abs_div, abs_neg, abs_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hr (le_of_not_gt hnear)
  have h := norm_integral_le_of_norm_le (hfg.norm.div_const r) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hbound y hy)
  simpa only [logarithmicOperator, Real.norm_eq_abs, integral_div] using h

end Erdos1132.Counterexample
