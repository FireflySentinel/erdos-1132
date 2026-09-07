import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivative bounds after division by a simple zero

The extended divided difference is smooth for analytic functions. Taylor's
formula bounds its first two derivatives by derivatives of the original function.
-/

noncomputable section

open Set
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

theorem contDiffAt_dslope {f : ℝ → ℝ} {t : ℝ} (hf : ContDiffAt ℝ ⊤ f t) (a : ℝ) :
    ContDiffAt ℝ ⊤ (dslope f a) t := by
  by_cases ht : t = a
  · subst t
    obtain ⟨p, hp⟩ := hf.analyticAt
    exact (show AnalyticAt ℝ (dslope f a) a from
      ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩).contDiffAt
  · have hc : ContDiffAt ℝ ⊤ (fun t => (f t - f a) / (t - a)) t :=
      (hf.sub contDiffAt_const).div
        (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr ht)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht] with u hu
    rw [dslope_of_ne _ hu, slope_def_field]

theorem dslope_hasDerivAt {f : ℝ → ℝ} {a t : ℝ} (hf : DifferentiableAt ℝ f t)
    (ht : t ≠ a) : HasDerivAt (dslope f a)
      ((deriv f t * (t - a) - (f t - f a)) / (t - a)^2) t := by
  have hd := (hf.hasDerivAt.sub_const (f a)).div
    ((hasDerivAt_id t).sub_const a) (sub_ne_zero.mpr ht)
  simp only [id_eq, mul_one] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ht] with u hu
  rw [dslope_of_ne _ hu, slope_def_field]
  rfl

theorem dslope_second_hasDerivAt {f : ℝ → ℝ} {a t : ℝ} (hf : ContDiffAt ℝ ⊤ f t)
    (ht : t ≠ a) : HasDerivAt (deriv (dslope f a))
      ((deriv (deriv f) t * (t - a)^2 -
        2 * (deriv f t * (t - a) - (f t - f a))) / (t - a)^3) t := by
  have hfd := hf.differentiableAt (by simp)
  have hfd' := (hf.derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  have hN := (hfd'.hasDerivAt.mul ((hasDerivAt_id t).sub_const a)).sub
    (hfd.hasDerivAt.sub_const (f a))
  have hd := hN.div (((hasDerivAt_id t).sub_const a).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr ht))
  have he : deriv (dslope f a) =ᶠ[𝓝 t] (fun u =>
      (deriv f u * (u - a) - (f u - f a)) / (u - a)^2) := by
    filter_upwards [eventually_ne_nhds ht, hf.eventually (by simp)] with u hu hfu
    exact (dslope_hasDerivAt (hfu.differentiableAt (by simp)) hu).deriv
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq, mul_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, add_sub_cancel_right] at hd
  convert! hd.congr_of_eventuallyEq he using 1
  field_simp

theorem taylorWithinEval_one_explicit {f : ℝ → ℝ} {a t : ℝ}
    (hf : ContDiffAt ℝ ⊤ f t) (hat : t ≠ a) :
    taylorWithinEval f 1 (uIcc t a) t a = f t + deriv f t * (a - t) := by
  have he : iteratedDerivWithin 1 f (uIcc t a) t = deriv f t := by
    simpa only [iteratedDeriv_one] using iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_uIcc hat) (hf.of_le (show (1 : ℕ∞ω) ≤ ⊤ by simp))
      (left_mem_uIcc)
  rw [show 1 = 0 + 1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval]
  norm_num only [Nat.factorial_zero, Nat.cast_one, zero_add, one_mul, inv_one,
    pow_one, smul_eq_mul, he]
  ring

theorem taylorWithinEval_two_explicit {f : ℝ → ℝ} {a t : ℝ}
    (hf : ContDiffAt ℝ ⊤ f t) (hat : t ≠ a) :
    taylorWithinEval f 2 (uIcc t a) t a =
      f t + deriv f t * (a - t) + deriv (deriv f) t * (a - t)^2 / 2 := by
  have he : iteratedDerivWithin 2 f (uIcc t a) t = deriv (deriv f) t := by
    simpa only [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      iteratedDerivWithin_eq_iteratedDeriv (n := 2)
        (uniqueDiffOn_uIcc hat) (hf.of_le (show (2 : ℕ∞ω) ≤ ⊤ by simp))
        (left_mem_uIcc)
  rw [show 2 = 1 + 1 by rfl, taylorWithinEval_succ, taylorWithinEval_one_explicit hf hat]
  norm_num only [Nat.factorial_one, Nat.cast_one, one_mul, he, smul_eq_mul]
  ring

theorem abs_deriv_dslope_le_of_ne {f : ℝ → ℝ} {a t l r C : ℝ}
    (hf : ∀ u ∈ Icc l r, ContDiffAt ℝ ⊤ f u) (ha : a ∈ Icc l r) (ht : t ∈ Icc l r) (hne : t ≠ a)
    (hC : ∀ u ∈ Icc l r, |iteratedDeriv 2 f u| ≤ C) :
    |deriv (dslope f a) t| ≤ C / 2 := by
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (n := 1) hne (fun u hu =>
      ((hf u (uIcc_subset_Icc ht ha hu)).of_le (by simp)).contDiffWithinAt)
  have hus : u ∈ Icc l r :=
    (uIcc_subset_Icc ht ha) ⟨hu.1.le, hu.2.le⟩
  rw [taylorWithinEval_one_explicit (hf t ht) hne] at he
  have heq : deriv (dslope f a) t = iteratedDeriv 2 f u / 2 := by
    rw [(dslope_hasDerivAt ((hf t ht).differentiableAt (by simp)) hne).deriv]
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, mul_one] at he
    apply (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr hne))).mpr
    nlinarith [he]
  rw [heq, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (hC u hus) (by norm_num)

theorem abs_second_deriv_dslope_le_of_ne {f : ℝ → ℝ} {a t l r C : ℝ}
    (hf : ∀ u ∈ Icc l r, ContDiffAt ℝ ⊤ f u) (ha : a ∈ Icc l r) (ht : t ∈ Icc l r) (hne : t ≠ a)
    (hC : ∀ u ∈ Icc l r, |iteratedDeriv 3 f u| ≤ C) :
    |deriv (deriv (dslope f a)) t| ≤ C / 3 := by
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (n := 2) hne (fun u hu =>
      ((hf u (uIcc_subset_Icc ht ha hu)).of_le (by simp)).contDiffWithinAt)
  have hus : u ∈ Icc l r :=
    (uIcc_subset_Icc ht ha) ⟨hu.1.le, hu.2.le⟩
  rw [taylorWithinEval_two_explicit (hf t ht) hne] at he
  have heq : deriv (deriv (dslope f a)) t = iteratedDeriv 3 f u / 3 := by
    rw [(dslope_second_hasDerivAt (hf t ht) hne).deriv]
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, mul_one] at he
    apply (div_eq_iff (pow_ne_zero 3 (sub_ne_zero.mpr hne))).mpr
    nlinarith [he]
  rw [heq, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  exact div_le_div_of_nonneg_right (hC u hus) (by norm_num)

/-- A continuous bound on a punctured interval extends to its interior point. -/
theorem abs_le_at_interior_of_ne {g : ℝ → ℝ} {a l r C : ℝ}
    (ha : a ∈ Ioo l r) (hg : ContinuousAt g a)
    (hbound : ∀ t ∈ Icc l r, t ≠ a → |g t| ≤ C) : |g a| ≤ C := by
  apply le_of_tendsto (hg.abs.tendsto.mono_left nhdsWithin_le_nhds
    : Filter.Tendsto (fun t => |g t|) (𝓝[≠] a) (𝓝 |g a|))
  have hi : ∀ᶠ t in 𝓝[≠] a, t ∈ Ioo l r :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ha.1 ha.2)
  filter_upwards [hi, self_mem_nhdsWithin] with t ht hne
  exact hbound t ⟨ht.1.le, ht.2.le⟩ hne

theorem abs_deriv_dslope_le {f : ℝ → ℝ} {a t l r C : ℝ}
    (hf : ∀ u ∈ Icc l r, ContDiffAt ℝ ⊤ f u) (ha : a ∈ Ioo l r) (ht : t ∈ Icc l r)
    (hC : ∀ u ∈ Icc l r, |iteratedDeriv 2 f u| ≤ C) :
    |deriv (dslope f a) t| ≤ C / 2 := by
  by_cases hne : t = a
  · subst t
    exact abs_le_at_interior_of_ne ha
      ((contDiffAt_dslope (hf a ht) a).derivWithin (m := 0) (by simp)).continuousAt
      (fun t ht hne => abs_deriv_dslope_le_of_ne hf ⟨ha.1.le, ha.2.le⟩ ht hne hC)
  · exact abs_deriv_dslope_le_of_ne hf ⟨ha.1.le, ha.2.le⟩ ht hne hC

theorem abs_second_deriv_dslope_le {f : ℝ → ℝ} {a t l r C : ℝ}
    (hf : ∀ u ∈ Icc l r, ContDiffAt ℝ ⊤ f u) (ha : a ∈ Ioo l r) (ht : t ∈ Icc l r)
    (hC : ∀ u ∈ Icc l r, |iteratedDeriv 3 f u| ≤ C) :
    |deriv (deriv (dslope f a)) t| ≤ C / 3 := by
  by_cases hne : t = a
  · subst t
    have hc := (contDiffAt_dslope (hf a ht) a).derivWithin (m := 2) (by simp)
    exact abs_le_at_interior_of_ne ha (hc.derivWithin (m := 0) (by norm_num)).continuousAt
      (fun t ht hne => abs_second_deriv_dslope_le_of_ne hf ⟨ha.1.le, ha.2.le⟩ ht hne hC)
  · exact abs_second_deriv_dslope_le_of_ne hf ⟨ha.1.le, ha.2.le⟩ ht hne hC

theorem abs_dslope_le {f : ℝ → ℝ} {a t l r C : ℝ}
    (hf : ∀ u ∈ Icc l r, DifferentiableAt ℝ f u)
    (ha : a ∈ Icc l r) (ht : t ∈ Icc l r)
    (hC : ∀ u ∈ Icc l r, |deriv f u| ≤ C) : |dslope f a t| ≤ C := by
  by_cases hne : t = a
  · subst t
    simpa only [dslope_same] using hC a ha
  · rw [dslope_of_ne _ hne, slope_def_field, abs_div]
    apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr
    simpa only [Real.norm_eq_abs] using
      (convex_Icc l r).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u hu => (hf u hu).hasDerivAt.hasDerivWithinAt)
        (fun u hu => by simpa only [Real.norm_eq_abs] using hC u hu) ha ht

end Erdos1132.Counterexample
