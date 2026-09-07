import Erdos1132.ApproximateIdentity

/-! # A quantitative approximate-identity estimate for Lipschitz functions -/

noncomputable section
open MeasureTheory Set Real
namespace Erdos1132

theorem probability_kernel_lipschitz_bound {k f : ℝ → ℝ} (hk : ∀ t, 0 ≤ k t)
    (hi : Integrable k) (hm : ∫ t, k t = 1) (hf : Measurable f)
    {M L δ : ℝ} (hM : ∀ t, |f t| ≤ M) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hlip : ∀ t, |f t-f 0| ≤ L*|t|) :
    |(∫ t, k t*f t)-f 0| ≤ L*δ+2*M*(∫ t in (Icc (-δ) δ)ᶜ, k t) := by
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0)
  have hif : Integrable (fun t => k t*f t) :=
    hi.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hM)
  have hid : Integrable (fun t => k t*(f t-f 0)) := by
    simpa only [mul_sub] using! hif.sub (hi.mul_const (f 0))
  have hie := hi.indicator (s := (Icc (-δ) δ)ᶜ) measurableSet_Icc.compl
  have hpoint (t : ℝ) : |k t*(f t-f 0)| ≤ (L*δ)*k t +
      (2*M)*(Icc (-δ) δ)ᶜ.indicator k t := by
    rw [abs_mul, abs_of_nonneg (hk t)]
    by_cases ht : t ∈ Icc (-δ) δ
    · rw [Set.indicator_of_notMem (show t ∉ (Icc (-δ) δ)ᶜ from not_not.mpr ht), mul_zero, add_zero]
      have hsmall := (hlip t).trans (mul_le_mul_of_nonneg_left (abs_le.mpr ht) hL)
      have hp := mul_le_mul_of_nonneg_left hsmall (hk t)
      nlinarith
    · rw [Set.indicator_of_mem (show t ∈ (Icc (-δ) δ)ᶜ from ht)]
      have hsmall : |f t-f 0| ≤ 2*M := (abs_sub _ _).trans (by linarith [hM t, hM 0])
      have hp := mul_le_mul_of_nonneg_left hsmall (hk t)
      have hplus := mul_nonneg (mul_nonneg hL hδ.le) (hk t)
      nlinarith
  have heq : (∫ t, k t*(f t-f 0)) = (∫ t, k t*f t)-f 0 := by
    simp_rw [mul_sub]
    rw [integral_sub hif (hi.mul_const _), integral_mul_const, hm, one_mul]
  rw [← heq]
  calc
    _ ≤ ∫ t, |k t*(f t-f 0)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L*δ)*k t+(2*M)*(Icc (-δ) δ)ᶜ.indicator k t :=
      integral_mono hid.abs ((hi.const_mul _).add (hie.const_mul _)) hpoint
    _ = _ := by
      rw [integral_add (hi.const_mul _) (hie.const_mul _), integral_const_mul,
        integral_const_mul, integral_indicator measurableSet_Icc.compl, hm, mul_one]

end Erdos1132
