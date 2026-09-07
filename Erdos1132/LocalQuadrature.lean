import Erdos1132.AveragedQuadrature
import Erdos1132.TaoPotential

/-! # Quantitative quadrature for functions supported in an interior interval -/

noncomputable section
open MeasureTheory Set Finset Real
open scoped BigOperators
namespace Erdos1132

theorem potential_difference_density_bound {C e h α ρ U₁ U₂ : ℝ} (hh : 0 < h)
    (h₁ : |U₁-α+Real.pi*h*ρ| ≤ C*(e+h^3))
    (h₂ : |U₂-α+Real.pi*(2*h)*ρ| ≤ C*(e+(2*h)^3)) :
    |(U₁-U₂)/(Real.pi*h)-ρ| ≤ C*(2*e+9*h^3)/(Real.pi*h) := by
  have he : (U₁-U₂)/(Real.pi*h)-ρ =
      ((U₁-α+Real.pi*h*ρ)-(U₂-α+Real.pi*(2*h)*ρ))/(Real.pi*h) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos Real.pi_pos hh)]
  apply div_le_div_of_nonneg_right _ (mul_pos Real.pi_pos hh).le
  calc
    _ ≤ |U₁-α+Real.pi*h*ρ|+|U₂-α+Real.pi*(2*h)*ρ| := abs_sub _ _
    _ ≤ C*(e+h^3)+C*(e+(2*h)^3) := add_le_add h₁ h₂
    _ = _ := by ring

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem integrable_exteriorDensity_mul_supported {a b l r α C M : ℝ}
    {f : ℝ → ℝ} (hf : Measurable f) (hM : ∀ x, |f x| ≤ M)
    (hρ : ∀ x ∈ Icc l r, |X.exteriorDensity a b α x 0| ≤ C)
    (hsupp : ∀ x, x ∉ Icc l r → f x = 0) :
    Integrable (fun x => X.exteriorDensity a b α x 0*f x) := by
  have hm : Measurable (fun x => X.exteriorDensity a b α x 0*f x) :=
    (X.measurable_exteriorDensity a b α 0).mul hf
  have hi : IntegrableOn (fun x => X.exteriorDensity a b α x 0*f x) (Icc l r) := by
    apply (integrable_const (C*M)).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    have hM0 := (abs_nonneg (f x)).trans (hM x)
    have hC0 := (abs_nonneg (X.exteriorDensity a b α x 0)).trans (hρ x hx)
    exact mul_le_mul (hρ x hx) (hM x) (abs_nonneg _) hC0
  exact hi.integrable_of_forall_notMem_eq_zero (fun x hx => by rw [hsupp x hx, mul_zero])

end Nodes

/-- The error is uniform over all bounded Lipschitz functions with support in
the specified interior interval. -/
theorem uniform_local_quadrature {a b d l r : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) (hlr : l ≤ r)
    (hJ : Icc l r ⊆ Icc (a+d) (b-d)) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      ∀ (f : ℝ → ℝ) (M L h δ : ℝ), Measurable f →
      (∀ x, |f x| ≤ M) → 0 ≤ L →
      (∀ x y, |f x-f y| ≤ L*|x-y|) →
      (∀ x, x ∉ Icc l r → f x = 0) → 0 < δ → 1/(n : ℝ) ≤ h →
      |(∑ i, f (X.point i))/(n : ℝ)-
        ∫ x, X.exteriorDensity a b X.potentialNormalization x 0*f x| ≤
        L*δ+8*M*h/(Real.pi*δ)+C*M*(potentialErrorSize n/h+h^2) := by
  obtain ⟨Cp, hCp, hpot⟩ := uniform_complex_potential_expansion hab hI hd
  obtain ⟨Cr, hCr, hden⟩ := uniform_exterior_density_bounds hab hI hd
  refine ⟨18*Cp/Real.pi, by positivity, ?_⟩
  intro n X hn hΛ f M L h δ hf hM hL hlip hsupp hδ hnh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hh : 0 < h := (one_div_pos.mpr hnR).trans_le hnh
  have hM0 := (abs_nonneg (f 0)).trans (hM 0)
  have hE := potentialErrorSize_nonneg hn
  let ρ := fun x => X.exteriorDensity a b X.potentialNormalization x 0
  let D := fun x => (X.complexLogPotential x h-X.complexLogPotential x (2*h))/(Real.pi*h)
  have hpoint (x : ℝ) (hx : x ∈ Icc l r) :
      |D x-ρ x| ≤ Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h) :=
    potential_difference_density_bound hh (hpot n X hn hΛ x (hJ hx) h hnh)
      (hpot n X hn hΛ x (hJ hx) (2*h) (hnh.trans (by linarith)))
  have hiD : Integrable (fun x => D x*f x) := X.integrable_averaged_node_kernel_mul hh hf hM
  have hiρ : Integrable (fun x => ρ x*f x) := X.integrable_exteriorDensity_mul_supported hf hM
    (fun x hx => (hden n X hn hΛ).1 x (hJ hx)) hsupp
  have he : (∫ x, D x*f x)-(∫ x, ρ x*f x) = ∫ x, (D x-ρ x)*f x := by
    rw [← integral_sub hiD hiρ]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hdiff : |(∫ x, D x*f x)-(∫ x, ρ x*f x)| ≤
      (r-l)*(Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M) := by
    rw [he, ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Icc l r) (fun x hx => by rw [hsupp x hx, mul_zero])]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc l r)
      (f := fun x => (D x-ρ x)*f x) (by simp) (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hpoint x hx) (hM x) (abs_nonneg _)
          (by positivity : 0 ≤ Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)))
    simpa only [Real.norm_eq_abs, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hlr), mul_comm] using hb
  have hlen : r-l ≤ 2 := by
    have hl := hI (mem_interval_of_inset hd.le (hJ (left_mem_Icc.mpr hlr)))
    have hr := hI (mem_interval_of_inset hd.le (hJ (right_mem_Icc.mpr hlr)))
    linarith [hl.1, hr.2]
  have hlast : (r-l)*(Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M) ≤
      (18*Cp/Real.pi)*M*(potentialErrorSize n/h+h^2) := by
    have h1 := mul_le_mul_of_nonneg_right hlen
      (by positivity : 0 ≤ Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M)
    have h2 : 2*(Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M) ≤
        (18*Cp/Real.pi)*M*(potentialErrorSize n/h+h^2) := by
      apply (mul_le_mul_iff_left₀ (mul_pos Real.pi_pos hh)).mp
      field_simp
      nlinarith [mul_nonneg hCp.le (mul_nonneg hM0 hE)]
    exact h1.trans h2
  have hq := X.averaged_node_quadrature_bound hn hh hδ hf hM hL hlip
  calc
    _ ≤ |(∑ i, f (X.point i))/(n : ℝ)-(∫ x, D x*f x)| +
        |(∫ x, D x*f x)-(∫ x, ρ x*f x)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hq (hdiff.trans hlast)

end Erdos1132
