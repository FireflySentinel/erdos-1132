import Erdos1132.Additive.ExteriorKernel
import Erdos1132.Additive.WeightedPotential

/-! # The exterior-integral density and its quantitative regularity

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Real
namespace Erdos1132.Nodes
variable {n : ℕ} (X : Nodes n)

/-- The density obtained from the boundary potential outside a fixed interval. -/
def exteriorDensity (a b α x h : ℝ) : ℝ :=
  -(1/Real.pi^2) * ∫ y in (Icc a b)ᶜ,
    (X.empiricalLogPotential y-α)/((y-x)^2+h^2)

theorem measurable_exteriorDensity (a b α h : ℝ) :
    Measurable (fun x => X.exteriorDensity a b α x h) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (X.empiricalLogPotential p.2-α)/((p.2-p.1)^2+h^2)) :=
    ((X.measurable_empiricalLogPotential.comp measurable_snd).sub_const α).div (by fun_prop)
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc a b)ᶜ)).measurable.const_mul _

theorem exterior_integral_bound (hn : 0 < n) {α C : ℝ} (hC : 0 ≤ C)
    {s : Set ℝ} (hs : MeasurableSet s) {g : ℝ → ℝ} (hg : Measurable g)
    (hbound : ∀ y ∈ s, |g y| ≤ C*(poissonKernel 1 y*|X.empiricalLogPotential y-α|)) :
    IntegrableOn g s ∧ |∫ y in s, g y| ≤ C*(weightedLogBound+|α|) := by
  have hi := (X.integrable_weighted_abs_potential_sub α).const_mul C
  have hgi : IntegrableOn g s := hi.integrableOn.mono' hg.aestronglyMeasurable.restrict
    (by filter_upwards [ae_restrict_mem hs] with y hy; simpa only [Real.norm_eq_abs] using hbound y hy)
  refine ⟨hgi, ?_⟩
  have hb := setIntegral_mono_on hgi.abs hi.integrableOn hs hbound
  have hnng : 0 ≤ᵐ[volume] fun y => C*(poissonKernel 1 y*|X.empiricalLogPotential y-α|) :=
    ae_of_all _ (fun y => mul_nonneg hC (mul_nonneg (poissonKernel_pos (by norm_num) _).le (abs_nonneg _)))
  have hall := setIntegral_le_integral (s := s) hi hnng
  simp only [integral_const_mul] at hb hall
  exact (abs_integral_le_integral_abs.trans hb).trans
    (hall.trans (mul_le_mul_of_nonneg_left (X.integral_weighted_abs_potential_sub_le hn α) hC))

theorem exterior_density_integrable_and_bound (hn : 0 < n) {a b d x : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1) (α h : ℝ) :
    IntegrableOn (fun y => (X.empiricalLogPotential y-α)/((y-x)^2+h^2)) (Icc a b)ᶜ ∧
      |X.exteriorDensity a b α x h| ≤
        (exteriorKernelBound d/Real.pi^2)*(weightedLogBound+|α|) := by
  have hm : Measurable (fun y => (X.empiricalLogPotential y-α)/((y-x)^2+h^2)) :=
    (X.measurable_empiricalLogPotential.sub_const α).div (by fun_prop)
  have hp := X.exterior_integral_bound hn (α := α) (exteriorKernelBound_pos hd).le
    measurableSet_Icc.compl hm (fun y hy => by
      have hsep := distance_compl_interval hx hy
      have hden : 0 < (y-x)^2+h^2 := by nlinarith [sq_abs (y-x), sq_nonneg h]
      rw [abs_div, abs_of_pos hden]
      have hb := mul_le_mul_of_nonneg_right (exteriorKernel_le_cauchy hd hx1 hsep h)
        (abs_nonneg (X.empiricalLogPotential y-α))
      convert! hb using 1 <;> ring)
  refine ⟨hp.1, ?_⟩
  unfold exteriorDensity
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1/Real.pi^2)]
  have hb := mul_le_mul_of_nonneg_left hp.2 (by positivity : 0 ≤ 1/Real.pi^2)
  convert! hb using 1 <;> ring

theorem exteriorDensity_height_bound (hn : 0 < n) {a b d x : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1) (α h : ℝ) :
    |X.exteriorDensity a b α x h-X.exteriorDensity a b α x 0| ≤
      ((exteriorKernelBound d/Real.pi^2)*(weightedLogBound+|α|)/d^2)*h^2 := by
  let C := (h^2/d^2)*exteriorKernelBound d
  have hC : 0 ≤ C := mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (exteriorKernelBound_pos hd).le
  let g := fun y => (X.empiricalLogPotential y-α)*(1/((y-x)^2+h^2)-1/(y-x)^2)
  have hg : Measurable g := (X.measurable_empiricalLogPotential.sub_const α).mul (by fun_prop)
  have hb := X.exterior_integral_bound hn (α := α) hC measurableSet_Icc.compl hg (fun y hy => by
    have hsep := distance_compl_interval hx hy
    have hk := exteriorKernel_height_difference hd hsep (h := h)
    have hc := exteriorKernel_le_cauchy hd hx1 hsep 0
    simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at hc
    have hnonneg : 0 ≤ h^2/d^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hh := hk.trans (mul_le_mul_of_nonneg_left hc hnonneg)
    have hmul := mul_le_mul_of_nonneg_left hh (abs_nonneg (X.empiricalLogPotential y-α))
    dsimp [g]
    rw [abs_mul]
    convert! hmul using 1 <;> simp only [C] <;> ring)
  have hi := (X.exterior_density_integrable_and_bound hn hd hx hx1 α h).1
  have hi0 := (X.exterior_density_integrable_and_bound hn hd hx hx1 α 0).1
  have he : X.exteriorDensity a b α x h-X.exteriorDensity a b α x 0 =
      -(1/Real.pi^2)*(∫ y in (Icc a b)ᶜ, g y) := by
    unfold exteriorDensity
    rw [← mul_sub, ← integral_sub hi hi0]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    dsimp [g]
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1/Real.pi^2)]
  have hm := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ 1/Real.pi^2)
  convert! hm using 1 <;> simp only [C] <;> ring

theorem exteriorDensity_lipschitz_bound (hn : 0 < n) {a b d x x₀ : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx0 : x₀ ∈ Icc (a+d) (b-d))
    (hx1 : |x| ≤ 1) (hx01 : |x₀| ≤ 1) (α : ℝ) :
    |X.exteriorDensity a b α x 0-X.exteriorDensity a b α x₀ 0| ≤
      (2*exteriorKernelBound d/Real.pi^2*(weightedLogBound+|α|)/d)*|x-x₀| := by
  let C := (|x-x₀|/d)*(2*exteriorKernelBound d)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg (abs_nonneg _) hd.le)
      (mul_nonneg (by norm_num) (exteriorKernelBound_pos hd).le)
  let g := fun y => (X.empiricalLogPotential y-α)*(1/(y-x)^2-1/(y-x₀)^2)
  have hg : Measurable g := (X.measurable_empiricalLogPotential.sub_const α).mul (by fun_prop)
  have hb := X.exterior_integral_bound hn (α := α) hC measurableSet_Icc.compl hg (fun y hy => by
    have hs := distance_compl_interval hx hy
    have ht := distance_compl_interval hx0 hy
    have hk := exteriorKernel_horizontal_difference hd hs ht
    have h1 := exteriorKernel_le_cauchy hd hx1 hs 0
    have h2 := exteriorKernel_le_cauchy hd hx01 ht 0
    simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at h1 h2
    have he : |(y-x)-(y-x₀)| = |x-x₀| := by
      rw [show (y-x)-(y-x₀) = -(x-x₀) by ring, abs_neg]
    rw [he] at hk
    have hsum := add_le_add h1 h2
    have hprod := mul_le_mul_of_nonneg_left hsum (div_nonneg (abs_nonneg (x-x₀)) hd.le)
    have hmul := mul_le_mul_of_nonneg_left (hk.trans hprod)
      (abs_nonneg (X.empiricalLogPotential y-α))
    dsimp [g]
    rw [abs_mul]
    convert! hmul using 1 <;> simp only [C] <;> ring)
  have hi := (X.exterior_density_integrable_and_bound hn hd hx hx1 α 0).1
  have hi0 := (X.exterior_density_integrable_and_bound hn hd hx0 hx01 α 0).1
  have he : X.exteriorDensity a b α x 0-X.exteriorDensity a b α x₀ 0 =
      -(1/Real.pi^2)*(∫ y in (Icc a b)ᶜ, g y) := by
    unfold exteriorDensity
    rw [← mul_sub, ← integral_sub hi hi0]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    dsimp [g]
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1/Real.pi^2)]
  have hm := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ 1/Real.pi^2)
  convert! hm using 1 <;> simp only [C] <;> ring

end Erdos1132.Nodes
