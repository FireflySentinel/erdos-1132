import Erdos1132.Additive.AveragedPoisson

/-! # Approximation of node averages by differences of complex potentials

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Real Complex
open scoped BigOperators
namespace Erdos1132

theorem averagedPoisson_convolution_bound {h δ M L : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    {f : ℝ → ℝ} (hf : Measurable f) (hM : ∀ t, |f t| ≤ M) (hL : 0 ≤ L)
    (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) (x : ℝ) :
    |(∫ y, averagedPoissonKernel h (y-x)*f y)-f x| ≤ L*δ+8*M*h/(Real.pi*δ) := by
  have hM0 := (abs_nonneg (f 0)).trans (hM 0)
  have hft : Measurable (fun t => f (x-t)) := hf.comp (measurable_const.sub measurable_id)
  have hb := probability_kernel_lipschitz_bound (averagedPoissonKernel_nonneg hh)
    (integrable_averagedPoissonKernel hh) (integral_averagedPoissonKernel hh)
    hft (fun t => hM (x-t)) hL hδ
    (fun t => by simpa only [sub_zero, sub_sub_cancel_left, abs_neg] using hlip (x-t) x)
  simp only [sub_zero] at hb
  have he : (∫ y, averagedPoissonKernel h (y-x)*f y) =
      ∫ t, averagedPoissonKernel h t*f (x-t) := by
    have he := integral_sub_left_eq_self
      (f := fun y => averagedPoissonKernel h (y-x)*f y) volume x
    simp only [sub_sub_cancel_left, averagedPoissonKernel_neg] at he
    exact he.symm
  rw [he]
  have htail := mul_le_mul_of_nonneg_left (averagedPoissonKernel_tail hh hδ)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0)
  have hb' := hb.trans (add_le_add_right htail (L*δ))
  convert! hb' using 1 <;> ring

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem averaged_node_kernel_identity {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∑ i, averagedPoissonKernel h (x-X.point i))/(n : ℝ) =
      (X.complexLogPotential x h-X.complexLogPotential x (2*h))/(Real.pi*h) := by
  simp_rw [averagedPoissonKernel_log hh]
  unfold complexLogPotential
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  ring

theorem integrable_averaged_node_kernel_mul {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    Integrable (fun y =>
      ((X.complexLogPotential y h-X.complexLogPotential y (2*h))/(Real.pi*h))*f y) := by
  have hi (i : Fin n) : Integrable (fun y => averagedPoissonKernel h (y-X.point i)*f y) :=
    ((integrable_averagedPoissonKernel hh).comp_sub_right (X.point i)).mul_bdd
      hf.aestronglyMeasurable (ae_of_all _ hM)
  have hs := (integrable_finsetSum Finset.univ (fun i _ => hi i)).div_const (n : ℝ)
  convert! hs using 1
  ext y
  rw [← X.averaged_node_kernel_identity hh]
  rw [div_mul_eq_mul_div, Finset.sum_mul]

theorem averaged_node_quadrature_bound (hn : 0 < n) {h δ M L : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) {f : ℝ → ℝ} (hf : Measurable f)
    (hM : ∀ y, |f y| ≤ M) (hL : 0 ≤ L) (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) :
    |(∑ i, f (X.point i))/(n : ℝ) -
      ∫ y, ((X.complexLogPotential y h-X.complexLogPotential y (2*h))/(Real.pi*h))*f y| ≤
      L*δ+8*M*h/(Real.pi*δ) := by
  have hi (i : Fin n) : Integrable (fun y => averagedPoissonKernel h (y-X.point i)*f y) :=
    ((integrable_averagedPoissonKernel hh).comp_sub_right (X.point i)).mul_bdd
      hf.aestronglyMeasurable (ae_of_all _ hM)
  have he : (∫ y, ((X.complexLogPotential y h-X.complexLogPotential y (2*h))/(Real.pi*h))*f y) =
      (∑ i, ∫ y, averagedPoissonKernel h (y-X.point i)*f y)/(n : ℝ) := by
    simp_rw [← X.averaged_node_kernel_identity hh, div_mul_eq_mul_div, Finset.sum_mul]
    rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  rw [he, ← sub_div, ← Finset.sum_sub_distrib, abs_div,
    abs_of_pos (by exact_mod_cast hn : 0 < (n : ℝ))]
  apply (div_le_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr
  calc
    _ ≤ ∑ i, |f (X.point i)-(∫ y, averagedPoissonKernel h (y-X.point i)*f y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (L*δ+8*M*h/(Real.pi*δ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_sub_comm]
      exact averagedPoisson_convolution_bound hh hδ hf hM hL hlip (X.point i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Nodes
end Erdos1132
