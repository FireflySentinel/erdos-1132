import Erdos1132.Additive.WeightedLipschitz
import Erdos1132.Additive.QuadratureRate
import Erdos1132.Additive.DensityPositive
import Mathlib.Topology.Order.ProjIcc

/-! # Quadrature for the actual squared weight divided by the local density

Paper: §3, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace Erdos1132

theorem eventually_weighted_square_quadrature (X : ∀ n, Nodes n)
    {a b d l r M L : ℝ} (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hd : 0 < d) (hlr : l ≤ r) (hJ : Icc l r ⊆ Icc (a+d) (b-d))
    (hM : 0 ≤ M) (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Measurable f)
    (hMf : ∀ x, |f x| ≤ M) (hlip : ∀ x y, |f x-f y| ≤ L*|x-y|)
    (hsupp : ∀ x, x ∉ Icc l r → f x = 0)
    (hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      |(∑ i, (f ((X n).point i))^2/
        (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)/(n : ℝ)-
        (∫ x, (f x)^2)| ≤ C/quarterRoot n := by
  obtain ⟨c, hc, hpos⟩ := eventually_exterior_density_positive X hab hI hd hΛ
  obtain ⟨D, hD, hDb⟩ := uniform_exterior_density_bounds hab hI hd
  obtain ⟨C, hC, hq⟩ := uniform_local_quadrature_rate (M := M^2/c)
    (L := 2*M*L/c+M^2*D/c^2) hab hI hd hlr hJ (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hΛ, hpos, eventually_gt_atTop (0:ℕ)] with n hnΛ hnp hn
  let ρ (x : ℝ) := (X n).exteriorDensity a b (X n).potentialNormalization x 0
  let R (x : ℝ) := ρ (projIcc l r hlr x)
  have hRm : Measurable R :=
    ((X n).measurable_exteriorDensity a b (X n).potentialNormalization 0).comp
      (continuous_subtype_val.comp continuous_projIcc).measurable
  have hRpos (x : ℝ) : c ≤ R x := hnp _ (hJ (projIcc l r hlr x).property)
  have hRlip (x y : ℝ) : |R x-R y| ≤ D*|x-y| := by
    exact ((hDb n (X n) hn hnΛ).2 _ (hJ (projIcc l r hlr x).property)
      _ (hJ (projIcc l r hlr y).property)).trans
        (mul_le_mul_of_nonneg_left (abs_projIcc_sub_le hlr x y) hD.le)
  let g (x : ℝ) := (f x)^2/R x
  have hgm : Measurable g := (hf.pow_const 2).div hRm
  have hgb (x : ℝ) : |g x| ≤ M^2/c := square_div_bound hc (hRpos x) hM (hMf x)
  have hgl (x y : ℝ) : |g x-g y| ≤ (2*M*L/c+M^2*D/c^2)*|x-y| :=
    square_div_lipschitz hM hL hc hD.le hMf hRpos hlip hRlip x y
  have hgs (x : ℝ) (hx : x ∉ Icc l r) : g x = 0 := by simp [g, hsupp x hx]
  have hR_eq (x : ℝ) (hx : x ∈ Icc l r) : R x = ρ x := by
    simp only [R, projIcc_of_mem hlr hx]
  have hg_eq (x : ℝ) : g x = (f x)^2/ρ x := by
    by_cases hx : x ∈ Icc l r
    · dsimp only [g]; rw [hR_eq x hx]
    · simp [hgs x hx, hsupp x hx]
  have hint (x : ℝ) : ρ x*g x = (f x)^2 := by
    by_cases hx : x ∈ Icc l r
    · rw [hg_eq]
      have hρ : ρ x ≠ 0 := (hc.trans_le (hnp x (hJ hx))).ne'
      field_simp
    · rw [hgs x hx, hsupp x hx]; ring
  have h := hq n (X n) hn hnΛ g hgm hgb hgl hgs
  change |(∑ i, g ((X n).point i))/(n : ℝ)-(∫ x, ρ x*g x)| ≤ _ at h
  simp_rw [hint] at h
  simpa only [hg_eq] using h

end Erdos1132
