import Erdos1132.Additive.DisjointEnergy
import Erdos1132.Additive.RieszConvolution
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Riesz energy comparison for actual finite atomic measures

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Real Finset
open scoped BigOperators
namespace Erdos1132

def unitClamp (x : ℝ) : ℝ := (projIcc (-1) 1 (by norm_num) x : ℝ)

theorem continuous_unitClamp : Continuous unitClamp := continuous_subtype_val.comp continuous_projIcc

theorem abs_unitClamp_le (x : ℝ) : |unitClamp x| ≤ 1 :=
  abs_le.mpr (projIcc (-1) 1 (by norm_num) x).property

theorem unitClamp_eq {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) : unitClamp x = x := by
  simp only [unitClamp, projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1) hx]

theorem atomic_riesz_energy_comparison {n : ℕ} (x a : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    (ha : ∀ i, |a i| ≤ B) {f : ℝ → ℝ} (hf : Measurable f)
    (hfb : ∀ t, |f t| ≤ B) (hsupp : ∀ t, t ∉ Icc (-1:ℝ) 1 → f t = 0) :
    2*(∑ i, a i*(∫ y, rieszKernel ε (x i-y)*f y)) -
      (∫ t, f t*(∫ y, rieszKernel ε (t-y)*f y)) ≤
      ∑ i, ∑ j, a i*a j*rieszKernel ε (x i-x j) := by
  let μ : Measure (Fin n) := Measure.count
  let ν := volume.restrict (Icc (-1:ℝ) 1)
  have hxm : Measurable x := measurable_of_finite _
  have ham : Measurable a := measurable_of_finite _
  have hc := continuous_unitClamp.measurable
  have hp := riesz_energy_comparison μ ν hxm ham hc hf hB hε hx abs_unitClamp_le ha hfb
  rw [integral_prod _ (integrable_weighted_riesz_pair μ ν hxm ham hc hf hB hε ha hfb),
    integral_prod _ (integrable_weighted_riesz_pair ν ν hc hf hc hf hB hε hfb hfb),
    integral_prod _ (integrable_weighted_riesz_pair μ μ hxm ham hxm ham hB hε ha ha)] at hp
  dsimp only [μ] at hp
  simp only [integral_count] at hp
  have hinner (t : ℝ) : (∫ y, f y*rieszKernel ε (t-unitClamp y) ∂ν) =
      ∫ y, rieszKernel ε (t-y)*f y := by
    change (∫ y in Icc (-1:ℝ) 1, _) = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Icc (-1:ℝ) 1)
      (fun y hy => by rw [hsupp y hy]; ring)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    dsimp only
    rw [unitClamp_eq hy]
    ring
  have hleft : (∑ i, ∫ y, a i*f y*rieszKernel ε (x i-unitClamp y) ∂ν) =
      ∑ i, a i*(∫ y, rieszKernel ε (x i-y)*f y) := by
    apply sum_congr rfl
    intro i hi
    simp_rw [mul_assoc]
    rw [integral_const_mul, hinner]
  have hright : (∫ t, ∫ y, f t*f y*rieszKernel ε (unitClamp t-unitClamp y) ∂ν ∂ν) =
      ∫ t, f t*(∫ y, rieszKernel ε (t-y)*f y) := by
    simp_rw [mul_assoc, integral_const_mul, hinner]
    change (∫ t in Icc (-1:ℝ) 1, _) = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Icc (-1:ℝ) 1)
      (fun t ht => by rw [hsupp t ht]; ring)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [unitClamp_eq ht]
  rw [hleft, hright] at hp
  exact hp

end Erdos1132
