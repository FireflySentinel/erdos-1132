import Erdos1132.PoissonPotential
import Erdos1132.LocalPoissonEstimate

/-! # Uniform Cauchy-weighted integrability of the boundary potential -/

noncomputable section
open MeasureTheory Set Filter Finset Real Complex
open scoped BigOperators
namespace Erdos1132

def weightedLogBound : ℝ := Real.log 2+(4+logSquareBound)/Real.pi

theorem weightedLogBound_nonneg : 0 ≤ weightedLogBound := by
  unfold weightedLogBound
  exact add_nonneg (Real.log_nonneg (by norm_num))
    (div_nonneg (by linarith [logSquareBound_nonneg]) Real.pi_pos.le)

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem empiricalLogPotential_nonpos_outside {y : ℝ} (hy : y ∉ Set.Icc (-2) 2) :
    X.empiricalLogPotential y ≤ 0 := by
  have hd (i : Fin n) : 1 ≤ |y-X.point i| := by
    have hi := X.mem_interval i
    rcases lt_or_gt_of_ne (show y ≠ 0 by intro he; simp [he] at hy) with hneg | hpos
    · have hy2 : y < -2 := by
        by_contra he
        exact hy ⟨le_of_not_gt he, by linarith⟩
      rw [abs_of_neg (by linarith [hi.1] : y-X.point i < 0)]
      linarith [hi.1]
    · have hy2 : 2 < y := by
        by_contra he
        exact hy ⟨by linarith, le_of_not_gt he⟩
      exact (by linarith [hi.2] : 1 ≤ y-X.point i).trans (le_abs_self _)
  unfold empiricalLogPotential
  apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg _)
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro i _
  rw [← Real.log_abs]
  exact Real.log_nonneg (hd i)

theorem complexLogPotential_zero_one_bounds (hn : 0 < n) :
    -Real.log 2 ≤ X.complexLogPotential 0 1 ∧ X.complexLogPotential 0 1 ≤ 0 := by
  have hnorm (i : Fin n) : 1 ≤ ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖ ∧
      ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖ ≤ 2 := by
    have hi := X.mem_interval i
    have hs : (X.point i)^2 ≤ 1 := by nlinarith [hi.1, hi.2]
    have he : ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖^2 = (X.point i)^2+1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, pow_two]
    constructor <;> nlinarith [norm_nonneg (((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I),
      sq_nonneg (X.point i)]
  have hsumlo : 0 ≤ ∑ i, Real.log ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖ :=
    Finset.sum_nonneg (fun i _ => Real.log_nonneg (hnorm i).1)
  have hsumhi : (∑ i, Real.log ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖) ≤ n*Real.log 2 := by
    calc
      _ ≤ ∑ _i : Fin n, Real.log 2 := Finset.sum_le_sum
        (fun i _ => Real.log_le_log (lt_of_lt_of_le zero_lt_one (hnorm i).1) (hnorm i).2)
      _ = _ := by simp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold complexLogPotential
  constructor
  · apply (le_div_iff₀ hnR).mpr
    nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsumlo) hnR.le

theorem integrable_weighted_abs_potential :
    Integrable (fun y => poissonKernel 1 y * |X.empiricalLogPotential y|) := by
  have hi := (X.integrable_poisson_empiricalLogPotential (by norm_num : (0 : ℝ) < 1) 0).abs
  simpa only [sub_zero, abs_mul, abs_of_pos (poissonKernel_pos (by norm_num : (0 : ℝ) < 1) _)] using hi

/-- A bound for the full real-line integral, including the logarithmic tails. -/
theorem integral_weighted_abs_potential_le (hn : 0 < n) :
    (∫ y, poissonKernel 1 y * |X.empiricalLogPotential y|) ≤ weightedLogBound := by
  let J := Set.Icc (-2 : ℝ) 2
  let g := fun y => poissonKernel 1 y * |X.empiricalLogPotential y|
  have hg : Integrable g := X.integrable_weighted_abs_potential
  have hJ : MeasurableSet J := measurableSet_Icc
  have hp : Integrable (fun y => poissonKernel 1 y * X.empiricalLogPotential y) := by
    simpa only [sub_zero] using X.integrable_poisson_empiricalLogPotential (by norm_num) 0
  have hid (y : ℝ) : g y ≤ -(poissonKernel 1 y * X.empiricalLogPotential y) +
      2*J.indicator g y := by
    by_cases hy : y ∈ J
    · rw [Set.indicator_of_mem hy]
      have hw : 0 ≤ poissonKernel 1 y := (poissonKernel_pos (by norm_num) _).le
      have hle := mul_le_mul_of_nonneg_left (le_abs_self (X.empiricalLogPotential y)) hw
      dsimp [g]
      linarith
    · rw [Set.indicator_of_notMem hy]
      dsimp [g]
      rw [abs_of_nonpos (X.empiricalLogPotential_nonpos_outside hy)]
      ring_nf
      exact le_rfl
  have hbound := integral_mono hg (hp.neg.add ((hg.indicator hJ).const_mul 2)) hid
  simp only [Pi.add_apply, Pi.neg_apply] at hbound
  have hpneg : Integrable (fun y => -(poissonKernel 1 y * X.empiricalLogPotential y)) := hp.neg
  rw [integral_add hpneg ((hg.indicator hJ).const_mul 2), integral_neg,
    integral_const_mul, integral_indicator hJ] at hbound
  have he := X.poisson_empiricalLogPotential (by norm_num : (0 : ℝ) < 1) 0
  simp only [sub_zero] at he
  rw [he] at hbound
  have hjbound : (∫ y in J, g y) ≤ (4+logSquareBound)/(2*Real.pi) := by
    have hmono : (∫ y in J, g y) ≤ ∫ y in J, (1/Real.pi)*|X.empiricalLogPotential y| := by
      apply integral_mono hg.integrableOn
        ((X.integrableOn_empiricalLogPotential (-2) 2).abs.const_mul _)
      intro y
      have hk := poissonKernel_le_inv_height (by norm_num : (0 : ℝ) < 1) y
      simp only [mul_one] at hk
      exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    rw [integral_const_mul] at hmono
    have hb := mul_le_mul_of_nonneg_left (X.integral_abs_empiricalLogPotential_le hn)
      (by positivity : 0 ≤ 1/Real.pi)
    calc
      _ ≤ (1/Real.pi)*((4+logSquareBound)/2) := hmono.trans hb
      _ = _ := by ring
  have hzero := X.complexLogPotential_zero_one_bounds hn
  unfold weightedLogBound
  have heq : 2*((4+logSquareBound)/(2*Real.pi)) = (4+logSquareBound)/Real.pi := by ring
  linarith

theorem integrable_weighted_abs_potential_sub (α : ℝ) :
    Integrable (fun y => poissonKernel 1 y * |X.empiricalLogPotential y-α|) := by
  have hi := (X.integrable_poisson_potential_sub (by norm_num : (0 : ℝ) < 1) 0 α).abs
  simpa only [sub_zero, abs_mul,
    abs_of_pos (poissonKernel_pos (by norm_num : (0 : ℝ) < 1) _)] using hi

/-- The same weighted estimate after subtracting any real constant. -/
theorem integral_weighted_abs_potential_sub_le (hn : 0 < n) (α : ℝ) :
    (∫ y, poissonKernel 1 y * |X.empiricalLogPotential y-α|) ≤ weightedLogBound+|α| := by
  have hi := (X.integrable_poisson_potential_sub (by norm_num : (0 : ℝ) < 1) 0 α).abs
  simp only [sub_zero, abs_mul,
    abs_of_pos (poissonKernel_pos (by norm_num : (0 : ℝ) < 1) _)] at hi
  have hright := X.integrable_weighted_abs_potential.add
    ((integrable_poissonKernel (by norm_num : (0 : ℝ) ≤ 1)).mul_const |α|)
  have hb := integral_mono hi hright (fun y => by
    change poissonKernel 1 y * |X.empiricalLogPotential y-α| ≤
      poissonKernel 1 y * |X.empiricalLogPotential y| + poissonKernel 1 y * |α|
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (poissonKernel_pos (by norm_num) _).le)
  simp only [Pi.add_apply] at hb
  rw [integral_add X.integrable_weighted_abs_potential
    ((integrable_poissonKernel (by norm_num : (0 : ℝ) ≤ 1)).mul_const |α|),
    integral_mul_const, integral_poissonKernel (by norm_num : (0 : ℝ) < 1), one_mul] at hb
  exact hb.trans (add_le_add_left (X.integral_weighted_abs_potential_le hn) _)

end Nodes
end Erdos1132
