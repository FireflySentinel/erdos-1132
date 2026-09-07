import Erdos1132.Additive.RieszRadius
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Vanishing errors in the local differentiation estimates

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace Erdos1132

theorem tendsto_pow_mul_exp_neg_half (k : ℕ) :
    Tendsto (fun t : ℝ => t^k*Real.exp (-t/2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t/2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have he := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).const_mul ((2 : ℝ)^k)
  simp only [mul_zero, Function.comp_apply] at he
  convert he using 1
  funext t
  simp only [div_pow]
  have htwo : (2 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show -(t/2) = -t/2 by ring]
  field_simp

theorem tendsto_pow_mul_exp_neg_square_half (k : ℕ) :
    Tendsto (fun t : ℝ => t^k*Real.exp (-t^2/2)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_pow_mul_exp_neg_half k)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (pow_nonneg (by linarith) _)
    nlinarith

theorem localRectangleLoss_nonneg {l r : ℝ} (hlr : l < r) (n : ℕ) :
    0 ≤ localRectangleLoss l r n := by unfold localRectangleLoss; positivity

theorem tendsto_localRectangleLoss (l r : ℝ) :
    Tendsto (localRectangleLoss l r) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_mul_exp_neg_square_half 16).comp tendsto_eighthRoot).const_mul
    (4*(2+4/(r-l)))
  simp only [mul_zero, Function.comp_apply] at ht
  convert ht using 1
  funext n
  have he := eighthRoot_pow_eight (Nat.cast_nonneg n)
  unfold localRectangleLoss
  have hp : (n : ℝ)^2 = (eighthRoot n)^16 := by
    calc
      (n : ℝ)^2 = ((eighthRoot n)^8)^2 := congrArg (fun y : ℝ => y^2) he.symm
      _ = _ := by ring
  rw [hp]
  ring

theorem tendsto_n_mul_localRectangleLoss (l r : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)*localRectangleLoss l r n) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_mul_exp_neg_square_half 24).comp tendsto_eighthRoot).const_mul
    (4*(2+4/(r-l)))
  simp only [mul_zero, Function.comp_apply] at ht
  convert ht using 1
  funext n
  let t := eighthRoot (n : ℝ)
  have he : t^8 = (n : ℝ) := eighthRoot_pow_eight (Nat.cast_nonneg n)
  change (n : ℝ)*(4*((2+4/(r-l))*(n : ℝ)^2)*Real.exp (-t^2/2)) = _
  have hp : (n : ℝ)*(n : ℝ)^2 = t^24 := by rw [← he]; ring
  calc
    _ = (4*(2+4/(r-l)))*((n : ℝ)*(n : ℝ)^2)*Real.exp (-t^2/2) := by ring
    _ = _ := by rw [hp]; ring

theorem tendsto_n_mul_exp_loss_sub_one {l r : ℝ} (hlr : l < r) :
    Tendsto (fun n : ℕ => (n : ℝ)*(Real.exp (localRectangleLoss l r n)-1)) atTop (𝓝 0) := by
  have ht := (tendsto_n_mul_localRectangleLoss l r).const_mul 2
  simp only [mul_zero, Function.comp_apply] at ht
  apply squeeze_zero' _ _ ht
  · exact Filter.Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg n)
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (localRectangleLoss_nonneg hlr n))))
  · filter_upwards [(tendsto_localRectangleLoss l r).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    have hd := localRectangleLoss_nonneg hlr n
    have he := Real.abs_exp_sub_one_le (x := localRectangleLoss l r n) (by simpa only [abs_of_nonneg hd] using hn.le)
    rw [abs_of_nonneg hd] at he
    have hb := (le_abs_self (Real.exp (localRectangleLoss l r n)-1)).trans he
    have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n (α := ℝ))
    nlinarith

theorem tendsto_inv_eighthRoot_nat :
    Tendsto (fun n : ℕ => 1/eighthRoot n) atTop (𝓝 0) :=
  tendsto_eighthRoot.const_div_atTop 1

theorem tendsto_log_div_eighthRoot_nat :
    Tendsto (fun n : ℕ => Real.log n/eighthRoot n) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => Real.log t/t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have he := (ht.comp tendsto_eighthRoot).const_mul 8
  simp only [mul_zero, Function.comp_apply] at he
  apply he.congr
  intro n
  have hpow := eighthRoot_pow_eight (Nat.cast_nonneg n)
  have hl : Real.log n = 8*Real.log (eighthRoot n) := by
    calc
      Real.log n = Real.log ((eighthRoot n)^8) := congrArg Real.log hpow.symm
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [hl]
  ring

theorem tendsto_log_affine_div_eighthRoot (a b : ℝ) :
    Tendsto (fun n : ℕ => (a*Real.log n+b)/eighthRoot n) atTop (𝓝 0) := by
  have ht := (tendsto_log_div_eighthRoot_nat.const_mul a).add
    (tendsto_inv_eighthRoot_nat.const_mul b)
  simp only [mul_zero, add_zero] at ht
  convert ht using 1
  funext n
  ring

theorem tendsto_log_affine_div_eighthRoot_sq (a b : ℝ) :
    Tendsto (fun n : ℕ => (a*Real.log n+b)/(eighthRoot n)^2) atTop (𝓝 0) := by
  have ht := (tendsto_log_affine_div_eighthRoot a b).mul tendsto_inv_eighthRoot_nat
  simp only [mul_zero, Function.comp_apply] at ht
  convert ht using 1
  funext n
  simp only [pow_two, div_eq_mul_inv, mul_inv_rev]
  ring

end Erdos1132
