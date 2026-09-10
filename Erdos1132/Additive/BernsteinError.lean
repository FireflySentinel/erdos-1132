import Erdos1132.Additive.BernsteinLimits

/-! # Additive error control for logarithmic upper levels

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace Erdos1132

def logarithmicLevel (a b : ℝ) (n : ℕ) : ℝ := a*Real.log n+b

def localDerivativeMultiplier (l r c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (localRectangleLoss l r n)*(1+1/(c*eighthRoot n))*(1+32/(eighthRoot n)^2)

theorem tendsto_logarithmicLevel_div_nat (a b : ℝ) :
    Tendsto (fun n : ℕ => logarithmicLevel a b n/n) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h1 := (ht.comp tendsto_natCast_atTop_atTop).const_mul a
  have h2 := (tendsto_natCast_atTop_atTop.const_div_atTop b :
    Tendsto (fun n : ℕ => b/(n : ℝ)) atTop (𝓝 0))
  have h := h1.add h2
  simp only [mul_zero, add_zero, Function.comp_apply] at h
  convert h using 1
  funext n
  dsimp [logarithmicLevel]
  ring

theorem tendsto_level_mul_exp_loss_sub_one {l r : ℝ} (hlr : l < r) (a b : ℝ) :
    Tendsto (fun n => logarithmicLevel a b n*(Real.exp (localRectangleLoss l r n)-1)) atTop (𝓝 0) := by
  have ht := (tendsto_logarithmicLevel_div_nat a b).mul (tendsto_n_mul_exp_loss_sub_one hlr)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

theorem tendsto_localDerivativeMultiplier_error {l r c : ℝ} (hlr : l < r) (hc : 0 < c)
    (a b : ℝ) :
    Tendsto (fun n => logarithmicLevel a b n*(localDerivativeMultiplier l r c n-1)) atTop (𝓝 0) := by
  have hbc : Tendsto (fun n : ℕ => 1/(c*eighthRoot n)) atTop (𝓝 0) := by
    have ht := tendsto_inv_eighthRoot_nat.const_mul (1/c)
    simp only [mul_zero] at ht
    convert ht using 1
    funext n
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hdc : Tendsto (fun n : ℕ => 32/(eighthRoot n)^2) atTop (𝓝 0) := by
    have ht := (tendsto_inv_eighthRoot_nat.pow 2).const_mul 32
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at ht
    convert ht using 1
    funext n
    simp only [div_pow, one_pow, mul_one_div]
  have h1 := ((tendsto_level_mul_exp_loss_sub_one hlr a b).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add hbc)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hdc)
  have h2 : Tendsto (fun n => logarithmicLevel a b n/(c*eighthRoot n)) atTop (𝓝 0) := by
    have ht := (tendsto_log_affine_div_eighthRoot a b).div_const c
    simp only [zero_div] at ht
    convert ht using 1
    funext n
    dsimp [logarithmicLevel]
    ring
  have h3 := (tendsto_log_affine_div_eighthRoot_sq a b).const_mul 32
  have hsum := (h1.add (h2.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hdc))).add h3
  simp only [zero_mul, mul_zero, zero_add] at hsum
  convert hsum using 1
  funext n
  dsimp [localDerivativeMultiplier, logarithmicLevel]
  ring

theorem tendsto_level_exp_loss_div_root_sq {l r : ℝ} (hlr : l < r) (a b : ℝ) :
    Tendsto (fun n => logarithmicLevel a b n*Real.exp (localRectangleLoss l r n)/(eighthRoot n)^2)
      atTop (𝓝 0) := by
  have ht := (tendsto_log_affine_div_eighthRoot_sq a b).mul
    (Real.continuous_exp.tendsto 0 |>.comp (tendsto_localRectangleLoss l r))
  simp only [zero_mul] at ht
  convert ht using 1
  funext n
  dsimp [logarithmicLevel]
  ring

theorem eventually_logarithmicLevel_bounds {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 1 ≤ logarithmicLevel a b n ∧ logarithmicLevel a b n ≤ n := by
  have hinf : Tendsto (logarithmicLevel a b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha)
  have hratio := (tendsto_logarithmicLevel_div_nat a b).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1, hinf.eventually (eventually_ge_atTop 1), hratio]
    with n hn hlevel hratio
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  refine ⟨hn0, hlevel, ?_⟩
  exact ((div_lt_one hnR).mp hratio).le

end Erdos1132
