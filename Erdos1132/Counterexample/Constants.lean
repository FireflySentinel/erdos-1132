import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Constants in the logarithmic integral estimate

The real-power contraction and the exponential choice of `ρ` give the
numerical bounds used in Sections 7.2–7.3. The cutoff index and radius
also give the cancellation in the lower estimate on `F`.

Paper: §7.2, the logarithmic integral estimate.
-/

namespace Erdos1132.Counterexample

/-- The concavity bound for the fractional power in (7.11). -/
theorem fractional_power_bound :
    (8 / 7 : ℝ) ^ (1 / 256 : ℝ) ≤ 1 + 1 / 1792 := by
  have h := rpow_one_add_le_one_add_mul_self
    (s := (1 / 7 : ℝ)) (p := (1 / 256 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The contraction factor in (7.11). -/
theorem contraction_factor_bound :
    (254 / 255 : ℝ) * (8 / 7 : ℝ) ^ (1 / 256 : ℝ) ≤ 1 - 1 / 512 := by
  have h := mul_le_mul_of_nonneg_left fractional_power_bound
    (show (0 : ℝ) ≤ 254 / 255 by norm_num)
  linarith

theorem log_five_le_two : Real.log 5 ≤ 2 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 5)).mpr
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at h ⊢
  exact h

/-- The full real-power bound for every `T ≥ 16`. -/
theorem logarithmic_contraction_bound {T : ℝ} (hT : 16 ≤ T) :
    (254 / 255 : ℝ) * (T / (T - Real.log 5)) ^ (1 / 256 : ℝ) ≤
      1 - 1 / 512 := by
  have hden : 0 < T - Real.log 5 := by linarith [log_five_le_two]
  have hbase : T / (T - Real.log 5) ≤ (8 / 7 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith [log_five_le_two]
  have hp := Real.rpow_le_rpow (div_nonneg (by linarith) hden.le)
    hbase (show (0 : ℝ) ≤ 1 / 256 by norm_num)
  exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans contraction_factor_bound

noncomputable def gapScale (A : ℝ) : ℝ := Real.exp (-1024 * (A + 40))

theorem gapScale_le_half {A : ℝ} (hA : 1 < A) : gapScale A ≤ 1 / 2 := by
  have hExp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hρ : gapScale A ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [Real.exp_neg] at hρ
  exact hρ.trans (by simpa only [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hExp)

/-- The explicitly chosen cutoff index in Section 7.3. -/
noncomputable def cutoffIndex (A : ℝ) (j : ℕ) : ℕ :=
  ⌈32 * (A + 1)⌉₊ + 64 * j * (2 * j) ^ 256 + j

noncomputable def cutoffRadius (j : ℕ) : ℝ :=
  Real.exp (8 - (2 * (j : ℝ)) ^ 256)

theorem cutoffRadius_pos (j : ℕ) : 0 < cutoffRadius j := Real.exp_pos _

theorem cutoffRadius_le_two {j : ℕ} (hj : 0 < j) : cutoffRadius j ≤ 2 := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (show (2 : ℝ) ≤ 2 * j by linarith) 256
  norm_num at hp
  have he : cutoffRadius j ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  linarith

/-- The logarithmic tail at the chosen cutoff is bounded by `2(2j)^256`. -/
theorem cutoffRadius_tail_bound (j : ℕ) :
    2 * Real.log (2 / cutoffRadius j) ≤ 2 * (2 * (j : ℝ)) ^ 256 := by
  rw [Real.log_div (by norm_num) (ne_of_gt (cutoffRadius_pos j)),
    cutoffRadius, Real.log_exp]
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

set_option exponentiation.threshold 300 in
/-- The large terms in the cutoff estimate cancel with the stated margin. -/
theorem cutoffIndex_margin (A : ℝ) {j : ℕ} (hj : 0 < j) :
    (A + 1) / (j : ℝ) + 1 / 32 ≤
      (cutoffIndex A j : ℝ) / (32 * j) - 2 * (2 * (j : ℝ)) ^ 256 := by
  have hjr : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hceil := Nat.le_ceil (32 * (A + 1))
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * j)).mpr
  simp only [cutoffIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  rw [show (A + 1) * 32 = 32 * (A + 1) by ring]
  ring_nf at hceil ⊢
  linarith

/-- At `r ≤ ρ/2`, the logarithmic variable used in Section 7.2 is at least 16. -/
theorem gapScale_log_parameter {A r : ℝ} (hA : 1 < A) (hr : 0 < r)
    (hsmall : r ≤ gapScale A / 2) :
    16 ≤ Real.log (Real.exp 8 / r) := by
  have hρ : 0 < gapScale A := Real.exp_pos _
  have hlog := Real.log_le_log hr hsmall
  rw [Real.log_div (ne_of_gt hρ) (by norm_num), gapScale, Real.log_exp] at hlog
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hr), Real.log_exp]
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- The choice of `ρ` makes the lower estimate in (7.12) exceed `A + 2`. -/
theorem gapScale_lower_bound {A r : ℝ} (hA : 1 < A) (hr : 0 < r)
    (hsmall : r ≤ gapScale A / 2) :
    A + 2 < (1 / 512 : ℝ) * Real.log (1 / (4 * r)) - 32 := by
  have hρ : 0 < gapScale A := Real.exp_pos _
  have harg : 1 / (2 * gapScale A) ≤ 1 / (4 * r) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (2 * gapScale A)) harg
  rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
    Real.log_mul (by norm_num) (ne_of_gt hρ), gapScale, Real.log_exp] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

end Erdos1132.Counterexample
