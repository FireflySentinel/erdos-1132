import Erdos1132.Counterexample.ShiftedHarmonic

/-!
# Uniform logarithmic correction for interior phase parameters

A half-step displacement changes each logarithm by at most its relative
size. This gives an explicit error bound independent of the fractional part.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set

namespace Erdos1132.Counterexample

theorem log_le_log_add_relative {x y δ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : y ≤ x + δ) :
    Real.log y ≤ Real.log x + δ/x := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hh
  have hd : y/x - 1 ≤ δ/x := by
    apply (sub_le_iff_le_add).mpr
    rw [← div_self hx.ne', ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hx.le
  linarith

theorem harmonic_log_correction {n m : ℕ} {s t a : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n)
    (ha : 0 < a) (hs : a ≤ s) (hπs : a ≤ Real.pi - s)
    (ht : t ∈ Ioo 0 1) (heq : (n : ℝ)*s/Real.pi + 1/2 = m + t) :
    Real.log m + Real.log ((n-m : ℕ) : ℝ) - Real.log (s*(Real.pi-s)) ≤
      2*Real.log n - 2*Real.log Real.pi + Real.pi/(n*a) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnmR : 0 < ((n-m : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hmn
  have hs0 : 0 < s := ha.trans_le hs
  have hps0 : 0 < Real.pi-s := ha.trans_le hπs
  have hu : 0 < (n : ℝ)*s/Real.pi := div_pos (mul_pos hnR hs0) Real.pi_pos
  have hw : 0 < (n : ℝ)*(Real.pi-s)/Real.pi := div_pos (mul_pos hnR hps0) Real.pi_pos
  have hmle : (m : ℝ) ≤ n*s/Real.pi + 1/2 := by linarith [ht.1]
  have hnmle : ((n-m : ℕ) : ℝ) ≤ n*(Real.pi-s)/Real.pi + 1/2 := by
    rw [Nat.cast_sub hmn.le]
    have hid : (n : ℝ)*(Real.pi-s)/Real.pi = n-n*s/Real.pi := by field_simp
    rw [hid]
    linarith [ht.2]
  have hleft := log_le_log_add_relative hu hmR hmle
  have hright := log_le_log_add_relative hw hnmR hnmle
  have hsumlog : Real.log (n*s/Real.pi) + Real.log (n*(Real.pi-s)/Real.pi) =
      2*Real.log n + Real.log (s*(Real.pi-s)) - 2*Real.log Real.pi := by
    rw [Real.log_div (mul_pos hnR hs0).ne' Real.pi_ne_zero,
      Real.log_div (mul_pos hnR hps0).ne' Real.pi_ne_zero,
      Real.log_mul hnR.ne' hs0.ne', Real.log_mul hnR.ne' hps0.ne',
      Real.log_mul hs0.ne' hps0.ne']
    ring
  have hbase : 0 < (n : ℝ)*a/Real.pi := div_pos (mul_pos hnR ha) Real.pi_pos
  have hle1 : (1/2 : ℝ)/(n*s/Real.pi) ≤ (1/2 : ℝ)/(n*a/Real.pi) := by
    apply div_le_div_of_nonneg_left (by norm_num) hbase
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hnR.le) Real.pi_pos.le
  have hle2 : (1/2 : ℝ)/(n*(Real.pi-s)/Real.pi) ≤ (1/2 : ℝ)/(n*a/Real.pi) := by
    apply div_le_div_of_nonneg_left (by norm_num) hbase
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hπs hnR.le) Real.pi_pos.le
  have htwo : (1/2 : ℝ)/(n*a/Real.pi) + (1/2 : ℝ)/(n*a/Real.pi) = Real.pi/(n*a) := by
    field_simp
    norm_num
  linarith

theorem phase_abs_cos_eq_sin {n m : ℕ} {s t : ℝ}
    (ht : t ∈ Ioo 0 1) (heq : (n : ℝ)*s/Real.pi + 1/2 = m + t) :
    |Real.cos (n*s)| = Real.sin (Real.pi*t) := by
  have hid : (n : ℝ)*s = (Real.pi*t - Real.pi/2) + m*Real.pi := by
    have hh := (div_eq_iff Real.pi_ne_zero).mp (show (n : ℝ)*s/Real.pi = m+t-1/2 by linarith)
    nlinarith [hh]
  rw [hid, Real.cos_add_nat_mul_pi, Real.cos_sub_pi_div_two, abs_mul, abs_pow]
  have hsin : 0 ≤ Real.sin (Real.pi*t) := Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg Real.pi_pos.le ht.1.le, by nlinarith [Real.pi_pos, ht.2]⟩
  simp [abs_of_nonneg hsin]

end Erdos1132.Counterexample
