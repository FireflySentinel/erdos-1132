import Erdos1132.Cancellation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Filter
open scoped Topology

namespace Erdos1132

def rowSize (n : ℕ) : ℝ := n + 2

def height (a : ℝ) (n : ℕ) : ℝ := rowSize n ^ (-a)

theorem rowSize_ge_two (n : ℕ) : 2 ≤ rowSize n := by
  dsimp [rowSize]
  linarith [Nat.cast_nonneg n (α := ℝ)]

theorem rowSize_pos (n : ℕ) : 0 < rowSize n := lt_of_lt_of_le (by norm_num) (rowSize_ge_two n)

theorem tendsto_rowSize : Tendsto rowSize atTop atTop := by
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

theorem height_pos (a : ℝ) (n : ℕ) : 0 < height a n := Real.rpow_pos_of_pos (rowSize_pos n) _

theorem height_le_one {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : height a n ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [rowSize_ge_two n]) (neg_nonpos.mpr ha)

theorem height_lt_one {a : ℝ} (ha : 0 < a) (n : ℕ) : height a n < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith [rowSize_ge_two n]) (neg_neg_of_pos ha)

theorem height_antitone {a b : ℝ} (hab : b < a) (n : ℕ) : height a n < height b n := by
  exact Real.rpow_lt_rpow_of_exponent_lt (by linarith [rowSize_ge_two n]) (neg_lt_neg hab)

theorem tendsto_height {a : ℝ} (ha : 0 < a) : Tendsto (height a) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_rowSize

theorem height_ratio (a b : ℝ) (n : ℕ) : height a n / height b n = height (a - b) n := by
  dsimp [height]
  rw [← Real.rpow_sub (rowSize_pos n)]
  congr 1
  ring

theorem tendsto_height_ratio {a b : ℝ} (hab : b < a) :
    Tendsto (fun n => height a n / height b n) atTop (𝓝 0) := by
  simp_rw [height_ratio]
  exact tendsto_height (sub_pos.mpr hab)

theorem neg_log_height (a : ℝ) (n : ℕ) : -Real.log (height a n) = a * Real.log (rowSize n) := by
  rw [height, Real.log_rpow (rowSize_pos n)]
  ring

theorem rowSize_mul_height (a : ℝ) (n : ℕ) :
    rowSize n * height a n = rowSize n ^ (1 - a) := by
  rw [sub_eq_add_neg, Real.rpow_add (rowSize_pos n), Real.rpow_one]
  rfl

theorem power_exponential_decay {a : ℝ} (ha : a < 1) :
    Tendsto (fun n => rowSize n ^ (2 * a) * Real.exp (-(rowSize n ^ (1 - a)) / 4))
      atTop (𝓝 0) := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_rowSize
  have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 * a / (1 - a)) (1 / 4) (by norm_num)).comp ht
  convert! hl using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul (rowSize_pos n).le,
    mul_div_cancel₀ _ (sub_ne_zero.mpr ha.ne' )]
  congr 2
  ring

theorem exp_div_four_le_sinh {t : ℝ} (ht : 1 ≤ t) : Real.exp t / 4 ≤ Real.sinh t := by
  have he : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hn : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith


/-- A uniform error bound for every row with `n + 2` distinct nodes. -/
def cancellationError (a : ℝ) (n : ℕ) : ℝ :=
  20 * (rowSize n ^ (2 * a) * Real.exp (-(rowSize n ^ (1 - a)) / 4))

theorem tendsto_cancellationError {a : ℝ} (ha : a < 1) :
    Tendsto (cancellationError a) atTop (𝓝 0) := by
  convert! (power_exponential_decay ha).const_mul 20 using 1
  norm_num

theorem cancellationError_nonneg (a : ℝ) (n : ℕ) : 0 ≤ cancellationError a n := by
  exact mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (rowSize_pos n).le _) (Real.exp_pos _).le)

theorem eventually_cancellation_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ n in atTop, ∀ X : Nodes (n + 2), ∀ (x : ℝ), x ∈ Set.Icc (-1) 1 →
      ‖X.signedCauchy ((x : ℂ) + height a n * Complex.I)‖ /
        (X.probability (by omega)).gamma (height a n) x ≤ cancellationError a n := by
  have ht : Tendsto (fun n => rowSize n ^ (1 - a) / 4) atTop atTop :=
    ((tendsto_rpow_atTop (sub_pos.mpr ha1)).comp tendsto_rowSize).atTop_div_const (by norm_num)
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn X x hx
  let h := height a n
  have hh : 0 < h := height_pos a n
  have hh1 : h ≤ 1 := height_le_one ha.le n
  have heq : rowSize n ^ (1 - a) / 4 = rowSize n * h / 4 := by
    rw [rowSize_mul_height]
  have harg : rowSize n ^ (1 - a) / 4 ≤ ((n + 2 - 1 : ℕ) : ℝ) * h / 2 := by
    rw [heq]
    have he : ((n + 2 - 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
    rw [he]
    dsimp [rowSize]
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  have hs := (exp_div_four_le_sinh hn).trans (Real.sinh_le_sinh.mpr harg)
  have hden : 0 < h ^ 2 * (Real.exp (rowSize n ^ (1 - a) / 4) / 4) := by positivity
  have hb := X.cancellation_ratio_bound (by omega) hh hh1 hx
  apply hb.trans
  calc
    (4 + h ^ 2) / (h ^ 2 * Real.sinh (((n + 2 - 1 : ℕ) : ℝ) * h / 2))
      ≤ (4 + h ^ 2) / (h ^ 2 * (Real.exp (rowSize n ^ (1 - a) / 4) / 4)) :=
        div_le_div_of_nonneg_left (by positivity) hden (mul_le_mul_of_nonneg_left hs (sq_nonneg h))
    _ ≤ 5 / (h ^ 2 * (Real.exp (rowSize n ^ (1 - a) / 4) / 4)) :=
      div_le_div_of_nonneg_right (by nlinarith) hden.le
    _ = cancellationError a n := by
      have hp : h ^ 2 = (rowSize n ^ (2 * a))⁻¹ := by
        dsimp only [h, height]
        rw [← Real.rpow_mul_natCast (rowSize_pos n).le,
          show (-a) * (2 : ℕ) = -(2 * a) by norm_num; ring,
          Real.rpow_neg (rowSize_pos n).le]
      rw [hp, cancellationError, show -(rowSize n ^ (1 - a)) / 4 = -(rowSize n ^ (1 - a) / 4) by ring,
        Real.exp_neg]
      field_simp
      ring

end Erdos1132
