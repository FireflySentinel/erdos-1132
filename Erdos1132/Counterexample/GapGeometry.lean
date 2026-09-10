import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# The smooth distance inside one gap

Section 7.2 uses `r(x) = (x-b)(c-x)/(c-b)` on a complementary interval.
These lemmas prove its comparison with the distance to the two endpoints,
its size bound, and its Lipschitz estimate on the closed gap.

Companion note: §2.2, the logarithmic integral estimate.
-/

noncomputable section

open Set

namespace Erdos1132.Counterexample

def gapRadius (b c x : ℝ) : ℝ := (x - b) * (c - x) / (c - b)

def gapDistance (b c x : ℝ) : ℝ := min (x - b) (c - x)

@[simp] theorem gapRadius_left (b c : ℝ) : gapRadius b c b = 0 := by
  simp [gapRadius]

@[simp] theorem gapRadius_right (b c : ℝ) : gapRadius b c c = 0 := by
  simp [gapRadius]

theorem gapRadius_pos {b c x : ℝ} (hx : x ∈ Ioo b c) :
    0 < gapRadius b c x := by
  unfold gapRadius
  exact div_pos (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
    (sub_pos.mpr (hx.1.trans hx.2))

theorem gapRadius_nonneg {b c x : ℝ} (hbc : b < c) (hx : x ∈ Icc b c) :
    0 ≤ gapRadius b c x := by
  unfold gapRadius
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
    (sub_pos.mpr hbc).le

/-- The first inequality in (7.5), on a single closed gap. -/
theorem gapRadius_le_distance {b c x : ℝ} (hbc : b < c) (_hx : x ∈ Icc b c) :
    gapRadius b c x ≤ gapDistance b c x := by
  unfold gapRadius gapDistance
  apply le_min
  · rw [div_le_iff₀ (sub_pos.mpr hbc)]
    nlinarith [sq_nonneg (x - b)]
  · rw [div_le_iff₀ (sub_pos.mpr hbc)]
    nlinarith [sq_nonneg (c - x)]

/-- The second inequality in (7.5), on a single closed gap. -/
theorem gapDistance_le_twice_radius {b c x : ℝ} (hbc : b < c) (hx : x ∈ Icc b c) :
    gapDistance b c x ≤ 2 * gapRadius b c x := by
  unfold gapDistance gapRadius
  rw [← mul_div_assoc, le_div_iff₀ (sub_pos.mpr hbc)]
  by_cases h : x - b ≤ c - x
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr (le_of_not_ge h))]

theorem gapRadius_le_quarter_length {b c x : ℝ} (hbc : b < c) :
    gapRadius b c x ≤ (c - b) / 4 := by
  unfold gapRadius
  rw [div_le_iff₀ (sub_pos.mpr hbc)]
  nlinarith [sq_nonneg (2 * x - b - c)]

theorem hasDerivAt_gapRadius (b c x : ℝ) :
    HasDerivAt (gapRadius b c) ((b + c - 2 * x) / (c - b)) x := by
  convert! (((hasDerivAt_id x).sub_const b).mul
    ((hasDerivAt_const x c).sub (hasDerivAt_id x))).div_const (c - b) using 1
  dsimp [gapRadius]
  ring

theorem gapRadius_derivative_bound {b c x : ℝ} (hbc : b < c) (hx : x ∈ Icc b c) :
    |(b + c - 2 * x) / (c - b)| ≤ 1 := by
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ (sub_pos.mpr hbc)]
    linarith [hx.2]
  · rw [div_le_iff₀ (sub_pos.mpr hbc)]
    linarith [hx.1]

theorem gapRadius_lipschitz {b c x y : ℝ} (hbc : b < c)
    (hx : x ∈ Icc b c) (hy : y ∈ Icc b c) :
    |gapRadius b c x - gapRadius b c y| ≤ |x - y| := by
  have h := (convex_Icc b c).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hasDerivAt_gapRadius b c z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using gapRadius_derivative_bound hbc hz)
    hy hx
  simpa only [Real.norm_eq_abs, one_mul] using h

end Erdos1132.Counterexample
