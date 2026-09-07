import Erdos1132.WeightedQuadrature

/-! # An explicit nonzero Lipschitz weight on any compact interval -/

noncomputable section
open Set MeasureTheory Real
namespace Erdos1132

def intervalWeight (l r x : ℝ) : ℝ := max 0 (min (x-l) (r-x))

theorem continuous_intervalWeight (l r : ℝ) : Continuous (intervalWeight l r) := by
  unfold intervalWeight
  fun_prop

theorem intervalWeight_nonneg (l r x : ℝ) : 0 ≤ intervalWeight l r x := le_max_left _ _

theorem intervalWeight_zero_off {l r x : ℝ} (hx : x ∉ Icc l r) : intervalWeight l r x = 0 := by
  unfold intervalWeight
  apply max_eq_left
  by_cases hxl : l ≤ x
  · have hxr : r < x := lt_of_not_ge (fun h => hx ⟨hxl, h⟩)
    exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

theorem intervalWeight_bound {l r : ℝ} (hlr : l ≤ r) (x : ℝ) : intervalWeight l r x ≤ r-l := by
  by_cases hx : x ∈ Icc l r
  · apply max_le (by linarith)
    exact (min_le_left _ _).trans (by linarith [hx.2])
  · rw [intervalWeight_zero_off hx]; linarith

theorem intervalWeight_lipschitz (l r x y : ℝ) :
    |intervalWeight l r x-intervalWeight l r y| ≤ |x-y| := by
  have hmin := abs_min_sub_min_le_max (x-l) (r-x) (y-l) (r-y)
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min (x-l) (r-x)) 0 (min (y-l) (r-y))
  have he1 : (x-l)-(y-l) = x-y := by ring
  have he2 : (r-x)-(r-y) = -(x-y) := by ring
  rw [he1, he2, abs_neg, max_self] at hmin
  simp only [sub_self, abs_zero] at hmax
  rw [max_eq_right (abs_nonneg (min (x-l) (r-x)-min (y-l) (r-y)))] at hmax
  exact hmax.trans hmin

theorem hasCompactSupport_intervalWeight (l r : ℝ) : HasCompactSupport (intervalWeight l r) :=
  HasCompactSupport.intro isCompact_Icc (fun x hx => intervalWeight_zero_off hx)

theorem integrable_intervalWeight (l r : ℝ) : Integrable (intervalWeight l r) :=
  (continuous_intervalWeight l r).integrable_of_hasCompactSupport (hasCompactSupport_intervalWeight l r)

theorem integral_intervalWeight_sq_pos {l r : ℝ} (hlr : l < r) :
    0 < ∫ x, (intervalWeight l r x)^2 := by
  have hcomp : HasCompactSupport (fun x => (intervalWeight l r x)^2) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by rw [intervalWeight_zero_off hx]; norm_num)
  have hm : intervalWeight l r ((l+r)/2) = (r-l)/2 := by
    have h1 : (l+r)/2-l = (r-l)/2 := by ring
    have h2 : r-(l+r)/2 = (r-l)/2 := by ring
    rw [intervalWeight, h1, h2, min_self, max_eq_right (by linarith)]
  exact ((continuous_intervalWeight l r).pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (l+r)/2) hcomp (fun x => sq_nonneg _) (by
      change (intervalWeight l r ((l+r)/2))^2 ≠ 0
      rw [hm]; positivity)

end Erdos1132
