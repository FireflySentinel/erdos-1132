import Erdos1132.Additive.InterpolantLocalGrowth

/-! # Choosing the finite Riesz contour inside the local growth rectangle

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace Erdos1132

def localRieszIndex (n : ℕ) : ℕ := ⌊(eighthRoot n)^2⌋₊

theorem floor_square_bounds {t : ℝ} (ht : 2 ≤ t) :
    1 ≤ ⌊t^2⌋₊ ∧ (⌊t^2⌋₊ : ℝ) ≤ t^2 ∧ t^2/2 ≤ (⌊t^2⌋₊ : ℝ) := by
  have hu := Nat.floor_le (sq_nonneg t)
  have hl := Nat.lt_floor_add_one (t^2)
  have ht2 : 4 ≤ t^2 := by nlinarith
  have hn : (1 : ℝ) ≤ ⌊t^2⌋₊ := by linarith
  refine ⟨by exact_mod_cast hn, hu, ?_⟩
  linarith

theorem riesz_radius_bounds {t c ω : ℝ} (ht : 2 ≤ t) (hc : 0 < c)
    (hct : 2 ≤ c*t^2) (hω : Real.pi*c*t^8 ≤ ω) :
    0 < ω ∧ (⌊t^2⌋₊ : ℝ)*Real.pi ≤ ω*((1/t^2)/2) ∧
      (⌊t^2⌋₊ : ℝ)*Real.pi ≤ ω*(1/t^4) ∧
      16/((⌊t^2⌋₊ : ℝ)*Real.pi) ≤ 32/t^2 := by
  have ht0 : 0 < t := by linarith
  have hm := floor_square_bounds ht
  have hm0 : (0 : ℝ) < ⌊t^2⌋₊ := by exact_mod_cast (show 0 < ⌊t^2⌋₊ by omega)
  have hω0 : 0 < ω := (by positivity : 0 < Real.pi*c*t^8).trans_le hω
  have ht2 : 1 ≤ t^2 := by nlinarith
  have ht4 : 1 ≤ t^4 := by nlinarith [sq_nonneg (t^2)]
  have hch : t^2 ≤ c*t^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hct) (sq_nonneg t)]
  have hcr : 2*t^2 ≤ c*t^6 := by
    have hm := mul_le_mul_of_nonneg_left ht4 (show 0 ≤ c*t^2 by positivity)
    nlinarith
  have hr' : t^2 ≤ c*t^8*((1/t^2)/2) := by
    have he : c*t^8*((1/t^2)/2) = c*t^6/2 := by field_simp
    rw [he]
    linarith
  have hh' : t^2 ≤ c*t^8*(1/t^4) := by
    have he : c*t^8*(1/t^4) = c*t^4 := by field_simp
    rwa [he]
  refine ⟨hω0, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hr' Real.pi_pos.le
    have h2 := mul_le_mul_of_nonneg_right hω (show 0 ≤ (1/t^2)/2 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hm.2.1 Real.pi_pos.le
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hh' Real.pi_pos.le
    have h2 := mul_le_mul_of_nonneg_right hω (show 0 ≤ 1/t^4 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hm.2.1 Real.pi_pos.le
    nlinarith
  · have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hden : t^2/2 ≤ (⌊t^2⌋₊ : ℝ)*Real.pi := by nlinarith [hm.2.2]
    have hd := one_div_le_one_div_of_le (show 0 < t^2/2 by positivity) hden
    have hmul := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 16)
    convert! hmul using 1 <;> field_simp <;> ring

theorem eventually_riesz_radius {l r c : ℝ} (hc : 0 < c) :
    ∀ᶠ (n : ℕ) in atTop, ∀ (X : Nodes n) (x : ℝ),
      c ≤ X.exteriorDensity l r X.potentialNormalization x 0 →
      1 ≤ localRieszIndex n ∧ 0 < localFrequency X l r x ∧
      (localRieszIndex n : ℝ)*Real.pi ≤ localFrequency X l r x*((1/(eighthRoot n)^2)/2) ∧
      (localRieszIndex n : ℝ)*Real.pi ≤ localFrequency X l r x*(1/(eighthRoot n)^4) ∧
      16/((localRieszIndex n : ℝ)*Real.pi) ≤ 32/(eighthRoot n)^2 := by
  filter_upwards [tendsto_eighthRoot.eventually (eventually_ge_atTop (2 : ℝ)),
    tendsto_eighthRoot.eventually (eventually_ge_atTop (2/c+2))] with n ht hlarge
  intro X x hρ
  let t := eighthRoot (n : ℝ)
  have ht0 : 0 < t := by change 2 ≤ t at ht; linarith
  have hct : 2 ≤ c*t^2 := by
    have hm := mul_le_mul_of_nonneg_left hlarge hc.le
    rw [mul_add, mul_div_cancel₀ _ hc.ne'] at hm
    have hs : t ≤ t^2 := by nlinarith
    nlinarith
  have he : t^8 = (n : ℝ) := eighthRoot_pow_eight (Nat.cast_nonneg n)
  have hω : Real.pi*c*t^8 ≤ localFrequency X l r x := by
    have hp := mul_le_mul_of_nonneg_left
      (show c ≤ X.exteriorDensity l r X.potentialNormalization x 0+1/t by linarith [one_div_pos.mpr ht0])
      (show 0 ≤ Real.pi*(n : ℝ) by positivity)
    dsimp [localFrequency]
    rw [he]
    nlinarith
  have hb := riesz_radius_bounds ht hc hct hω
  exact ⟨(floor_square_bounds ht).1, hb⟩

end Erdos1132
