import Erdos1132.Shared.PoissonSemigroup

/-! # Harmonic representation of a truncated potential

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped BigOperators

namespace Erdos1132

theorem inverse_quadratic_integral_bound {η d : ℝ} (hη : 0 ≤ η) (hd : d ≠ 0) :
    (∫ s in η..1, 1 / (d ^ 2 + s ^ 2)) ≤ Real.pi / (2 * |d|) := by
  have hd' : 0 < |d| := abs_pos.mpr hd
  have he : (fun s : ℝ => 1 / (d ^ 2 + s ^ 2)) =
      fun s => (Real.pi / |d|) * poissonKernel |d| s := by
    funext s
    unfold poissonKernel
    rw [sq_abs]
    field_simp
    ring
  rw [he, intervalIntegral.integral_const_mul]
  have hi := intervalIntegral_poissonKernel hd' 0 η 1
  simp only [sub_zero] at hi
  rw [hi]
  have h0 : 0 ≤ Real.arctan (η / |d|) := Real.arctan_nonneg.mpr (div_nonneg hη hd'.le)
  have h1 := Real.arctan_lt_pi_div_two (1 / |d|)
  field_simp
  nlinarith [Real.pi_pos]

theorem quadratic_local_comparison {η s x y v : ℝ} (hη : 0 < η) (hs : η ≤ s) :
    1 / ((x - v) ^ 2 + s ^ 2) ≤
      (1 + |x - y| / η) ^ 2 / ((y - v) ^ 2 + s ^ 2) := by
  let z : ℂ := (x - v : ℝ) + s * I
  let w : ℂ := (y - v : ℝ) + s * I
  have hn : η ≤ ‖z‖ := by
    apply hs.trans
    simpa [z, abs_of_nonneg (hη.le.trans hs)] using Complex.abs_im_le_norm z
  have hw : ‖w‖ ≤ ‖z‖ + |x - y| := by
    have he : w = z + ((y - x : ℝ) : ℂ) := by dsimp [w, z]; push_cast; ring
    rw [he]
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] using norm_add_le z ((y - x : ℝ) : ℂ)
  have hd : |x - y| ≤ (|x - y| / η) * ‖z‖ := by
    calc
      _ = (|x - y| / η) * η := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
  have hw' : ‖w‖ ≤ (1 + |x - y| / η) * ‖z‖ := by nlinarith
  have hsq : ‖w‖ ^ 2 ≤ (1 + |x - y| / η) ^ 2 * ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg z, sq_nonneg ((1 + |x - y| / η) * ‖z‖ - ‖w‖)]
  have hposx : 0 < (x - v) ^ 2 + s ^ 2 := by nlinarith
  have hposy : 0 < (y - v) ^ 2 + s ^ 2 := by nlinarith
  apply (div_le_div_iff₀ hposx hposy).mpr
  simp only [Complex.sq_norm] at hsq
  simpa [z, w, normSq_apply, ← pow_two] using hsq

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

def truncatedPotential (η x : ℝ) : ℝ := (2 / Real.pi) * ∫ s in η..1, μ.gamma s x / s

theorem gamma_div {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    μ.gamma s x / s = ∑ i, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2) := by
  unfold gamma
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem continuousOn_gamma_div {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ContinuousOn (fun s => μ.gamma s x / s) (Ici η) := by
  have hc : ContinuousOn (fun s => ∑ i, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2)) (Ici η) := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.div (by fun_prop) (fun s hs => ne_of_gt (by
      have : η ≤ s := hs
      nlinarith [sq_nonneg (x - μ.point i)]))
  apply hc.congr
  intro s hs
  exact μ.gamma_div (ne_of_gt (lt_of_lt_of_le hη hs)) x

theorem intervalIntegrable_gamma_div {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x : ℝ) :
    IntervalIntegrable (fun s => μ.gamma s x / s) volume η 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hη1]
  exact (μ.continuousOn_gamma_div hη x).mono Icc_subset_Ici_self

theorem truncatedPotential_nonneg {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x : ℝ) :
    0 ≤ μ.truncatedPotential η x := by
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg hη1
  intro s hs
  exact div_nonneg (μ.gamma_pos (lt_of_lt_of_le hη hs.1) x).le (hη.le.trans hs.1)

theorem truncatedPotential_local {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x y : ℝ) :
    μ.truncatedPotential η x ≤ (1 + |x - y| / η) ^ 2 * μ.truncatedPotential η y := by
  unfold truncatedPotential
  rw [mul_left_comm ((1 + |x - y| / η) ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hη1 (μ.intervalIntegrable_gamma_div hη hη1 x)
    ((μ.intervalIntegrable_gamma_div hη hη1 y).const_mul _)
  intro s hs
  rw [μ.gamma_div (ne_of_gt (hη.trans_le hs.1)), μ.gamma_div (ne_of_gt (hη.trans_le hs.1)),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hb := mul_le_mul_of_nonneg_left (quadratic_local_comparison (x := x) (y := y)
    (v := μ.point i) hη hs.1) (μ.mass_nonneg i)
  convert! hb using 1 <;> ring

theorem truncatedPotential_le_absolute {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {x : ℝ} (hx : ∀ i, x ≠ μ.point i) :
    μ.truncatedPotential η x ≤ ∑ i, μ.mass i / |x - μ.point i| := by
  have hi (i : Fin n) : IntervalIntegrable
      (fun s => μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2)) volume η 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun s => ne_of_gt (by
      have := sq_pos_of_ne_zero (sub_ne_zero.mpr (hx i))
      nlinarith [sq_nonneg s]))
  have he : (∫ s in η..1, μ.gamma s x / s) =
      ∑ i, ∫ s in η..1, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2) := by
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hη1] at hs
    exact μ.gamma_div (ne_of_gt (hη.trans_le hs.1)) x
  rw [truncatedPotential, he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he' : (∫ s in η..1, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2)) =
      μ.mass i * ∫ s in η..1, 1 / ((x - μ.point i) ^ 2 + s ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  rw [he']
  have hb := mul_le_mul_of_nonneg_left
    (inverse_quadratic_integral_bound hη.le (sub_ne_zero.mpr (hx i))) (μ.mass_nonneg i)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 / Real.pi by positivity)
  convert! hb' using 1
  field_simp

end AtomicProbability
end Erdos1132
