import Erdos1132.Additive.CosCircleBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # The finite set of cosine poles used by the local Riesz formula

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Complex Real Metric Set Finset
open scoped BigOperators
namespace Erdos1132

def rieszPoint (j : ℤ) : ℝ := ((j : ℝ)+1/2)*Real.pi

def cosinePoles (m : ℕ) : Finset ℂ :=
  (Finset.Ico (-(m : ℤ)) (m : ℤ)).image (fun j => (rieszPoint j : ℂ))

theorem rieszPoint_cos (j : ℤ) : Complex.cos (rieszPoint j) = 0 := by
  apply Complex.cos_eq_zero_iff.mpr
  refine ⟨j, ?_⟩
  simp only [rieszPoint, ofReal_mul, ofReal_add, ofReal_intCast, ofReal_div, ofReal_one,
    ofReal_ofNat]
  ring

theorem rieszPoint_norm_lt {m : ℕ} {j : ℤ}
    (hj : j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ)) : ‖(rieszPoint j : ℂ)‖ < (m : ℝ)*Real.pi := by
  rcases Finset.mem_Ico.mp hj with ⟨hlo, hhi⟩
  have hlo' : -(m : ℝ) ≤ j := by exact_mod_cast hlo
  have hhi' : (j : ℝ)+1 ≤ m := by exact_mod_cast (show j+1 ≤ (m : ℤ) by omega)
  rw [Complex.norm_real, Real.norm_eq_abs, rieszPoint, abs_mul, abs_of_pos Real.pi_pos]
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem cosinePoles_inside {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    ‖z‖ < (m : ℝ)*Real.pi := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  exact rieszPoint_norm_lt hj

theorem cosinePoles_real {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) : z.im = 0 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  simp

theorem cosinePoles_zero {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) : Complex.cos z = 0 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  exact rieszPoint_cos j

theorem zero_not_mem_cosinePoles (m : ℕ) : (0 : ℂ) ∉ cosinePoles m := by
  intro he
  have h := cosinePoles_zero he
  simpa using h

theorem cos_zero_mem_cosinePoles {m : ℕ} {z : ℂ} (hz : Complex.cos z = 0)
    (hn : ‖z‖ < (m : ℝ)*Real.pi) : z ∈ cosinePoles m := by
  obtain ⟨j, hj⟩ := Complex.cos_eq_zero_iff.mp hz
  have he : z = (rieszPoint j : ℂ) := by
    rw [hj]
    simp only [rieszPoint, ofReal_mul, ofReal_add, ofReal_intCast, ofReal_div, ofReal_one,
      ofReal_ofNat]
    ring
  rw [he] at hn ⊢
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_Ico.mpr ?_, rfl⟩
  rw [Complex.norm_real, Real.norm_eq_abs, rieszPoint, abs_mul, abs_of_pos Real.pi_pos] at hn
  have hab : |(j : ℝ)+1/2| < m := by nlinarith [Real.pi_pos]
  have hb := abs_lt.mp hab
  have hlo : -(m : ℝ)-1 < j := by linarith [hb.1]
  have hhi : (j : ℝ) < m := by linarith [hb.2]
  have hlo' : -(m : ℤ)-1 < j := by exact_mod_cast hlo
  have hhi' : j < (m : ℤ) := by exact_mod_cast hhi
  exact ⟨by omega, hhi'⟩

theorem cosinePoles_exact {m : ℕ} (hm : 1 ≤ m) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) ((m : ℝ)*Real.pi)) :
    Complex.cos z = 0 ↔ z ∈ cosinePoles m := by
  constructor
  · intro hc
    apply cos_zero_mem_cosinePoles hc
    have hn : ‖z‖ ≤ (m : ℝ)*Real.pi := by simpa [mem_closedBall, dist_eq_norm] using hz
    apply lt_of_le_of_ne hn
    intro he
    have hb := exp_im_le_eight_norm_cos hm he
    rw [hc, norm_zero, mul_zero] at hb
    exact (Real.exp_pos _).not_ge hb
  · exact cosinePoles_zero

theorem cosinePoles_sin_sq {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    Complex.sin z ^ 2 = 1 := by
  have h := Complex.sin_sq_add_cos_sq z
  simpa [cosinePoles_zero hz] using h

theorem cosinePoles_simple {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    deriv Complex.cos z ≠ 0 := by
  rw [Complex.deriv_cos]
  apply neg_ne_zero.mpr
  intro he
  have h := cosinePoles_sin_sq hz
  simp [he] at h

theorem cosinePoles_sin_norm {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    ‖Complex.sin z‖ = 1 := by
  have h := congrArg norm (cosinePoles_sin_sq hz)
  rw [norm_pow, norm_one] at h
  nlinarith [norm_nonneg (Complex.sin z)]

theorem first_rieszPoint_mem {m : ℕ} (hm : 1 ≤ m) :
    (Real.pi/2 : ℂ) ∈ cosinePoles m := by
  apply Finset.mem_image.mpr
  refine ⟨0, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
  simp [rieszPoint]
  ring

end Erdos1132
