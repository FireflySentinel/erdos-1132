import Erdos1132.Additive.PoissonPotential

/-! # A uniform decrease of logarithmic potentials between two positive heights

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Real Complex
open scoped BigOperators
namespace Erdos1132

theorem log_norm_height_drop {t h : ℝ} (ht : |t| ≤ 2) (hh : 0 < h) (hh1 : h ≤ 1) :
    h^2/32 ≤ Real.log ‖(t : ℂ)+h*I‖ - Real.log ‖(t : ℂ)+(h/2 : ℝ)*I‖ := by
  let A := t^2+h^2
  let B := t^2+(h/2)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA5 : A ≤ 5 := by
    dsimp [A]
    nlinarith [sq_abs t, abs_nonneg t]
  have he1 : ‖(t : ℂ)+h*I‖^2 = A := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, A, pow_two]
  have he2 : ‖(t : ℂ)+(h/2 : ℝ)*I‖^2 = B := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, B, pow_two]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hB hA)
  rw [Real.log_div hB.ne' hA.ne'] at hlog
  have hlogA : Real.log A = 2*Real.log ‖(t : ℂ)+h*I‖ := by
    rw [← he1, Real.log_pow]
    norm_num
  have hlogB : Real.log B = 2*Real.log ‖(t : ℂ)+(h/2 : ℝ)*I‖ := by
    rw [← he2, Real.log_pow]
    norm_num
  have hAB : 1-B/A ≥ 3*h^2/20 := by
    apply (le_sub_iff_add_le).mpr
    apply (mul_le_mul_iff_left₀ hA).mp
    rw [one_mul]
    have he : (3*h^2/20+B/A)*A = 3*h^2*A/20+B := by field_simp
    rw [he]
    dsimp [A, B] at *
    nlinarith [mul_le_mul_of_nonneg_left hA5 (sq_nonneg h)]
  rw [hlogA, hlogB] at hlog
  nlinarith [sq_nonneg h]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem complexLogPotential_height_drop (hn : 0 < n) {x h : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    h^2/32 ≤ X.complexLogPotential x (h/2)-X.complexLogPotential x h := by
  have hpoint (i : Fin n) := log_norm_height_drop (t := x-X.point i)
    (by apply abs_le.mpr; have hi := X.mem_interval i; constructor <;> linarith [hx.1, hx.2, hi.1, hi.2]) hh hh1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_sub_distrib] at hs
  unfold complexLogPotential
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← sub_div]
  apply (le_div_iff₀ hnR).mpr
  nlinarith

end Nodes
end Erdos1132
