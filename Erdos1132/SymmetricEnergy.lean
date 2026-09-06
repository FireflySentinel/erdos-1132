import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

noncomputable section

open MeasureTheory

namespace Erdos1132

/-- Symmetrizing a positive ratio can only increase the energy of a symmetric kernel. -/
theorem symmetric_ratio_energy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (k : α → α → ℝ) (w : α → ℝ)
    (hk : ∀ x y, 0 ≤ k x y) (hs : ∀ x y, k x y = k y x)
    (hw : ∀ x, 0 < w x)
    (hi : Integrable (fun p : α × α => k p.1 p.2) (μ.prod μ))
    (hr : Integrable (fun p : α × α => k p.1 p.2 * (w p.2 / w p.1)) (μ.prod μ)) :
    (∫ p : α × α, k p.1 p.2 ∂μ.prod μ) ≤
      ∫ p : α × α, k p.1 p.2 * (w p.2 / w p.1) ∂μ.prod μ := by
  have hp (x y : α) : 2 * k x y ≤
      k x y * (w y / w x) + k y x * (w x / w y) := by
    have ha : 2 ≤ w y / w x + w x / w y := by
      calc
        2 ≤ (w y * w y + w x * w x) / (w x * w y) := by
          apply (le_div_iff₀ (mul_pos (hw x) (hw y))).mpr
          nlinarith [sq_nonneg (w x - w y)]
        _ = w y / w x + w x / w y := by
          field_simp
    rw [← hs x y]
    nlinarith [mul_le_mul_of_nonneg_left ha (hk x y)]
  have hm := integral_mono (hi.const_mul 2) (hr.add hr.swap)
    (fun p => hp p.1 p.2)
  simp only [Pi.add_apply] at hm
  rw [integral_const_mul, integral_add hr hr.swap] at hm
  change 2 * (∫ p : α × α, k p.1 p.2 ∂μ.prod μ) ≤
    (∫ p : α × α, k p.1 p.2 * (w p.2 / w p.1) ∂μ.prod μ) +
    (∫ p : α × α, (fun q : α × α => k q.1 q.2 * (w q.2 / w q.1)) p.swap
      ∂μ.prod μ) at hm
  have heq := integral_prod_swap (μ := μ) (ν := μ)
    (fun p : α × α => k p.1 p.2 * (w p.2 / w p.1))
  rw [heq] at hm
  linarith

end Erdos1132
