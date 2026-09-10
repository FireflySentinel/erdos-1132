import Erdos1132.Additive.DerivativeJumps

/-! # Symmetrization of the derivative-jump energy

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace Erdos1132

/-- Pairing the two orientations of each interaction removes the positive
mass ratios. The amplitudes may vanish. -/
theorem reciprocal_energy_le_weighted {ι : Type*} [Fintype ι]
    (x a ν : ι → ℝ) (hν : ∀ i, 0 < ν i) :
    (∑ k, ∑ j, a k * a j / |x k - x j|) ≤
      ∑ k, ∑ j, (a k)^2 * ν j / (ν k * |x k - x j|) := by
  have hpair (k j : ι) : 2 * (a k * a j / |x k - x j|) ≤
      (a k)^2 * ν j / (ν k * |x k - x j|) +
        (a j)^2 * ν k / (ν j * |x j - x k|) := by
    have hraw : 2 * a k * a j ≤ (a k)^2 * ν j / ν k + (a j)^2 * ν k / ν j := by
      have heq : (a k)^2 * ν j / ν k + (a j)^2 * ν k / ν j =
          ((a k * ν j)^2 + (a j * ν k)^2) / (ν k * ν j) := by
        field_simp
      rw [heq]
      apply (le_div_iff₀ (mul_pos (hν k) (hν j))).mpr
      nlinarith [sq_nonneg (a k * ν j - a j * ν k)]
    calc
      _ = (2 * a k * a j) / |x k - x j| := by ring
      _ ≤ ((a k)^2 * ν j / ν k + (a j)^2 * ν k / ν j) / |x k - x j| :=
        div_le_div_of_nonneg_right hraw (abs_nonneg _)
      _ = _ := by rw [add_div, div_div, div_div, abs_sub_comm (x k) (x j)]
  have hsum := sum_le_sum (s := univ) fun k _ => sum_le_sum (s := univ) fun j _ => hpair k j
  simp only [sum_add_distrib, ← mul_sum] at hsum
  have hswap : (∑ k, ∑ j, (a j)^2 * ν k / (ν j * |x j - x k|)) =
      ∑ k, ∑ j, (a k)^2 * ν j / (ν k * |x k - x j|) := sum_comm
  rw [hswap] at hsum
  linarith

namespace Nodes
variable {n : ℕ} (X : Nodes n)

/-- The ordered-sum normalization of the jump energy, with its diagonal
identically zero under real division. -/
theorem jumpEnergy_eq_weighted (a : Fin n → ℝ) :
    (∑ k, (a k)^2 * X.derivativeJump k / 2) =
      ∑ k, ∑ j, (a k)^2 * X.mass j / (X.mass k * |X.point k - X.point j|) := by
  apply sum_congr rfl
  intro k _
  rw [X.derivativeJump_eq_mass_sum]
  have heq : (a k)^2 * (2 * ∑ i ∈ univ.erase k,
      X.mass i / (X.mass k * |X.point k - X.point i|)) / 2 =
      ∑ i ∈ univ.erase k, (a k)^2 * X.mass i / (X.mass k * |X.point k - X.point i|) := by
    calc
      _ = (a k)^2 * ∑ i ∈ univ.erase k,
          X.mass i / (X.mass k * |X.point k - X.point i|) := by ring
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
  rw [heq, ← sum_erase_add _ _ (mem_univ k)]
  simp

/-- The reciprocal-distance energy is bounded above by the derivative-jump
energy, including zero amplitudes and endpoint nodes. -/
theorem reciprocal_energy_le_jumpEnergy (a : Fin n → ℝ) :
    (∑ k, ∑ j, a k * a j / |X.point k - X.point j|) ≤
      ∑ k, (a k)^2 * X.derivativeJump k / 2 := by
  rw [X.jumpEnergy_eq_weighted]
  exact reciprocal_energy_le_weighted X.point a X.mass
    (fun i => X.mass_pos (Nat.zero_lt_of_lt i.isLt) i)

end Nodes
end Erdos1132
