import Erdos1132.InterpolantPieces
import Erdos1132.InterpolantDerivative

/-! # Bounded nodal data attaining Lebesgue values and derivative jumps -/

noncomputable section
open Set Filter Polynomial Finset Real
open scoped Topology BigOperators
namespace Erdos1132

def unitSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem abs_unitSign (x : ℝ) : |unitSign x| = 1 := by unfold unitSign; split <;> norm_num

theorem unitSign_mul (x : ℝ) : unitSign x*x = |x| := by
  unfold unitSign
  split_ifs with hx
  · simp [abs_of_nonneg hx]
  · simp [abs_of_neg (lt_of_not_ge hx)]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem interpolant_derivative_eval (v : Fin n → ℝ) (x : ℝ) :
    (X.interpolant v).derivative.eval x = ∑ i, v i*(X.cardinal i).derivative.eval x := by
  simp [interpolant, derivative_sum, derivative_mul, eval_finsetSum, eval_mul, eval_C]

theorem exists_interpolant_attaining (x : ℝ) :
    ∃ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) ∧ (X.interpolant v).eval x = X.lebesgue x := by
  refine ⟨fun i => unitSign ((X.cardinal i).eval x), fun i => (abs_unitSign _).le, ?_⟩
  simp [interpolant, lebesgue, eval_finsetSum, eval_mul, eval_C, unitSign_mul]

theorem exists_interpolant_jump (k : Fin n) :
    ∃ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) ∧
      (X.interpolant v).derivative.eval (X.point k) = X.derivativeJump k/2 := by
  classical
  let v (i : Fin n) := if i = k then (0:ℝ) else unitSign ((X.cardinal i).derivative.eval (X.point k))
  refine ⟨v, ?_, ?_⟩
  · intro i
    dsimp only [v]
    split_ifs <;> simp [abs_unitSign]
  · rw [X.interpolant_derivative_eval, X.derivativeJump_eq_cardinal_sum,
      ← sum_erase_add _ _ (Finset.mem_univ k)]
    simp only [v, if_true, zero_mul, add_zero]
    have he : (∑ i ∈ univ.erase k, (if i = k then (0:ℝ) else
      unitSign ((X.cardinal i).derivative.eval (X.point k)))*(X.cardinal i).derivative.eval (X.point k)) =
        ∑ i ∈ univ.erase k, |(X.cardinal i).derivative.eval (X.point k)| := by
      apply sum_congr rfl
      intro i hi
      rw [if_neg (mem_erase.mp hi).1, unitSign_mul]
    rw [he]
    ring

theorem derivativeJump_le_of_interpolant_bound (k : Fin n) {D : ℝ}
    (hD : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      |(X.interpolant v).derivative.eval (X.point k)| ≤ D) : X.derivativeJump k ≤ 2*D := by
  obtain ⟨v, hv, he⟩ := X.exists_interpolant_jump k
  have hh := hD v hv
  rw [he, abs_of_nonneg (div_nonneg (X.derivativeJump_nonneg k) (by norm_num))] at hh
  linarith

end Nodes

theorem eventually_normalized_jump_upper (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ k : Fin n, (X n).point k ∈ Icc (l+2*d) (r-2*d) →
      (X n).derivativeJump k ≤
        2*(Real.pi*n*(X n).exteriorDensity l r (X n).potentialNormalization ((X n).point k) 0)*
          (logarithmicLevel a b n+η) := by
  filter_upwards [eventually_sharp_interpolant_derivative X hlr hI hd ha hupper hη]
    with n hn k hk
  have hh := (X n).derivativeJump_le_of_interpolant_bound k (hn _ hk)
  convert! hh using 1 <;> ring

end Erdos1132
