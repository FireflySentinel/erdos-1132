import Erdos1132.DerivativeJumps
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Elementary bounds for the normalized node polynomial -/

noncomputable section
open Polynomial Finset Set
open scoped BigOperators
namespace Erdos1132.Nodes
variable {n : ℕ} (X : Erdos1132.Nodes n)

theorem sum_cardinal (hn : 0 < n) : ∑ i, X.cardinal i = 1 := by
  exact Lagrange.sum_basis X.injective.injOn ⟨⟨0, hn⟩, mem_univ _⟩

theorem one_le_lebesgue (hn : 0 < n) (x : ℝ) : 1 ≤ X.lebesgue x := by
  have he : ∑ i, (X.cardinal i).eval x = 1 := by
    rw [← eval_finsetSum, X.sum_cardinal hn, eval_one]
  calc
    1 = |∑ i, (X.cardinal i).eval x| := by rw [he, abs_one]
    _ ≤ _ := abs_sum_le_sum_abs _ _

theorem abs_cardinal_identity (i : Fin n) (x : ℝ) :
    |x - X.point i| * |(X.cardinal i).eval x| =
      |X.weight i| * |X.nodePolynomial.eval x| := by
  have he := congrArg (fun P : ℝ[X] => P.eval x) (X.cardinal_mul_linear i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at he
  simpa only [abs_mul] using congrArg abs he

/-- The normalized monic polynomial is bounded by twice the Lebesgue function
throughout the interpolation interval, including the nodes. -/
theorem normalized_polynomial_le_lebesgue {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |X.nodePolynomial.eval x| * X.totalWeight ≤ 2 * X.lebesgue x := by
  unfold totalWeight lebesgue
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro i _
  rw [mul_comm |X.nodePolynomial.eval x|, ← X.abs_cardinal_identity]
  have hdist : |x-X.point i| ≤ 2 := by
    apply abs_le.mpr
    have hi := X.mem_interval i
    constructor <;> linarith [hx.1, hx.2, hi.1, hi.2]
  exact mul_le_mul_of_nonneg_right hdist (abs_nonneg _)

/-- A lower bound on every node distance supplies the reverse inequality. -/
theorem distance_mul_lebesgue_le_normalized_polynomial {δ x : ℝ}
    (hδ : ∀ i, δ ≤ |x - X.point i|) :
    δ * X.lebesgue x ≤ |X.nodePolynomial.eval x| * X.totalWeight := by
  unfold lebesgue totalWeight
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro i _
  calc
    _ ≤ |x-X.point i| * |(X.cardinal i).eval x| :=
      mul_le_mul_of_nonneg_right (hδ i) (abs_nonneg _)
    _ = _ := by rw [X.abs_cardinal_identity]; ring

theorem distance_le_normalized_polynomial (hn : 0 < n) {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ i, δ ≤ |x - X.point i|) :
    δ ≤ |X.nodePolynomial.eval x| * X.totalWeight := by
  calc
    δ = δ * 1 := (mul_one _).symm
    _ ≤ δ * X.lebesgue x := mul_le_mul_of_nonneg_left (X.one_le_lebesgue hn x) hδ0
    _ ≤ _ := X.distance_mul_lebesgue_le_normalized_polynomial hδ

def potentialNormalization : ℝ := Real.log X.totalWeight / n

def realLogPotential (x : ℝ) : ℝ := -Real.log |X.nodePolynomial.eval x| / n

/-- The local polynomial bounds give explicit two-sided logarithmic-potential
bounds away from the nodes. -/
theorem local_potential_bounds (hn : 0 < n) {x δ Λ : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) (hδ0 : 0 < δ) (hδ : ∀ i, δ ≤ |x-X.point i|)
    (hΛ : X.lebesgue x ≤ Λ) :
    X.potentialNormalization - Real.log (2*Λ)/n ≤ X.realLogPotential x ∧
      X.realLogPotential x ≤ X.potentialNormalization - Real.log δ/n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlow := X.distance_le_normalized_polynomial hn hδ0.le hδ
  have hupper := (X.normalized_polynomial_le_lebesgue hx).trans
    (mul_le_mul_of_nonneg_left hΛ (by norm_num))
  have hprod : 0 < |X.nodePolynomial.eval x| * X.totalWeight := hδ0.trans_le hlow
  have hP : 0 < |X.nodePolynomial.eval x| :=
    (mul_pos_iff_of_pos_right (X.totalWeight_pos hn)).mp hprod
  have hlo := Real.log_le_log hδ0 hlow
  have hhi := Real.log_le_log hprod hupper
  rw [Real.log_mul hP.ne' (X.totalWeight_pos hn).ne'] at hlo hhi
  unfold potentialNormalization realLogPotential
  constructor
  · apply (le_div_iff₀ hnR).mpr
    have he : (Real.log X.totalWeight/n - Real.log (2*Λ)/n) * n =
        Real.log X.totalWeight - Real.log (2*Λ) := by field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hnR).mpr
    have he : (Real.log X.totalWeight/n - Real.log δ/n) * n =
        Real.log X.totalWeight - Real.log δ := by field_simp
    rw [he]
    linarith

end Erdos1132.Nodes
