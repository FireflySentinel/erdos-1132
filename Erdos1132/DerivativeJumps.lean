import Erdos1132.Interpolation
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # The exact derivative jumps of a Lebesgue function -/

noncomputable section
open Set Filter Polynomial Finset
open scoped Topology BigOperators

namespace Erdos1132

theorem HasDerivAt.abs_right_of_eq_zero {f : ℝ → ℝ} {d x : ℝ}
    (hf : HasDerivAt f d x) (hx : f x = 0) :
    HasDerivWithinAt (fun y => |f y|) |d| (Ioi x) x := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have ht := (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).abs
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope_def_field, hx, abs_zero, sub_zero, abs_div,
    abs_of_pos (sub_pos.mpr (show x < y from hy))]

theorem HasDerivAt.abs_left_of_eq_zero {f : ℝ → ℝ} {d x : ℝ}
    (hf : HasDerivAt f d x) (hx : f x = 0) :
    HasDerivWithinAt (fun y => |f y|) (-|d|) (Iio x) x := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have ht := (hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)).abs.neg
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope_def_field, hx, abs_zero, sub_zero, abs_div,
    abs_of_neg (sub_neg.mpr (show y < x from hy)), div_neg, neg_neg]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem cardinal_mul_linear (i : Fin n) :
    (Polynomial.X - C (X.point i)) * X.cardinal i = C (X.weight i) * X.nodePolynomial := by
  unfold cardinal weight nodePolynomial
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (mem_univ i),
    Lagrange.nodal_eq_mul_nodal_erase (mem_univ i)]
  ring

/-- The derivative of one cardinal polynomial at a different interpolation node. -/
theorem cardinal_derivative_at_other_node (i k : Fin n) (hik : i ≠ k) :
    (X.cardinal i).derivative.eval (X.point k) =
      X.weight i / (X.weight k * (X.point k - X.point i)) := by
  have hid := congrArg (fun P : ℝ[X] => P.derivative.eval (X.point k))
    (X.cardinal_mul_linear i)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_add, eval_mul, one_mul, eval_sub, eval_X,
    eval_C, zero_mul, zero_add] at hid
  rw [X.cardinal_at_node, if_neg hik, zero_add] at hid
  have hw : X.nodePolynomial.derivative.eval (X.point k) = (X.weight k)⁻¹ := by
    rw [X.weight_eq_derivative, inv_inv]
  rw [hw] at hid
  have hdiff : X.point k - X.point i ≠ 0 :=
    sub_ne_zero.mpr (X.injective.ne hik.symm)
  apply (eq_div_iff (mul_ne_zero (X.weight_ne_zero k) hdiff)).mpr
  calc
    _ = X.weight k * ((X.point k - X.point i) * (X.cardinal i).derivative.eval (X.point k)) := by ring
    _ = X.weight k * (X.weight i * (X.weight k)⁻¹) := by rw [hid]
    _ = X.weight i := by field_simp [X.weight_ne_zero k]

theorem abs_cardinal_derivative_at_other_node (i k : Fin n) (hik : i ≠ k) :
    |(X.cardinal i).derivative.eval (X.point k)| =
      X.mass i / (X.mass k * |X.point k - X.point i|) := by
  rw [X.cardinal_derivative_at_other_node i k hik, abs_div, abs_mul]
  unfold mass
  have hW : X.totalWeight ≠ 0 := (X.totalWeight_pos (Nat.zero_lt_of_lt i.isLt)).ne'
  field_simp

def derivativeJump (k : Fin n) : ℝ :=
  derivWithin X.lebesgue (Ioi (X.point k)) (X.point k) -
    derivWithin X.lebesgue (Iio (X.point k)) (X.point k)

theorem lebesgue_hasDerivWithinAt_right (k : Fin n) :
    HasDerivWithinAt X.lebesgue
      (∑ i : Fin n, if i = k then (X.cardinal i).derivative.eval (X.point k)
        else |(X.cardinal i).derivative.eval (X.point k)|)
      (Ioi (X.point k)) (X.point k) := by
  apply HasDerivWithinAt.fun_sum
  intro i _
  change HasDerivWithinAt (fun y : ℝ => |(X.cardinal i).eval y|) _ _ _
  have hp : HasDerivAt (fun y : ℝ => (X.cardinal i).eval y)
      ((X.cardinal i).derivative.eval (X.point k)) (X.point k) :=
    (X.cardinal i).hasDerivAt (X.point k)
  by_cases hik : i = k
  · rw [if_pos hik]
    have hpos : 0 < (X.cardinal i).eval (X.point k) := by
      rw [X.cardinal_at_node, if_pos hik]; norm_num
    simpa only [one_mul] using!
      ((hasDerivAt_abs_pos hpos).comp (X.point k) hp).hasDerivWithinAt
  · rw [if_neg hik]
    exact HasDerivAt.abs_right_of_eq_zero hp
      (by rw [X.cardinal_at_node, if_neg hik])

theorem lebesgue_hasDerivWithinAt_left (k : Fin n) :
    HasDerivWithinAt X.lebesgue
      (∑ i : Fin n, if i = k then (X.cardinal i).derivative.eval (X.point k)
        else -|(X.cardinal i).derivative.eval (X.point k)|)
      (Iio (X.point k)) (X.point k) := by
  apply HasDerivWithinAt.fun_sum
  intro i _
  change HasDerivWithinAt (fun y : ℝ => |(X.cardinal i).eval y|) _ _ _
  have hp : HasDerivAt (fun y : ℝ => (X.cardinal i).eval y)
      ((X.cardinal i).derivative.eval (X.point k)) (X.point k) :=
    (X.cardinal i).hasDerivAt (X.point k)
  by_cases hik : i = k
  · rw [if_pos hik]
    have hpos : 0 < (X.cardinal i).eval (X.point k) := by
      rw [X.cardinal_at_node, if_pos hik]; norm_num
    simpa only [one_mul] using!
      ((hasDerivAt_abs_pos hpos).comp (X.point k) hp).hasDerivWithinAt
  · rw [if_neg hik]
    exact HasDerivAt.abs_left_of_eq_zero hp
      (by rw [X.cardinal_at_node, if_neg hik])

/-- The cusp formula includes the first and last nodes, using the exterior
polynomial pieces for their outward derivatives. -/
theorem derivativeJump_eq_cardinal_sum (k : Fin n) :
    X.derivativeJump k = 2 * ∑ i ∈ univ.erase k,
      |(X.cardinal i).derivative.eval (X.point k)| := by
  rw [derivativeJump,
    (X.lebesgue_hasDerivWithinAt_right k).derivWithin (uniqueDiffWithinAt_Ioi _),
    (X.lebesgue_hasDerivWithinAt_left k).derivWithin (uniqueDiffWithinAt_Iio _),
    ← sum_sub_distrib]
  rw [← sum_erase_add _ _ (mem_univ k)]
  simp only [ite_true, sub_self, add_zero, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [if_neg (mem_erase.mp hi).1, if_neg (mem_erase.mp hi).1]
  ring

/-- The exact mass-weighted jump identity in Section 3. -/
theorem derivativeJump_eq_mass_sum (k : Fin n) :
    X.derivativeJump k = 2 * ∑ i ∈ univ.erase k,
      X.mass i / (X.mass k * |X.point k - X.point i|) := by
  rw [X.derivativeJump_eq_cardinal_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact X.abs_cardinal_derivative_at_other_node i k (mem_erase.mp hi).1

theorem derivativeJump_nonneg (k : Fin n) : 0 ≤ X.derivativeJump k := by
  rw [X.derivativeJump_eq_cardinal_sum]
  positivity

end Nodes
end Erdos1132
