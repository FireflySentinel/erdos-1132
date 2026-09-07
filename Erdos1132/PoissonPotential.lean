import Erdos1132.PoissonLog
import Erdos1132.PotentialL2

/-! # Exact Poisson representation of empirical logarithmic potentials -/

noncomputable section
open MeasureTheory Set Finset Complex
open scoped BigOperators
namespace Erdos1132.Nodes
variable {n : ℕ} (X : Erdos1132.Nodes n)

/-- The logarithmic potential at a complex point in Cartesian coordinates. -/
def complexLogPotential (x h : ℝ) : ℝ :=
  -(∑ i, Real.log ‖((x-X.point i : ℝ) : ℂ)+h*I‖) / n

theorem integrable_poisson_empiricalLogPotential {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * X.empiricalLogPotential y) := by
  have hi := ((integrable_finsetSum Finset.univ
    (fun i _ => integrable_poisson_log hh x (X.point i))).neg).div_const (n : ℝ)
  convert hi using 1
  funext y
  simp only [empiricalLogPotential, ← mul_div_assoc, mul_neg, Finset.mul_sum, Pi.neg_apply]

theorem poisson_empiricalLogPotential {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∫ y, poissonKernel h (y-x) * X.empiricalLogPotential y) =
      X.complexLogPotential x h := by
  simp_rw [empiricalLogPotential, ← mul_div_assoc, mul_neg, Finset.mul_sum]
  rw [integral_div, integral_neg, integral_finsetSum _
    (fun i _ => integrable_poisson_log hh x (X.point i))]
  simp only [integral_poisson_log hh, complexLogPotential]

theorem integrable_poisson_potential_sub {h : ℝ} (hh : 0 < h) (x α : ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * (X.empiricalLogPotential y-α)) := by
  simpa only [mul_sub, Pi.sub_apply] using! (X.integrable_poisson_empiricalLogPotential hh x).sub
    (((integrable_poissonKernel hh.le).comp_sub_right x).mul_const α)

/-- Centering the Poisson formula at any real normalization constant. -/
theorem poisson_potential_sub {h : ℝ} (hh : 0 < h) (x α : ℝ) :
    X.complexLogPotential x h = α +
      ∫ y, poissonKernel h (y-x) * (X.empiricalLogPotential y-α) := by
  simp_rw [mul_sub]
  rw [integral_sub (X.integrable_poisson_empiricalLogPotential hh x)
    (((integrable_poissonKernel hh.le).comp_sub_right x).mul_const α),
    X.poisson_empiricalLogPotential hh, integral_mul_const,
    integral_sub_right_eq_self, integral_poissonKernel hh]
  ring

theorem complexLogPotential_eq_polynomial {h : ℝ} (hh : 0 < h) (x : ℝ) :
    X.complexLogPotential x h =
      -Real.log ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ / n := by
  have hnz (i : Fin n) : ((x-X.point i : ℝ) : ℂ)+h*I ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hh.ne' hi
  have he : X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I) =
      ∏ i, (((x-X.point i : ℝ) : ℂ)+h*I) := by
    simp only [nodePolynomial, Lagrange.nodal, Polynomial.eval₂_finsetProd,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    apply Finset.prod_congr rfl
    intro i _
    change (x : ℂ)+h*I-(X.point i : ℂ) = ((x-X.point i : ℝ) : ℂ)+h*I
    push_cast
    ring
  rw [he, norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hnz i))]
  rfl

end Erdos1132.Nodes
