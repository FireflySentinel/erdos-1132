import Erdos1132.Additive.LocalPotential
import Erdos1132.Additive.LogSquare
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # A uniform square-integral bound for empirical logarithmic potentials

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Polynomial Finset
open scoped BigOperators
namespace Erdos1132.Nodes
variable {n : ℕ} (X : Erdos1132.Nodes n)

def empiricalLogPotential (x : ℝ) : ℝ :=
  -(∑ i, Real.log (x-X.point i)) / n

theorem empiricalLogPotential_eq_realLogPotential {x : ℝ}
    (hx : ∀ i, x ≠ X.point i) : X.empiricalLogPotential x = X.realLogPotential x := by
  unfold empiricalLogPotential realLogPotential
  rw [Real.log_abs]
  congr 2
  unfold nodePolynomial Lagrange.nodal
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  exact (Real.log_prod (fun i _ => sub_ne_zero.mpr (hx i))).symm

theorem ae_empiricalLogPotential_eq_realLogPotential :
    X.empiricalLogPotential =ᵐ[volume] X.realLogPotential := by
  have havoid : ∀ᵐ x : ℝ, x ∉ Set.range X.point := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      (Set.finite_range X.point).measure_zero volume
  filter_upwards [havoid] with x hx
  exact X.empiricalLogPotential_eq_realLogPotential
    (fun i hi => hx ⟨i, hi.symm⟩)

theorem measurable_empiricalLogPotential : Measurable X.empiricalLogPotential := by
  unfold empiricalLogPotential
  exact ((Finset.measurable_sum _ fun i _ =>
    Real.measurable_log.comp (measurable_id.sub measurable_const)).neg).div_const _

theorem empiricalLogPotential_sq_le (hn : 0 < n) (x : ℝ) :
    (X.empiricalLogPotential x)^2 ≤ (∑ i, (Real.log (x-X.point i))^2) / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun i : Fin n => Real.log (x-X.point i)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hcs
  unfold empiricalLogPotential
  rw [div_pow, neg_sq]
  apply (div_le_div_iff₀ (sq_pos_of_pos hnR) hnR).mpr
  nlinarith

theorem integrableOn_empiricalLogPotential (a b : ℝ) :
    IntegrableOn X.empiricalLogPotential (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · have hi (i : Fin n) : IntegrableOn (fun x => Real.log (x-X.point i)) (Set.Icc a b) := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      simpa only [sub_add_cancel] using
        (intervalIntegral.intervalIntegrable_log' (a := a-X.point i) (b := b-X.point i)).comp_sub_right (X.point i)
    exact ((integrable_finsetSum _ fun i _ => hi i).neg).div_const _
  · simp [Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)]

theorem integrableOn_empiricalLogPotential_sq (hn : 0 < n) (a b : ℝ) :
    IntegrableOn (fun x => (X.empiricalLogPotential x)^2) (Set.Icc a b) := by
  have hi : IntegrableOn (fun x => (∑ i, (Real.log (x-X.point i))^2) / n) (Set.Icc a b) :=
    (integrable_finsetSum _ (fun i _ => integrableOn_log_sub_sq a b (X.point i))).div_const _
  apply hi.mono' ((X.measurable_empiricalLogPotential.pow_const 2).aestronglyMeasurable)
  apply ae_of_all
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X.empiricalLogPotential x))] using
    X.empiricalLogPotential_sq_le hn x

/-- The square-integral bound is independent of the row size and of the node
positions in `[-1,1]`. -/
theorem integral_empiricalLogPotential_sq_le (hn : 0 < n) :
    (∫ x in Set.Icc (-2 : ℝ) 2, (X.empiricalLogPotential x)^2) ≤
      ∫ x in Set.Icc (-3 : ℝ) 3, (Real.log x)^2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi (i : Fin n) := integrableOn_log_sub_sq (-2) 2 (X.point i)
  calc
    _ ≤ ∫ x in Set.Icc (-2 : ℝ) 2, (∑ i, (Real.log (x-X.point i))^2) / n :=
      integral_mono (X.integrableOn_empiricalLogPotential_sq hn _ _)
        ((integrable_finsetSum _ (fun i _ => hi i)).div_const _) (X.empiricalLogPotential_sq_le hn)
    _ = (∑ i, ∫ x in Set.Icc (-2 : ℝ) 2, (Real.log (x-X.point i))^2) / n := by
      rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
    _ ≤ (∑ _i : Fin n, ∫ x in Set.Icc (-3 : ℝ) 3, (Real.log x)^2) / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      exact sum_le_sum (fun i _ => integral_log_sub_sq_le (X.mem_interval i))
    _ = _ := by simp [hnR.ne']

end Erdos1132.Nodes
