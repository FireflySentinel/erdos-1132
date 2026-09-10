import Erdos1132.Shared.IntervalHarmonic
import Mathlib.Algebra.Polynomial.Roots

/-! # Rational formulas and boundary limits for Cauchy transforms

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset Complex Set

namespace Erdos1132.AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

def denominator : ℂ[X] := Lagrange.nodal univ (fun i => (μ.point i : ℂ))

def numerator : ℂ[X] :=
  ∑ i, C (μ.mass i : ℂ) * Lagrange.nodal (univ.erase i) (fun j => (μ.point j : ℂ))

theorem denominator_eval_ne_zero {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
    μ.denominator.eval z ≠ 0 :=
  Lagrange.eval_nodal_not_at_node (fun i _ => hz i)

theorem numerator_eval {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
    μ.numerator.eval z = μ.denominator.eval z * μ.cauchy z := by
  simp only [numerator, eval_finsetSum, eval_mul, eval_C, cauchy, mul_sum]
  apply sum_congr rfl
  intro i _
  have h := congrArg (Polynomial.eval z)
    (Lagrange.nodal_eq_mul_nodal_erase (v := fun j => (μ.point j : ℂ)) (mem_univ i))
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  have hzi := sub_ne_zero.mpr (hz i)
  apply (mul_right_cancel₀ hzi)
  rw [mul_assoc _ (_ / _) _, div_mul_cancel₀ _ hzi]
  dsimp [denominator]
  linear_combination -(μ.mass i : ℂ) * h

theorem finite_boundary_fiber (v : ℝ) : {t : ℝ | μ.boundary t = v}.Finite := by
  let q : ℂ[X] := C (v : ℂ) * μ.denominator - μ.numerator
  have heval {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
      q.eval z = μ.denominator.eval z * ((v : ℂ) - μ.cauchy z) := by
    simp only [q, eval_sub, eval_mul, eval_C, μ.numerator_eval hz]
    ring
  have hI (i : Fin n) : I ≠ (μ.point i : ℂ) := by
    intro hi
    have := congrArg Complex.im hi
    norm_num at this
  have hq : q ≠ 0 := by
    intro hq
    have h := heval hI
    rw [hq, eval_zero] at h
    have hc : (v : ℂ) = μ.cauchy I := sub_eq_zero.mp
      ((mul_eq_zero.mp h.symm).resolve_left (μ.denominator_eval_ne_zero hI))
    have hi := μ.cauchy_im_neg (z := I) (by simp)
    rw [← hc] at hi
    simp at hi
  have hf : {t : ℝ | q.IsRoot (t : ℂ)}.Finite :=
    Set.Finite.preimage Complex.ofReal_injective.injOn (Polynomial.finite_setOfPred_isRoot hq)
  apply ((Set.finite_range μ.point).union hf).subset
  intro t ht
  by_cases hnode : t ∈ range μ.point
  · exact Or.inl hnode
  · right
    have htn (i : Fin n) : (t : ℂ) ≠ (μ.point i : ℂ) := by
      intro hi
      exact hnode ⟨i, (Complex.ofReal_injective hi).symm⟩
    change q.eval (t : ℂ) = 0
    rw [heval htn, μ.cauchy_ofReal t, ht, sub_self, mul_zero]

theorem ae_regular_boundary_comp (a b : ℝ) {g : ℝ → ℝ} (hg : Function.Injective g) :
    ∀ᵐ t, (∀ i, g t ≠ μ.point i) ∧ μ.boundary (g t) ≠ a ∧ μ.boundary (g t) ≠ b := by
  have hfinite : (range μ.point ∪ {t | μ.boundary t = a} ∪ {t | μ.boundary t = b}).Finite :=
    ((Set.finite_range μ.point).union (μ.finite_boundary_fiber a)).union (μ.finite_boundary_fiber b)
  have hnull := (Set.Finite.preimage hg.injOn hfinite).measure_zero (μ := MeasureTheory.volume)
  have hae : ∀ᵐ t, t ∉ g ⁻¹' (range μ.point ∪ {t | μ.boundary t = a} ∪ {t | μ.boundary t = b}) := by
    apply MeasureTheory.ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hae] with t ht
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
  exact ⟨fun i hi => ht.1.1 ⟨i, hi.symm⟩, ht.1.2, ht.2⟩

end Erdos1132.AtomicProbability
