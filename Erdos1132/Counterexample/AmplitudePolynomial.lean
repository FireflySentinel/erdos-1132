import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# Algebraic part of the amplitude construction

The polynomial in (7.18) has the prescribed trigonometric expansion and degree
exactly `n` when `h(0)` is nonzero and `n > deg h`.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace Erdos1132.Counterexample

def amplitudePolynomial (h : ℝ[X]) (n : ℕ) : ℝ[X] :=
  ∑ r ∈ range (h.natDegree + 1),
    C (h.coeff r) * Polynomial.Chebyshev.T ℝ (n - r : ℕ)

theorem amplitudePolynomial_eval_cos (h : ℝ[X]) (n : ℕ) (θ : ℝ) :
    (amplitudePolynomial h n).eval (Real.cos θ) =
      ∑ r ∈ range (h.natDegree + 1), h.coeff r * Real.cos ((n - r : ℕ) * θ) := by
  simp [amplitudePolynomial, eval_finsetSum, Polynomial.Chebyshev.T_real_cos]

/-- The real and imaginary trigonometric components of the amplitude give the
exact phase expansion, before choosing a continuous argument of `h`. -/
theorem amplitudePolynomial_trig_expansion (h : ℝ[X]) {n : ℕ}
    (hn : h.natDegree < n) (θ : ℝ) :
    (amplitudePolynomial h n).eval (Real.cos θ) =
      Real.cos (n * θ) *
        (∑ r ∈ range (h.natDegree + 1), h.coeff r * Real.cos (r * θ)) +
      Real.sin (n * θ) *
        (∑ r ∈ range (h.natDegree + 1), h.coeff r * Real.sin (r * θ)) := by
  rw [amplitudePolynomial_eval_cos, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  have hrn : r ≤ n := by have := mem_range.mp hr; omega
  rw [Nat.cast_sub hrn, sub_mul, Real.cos_sub]
  ring

/-- The `h₀ Tₙ` term cannot cancel with the remaining lower-degree terms. -/
theorem amplitudePolynomial_degree (h : ℝ[X]) {n : ℕ}
    (hn : h.natDegree < n) (hzero : h.coeff 0 ≠ 0) :
    (amplitudePolynomial h n).degree = (n : WithBot ℕ) := by
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  let q : ℝ[X] := ∑ r ∈ range h.natDegree,
    C (h.coeff (r + 1)) * Polynomial.Chebyshev.T ℝ (n - (r + 1) : ℕ)
  have hsplit : amplitudePolynomial h n =
      C (h.coeff 0) * Polynomial.Chebyshev.T ℝ (n : ℕ) + q := by
    unfold amplitudePolynomial q
    rw [sum_range_succ']
    simp only [Nat.sub_zero]
    rw [add_comm]
  have hlead : (C (h.coeff 0) * Polynomial.Chebyshev.T ℝ (n : ℕ)).degree =
      (n : WithBot ℕ) := by
    rw [degree_C_mul hzero, Polynomial.Chebyshev.degree_T]
    simp
  have htail : q.degree < (n : WithBot ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < n)).mpr
    intro r _
    by_cases hr : h.coeff (r + 1) = 0
    · simp [hr]
    · rw [degree_C_mul hr, Polynomial.Chebyshev.degree_T]
      simp only [Int.natAbs_natCast]
      exact_mod_cast (Nat.sub_lt hnpos (Nat.succ_pos r))
  rw [hsplit, degree_add_eq_left_of_degree_lt (htail.trans_eq hlead.symm), hlead]

theorem amplitudePolynomial_natDegree (h : ℝ[X]) {n : ℕ}
    (hn : h.natDegree < n) (hzero : h.coeff 0 ≠ 0) :
    (amplitudePolynomial h n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (amplitudePolynomial_degree h hn hzero)

end Erdos1132.Counterexample
