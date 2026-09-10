import Erdos1132.Counterexample.AmplitudePhase
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Reflecting polynomial zeros across the unit circle

Each interior zero is replaced by its conjugate reciprocal through the
factor `1 - conj(r) z`. This preserves the modulus on the unit circle,
including the case `r = 0`, and gives a polynomial nonvanishing on the disk.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Polynomial Complex Set
open scoped ComplexConjugate

namespace Erdos1132.Counterexample

def reflectedFactor (r : ℂ) : ℂ[X] :=
  if ‖r‖ < 1 then 1 - C (conj r)*X else X-C r

def outerPolynomial (P : ℂ[X]) : ℂ[X] :=
  C P.leadingCoeff * (P.roots.map reflectedFactor).prod

theorem reflectedFactor_zero_free {r z : ℂ}
    (hr : ‖r‖ ≠ 1) (hz : ‖z‖ ≤ 1) : (reflectedFactor r).eval z ≠ 0 := by
  by_cases hri : ‖r‖ < 1
  · simp only [reflectedFactor, if_pos hri, eval_sub, eval_one, eval_mul, eval_C, eval_X]
    intro he
    have heq : conj r*z = 1 := by linear_combination -he
    have hn := congrArg norm heq
    rw [norm_mul, norm_conj, norm_one] at hn
    have hh : ‖r‖*‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans_lt (by simpa using hri)
    linarith
  · simp only [reflectedFactor, if_neg hri, eval_sub, eval_X, eval_C, sub_ne_zero]
    intro he
    have hro : 1 < ‖r‖ := lt_of_le_of_ne (le_of_not_gt hri) hr.symm
    rw [he] at hz
    linarith

theorem reflectedFactor_norm_circle (r : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(reflectedFactor r).eval z‖ = ‖z-r‖ := by
  by_cases hri : ‖r‖ < 1
  · simp only [reflectedFactor, if_pos hri, eval_sub, eval_one, eval_mul, eval_C, eval_X]
    have hzprod : z*conj z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
      norm_num
    have hid : 1-conj r*z = z*conj (z-r) := by
      rw [map_sub]
      linear_combination -hzprod
    rw [hid, norm_mul, norm_conj, hz, one_mul]
  · simp [reflectedFactor, hri]

theorem reflectedFactor_map_conj (r : ℂ) :
    (reflectedFactor r).map (starRingEnd ℂ) = reflectedFactor (conj r) := by
  by_cases hr : ‖r‖ < 1 <;> simp [reflectedFactor, hr, Polynomial.map_sub, Polynomial.map_mul]

theorem outerPolynomial_zero_free {P : ℂ[X]}
    (hP : ∀ z : ℂ, ‖z‖ = 1 → P.eval z ≠ 0)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : (outerPolynomial P).eval z ≠ 0 := by
  have hP0 : P ≠ 0 := by intro he; simpa [he] using hP 1 (by simp)
  rw [outerPolynomial, eval_mul, eval_C, eval_multiset_prod]
  apply mul_ne_zero (leadingCoeff_ne_zero.mpr hP0)
  apply Multiset.prod_ne_zero
  intro hw
  obtain ⟨f, hf, he⟩ := Multiset.mem_map.mp hw
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hf
  apply reflectedFactor_zero_free (z := z) _ hz he
  intro hnorm
  exact hP r hnorm ((mem_roots hP0).mp hr)

theorem outerPolynomial_norm_circle (P : ℂ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(outerPolynomial P).eval z‖ = ‖P.eval z‖ := by
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.splits P).natDegree_eq_card_roots.symm
  conv_rhs => rw [← hfac]
  simp only [outerPolynomial, eval_mul, eval_C, eval_multiset_prod, norm_mul,
    Multiset.map_map]
  congr 1
  induction P.roots using Multiset.induction_on with
  | empty => simp
  | @cons r S hS =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Function.comp_apply,
      reflectedFactor_norm_circle r hz, eval_sub, eval_X, eval_C]
    congr 1
    simpa only [Function.comp_apply, eval_sub, eval_X, eval_C] using hS


theorem outerPolynomial_map_conj (P : ℂ[X]) :
    (outerPolynomial P).map (starRingEnd ℂ) = outerPolynomial (P.map (starRingEnd ℂ)) := by
  have hroots := (IsAlgClosed.splits P).roots_map_of_injective (starRingEnd ℂ).injective
  simp only [outerPolynomial, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_multiset_prod, Polynomial.leadingCoeff_map_of_injective
      (starRingEnd ℂ).injective, hroots, Multiset.map_map]
  congr 2
  apply Multiset.map_congr rfl
  intro r _
  exact reflectedFactor_map_conj r

theorem exists_real_polynomial_of_map_conj {P : ℂ[X]}
    (hP : P.map (starRingEnd ℂ) = P) : ∃ q : ℝ[X], complexPolynomial q = P := by
  apply (Polynomial.mem_lifts P).mp
  apply (Polynomial.lifts_iff_coeff_lifts P).mpr
  intro n
  have hh := congrArg (fun Q : ℂ[X] => Q.coeff n) hP
  rw [coeff_map] at hh
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hh
  exact ⟨r, hr.symm⟩

@[simp] theorem complexPolynomial_map_conj (P : ℝ[X]) :
    (complexPolynomial P).map (starRingEnd ℂ) = complexPolynomial P := by
  ext n
  simp [complexPolynomial]

/-- Reflection preserves real coefficients and boundary modulus, while
moving all zeros out of the closed unit disk. -/
theorem exists_real_outer_polynomial (P : ℝ[X])
    (hP : ∀ z : ℂ, ‖z‖ = 1 → (complexPolynomial P).eval z ≠ 0) :
    ∃ h : ℝ[X], 0 < h.coeff 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0) ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖(complexPolynomial h).eval z‖ = ‖(complexPolynomial P).eval z‖ := by
  have hc : (outerPolynomial (complexPolynomial P)).map (starRingEnd ℂ) =
      outerPolynomial (complexPolynomial P) := by rw [outerPolynomial_map_conj, complexPolynomial_map_conj]
  obtain ⟨q, hq⟩ := exists_real_polynomial_of_map_conj hc
  have hqzero (z : ℂ) (hz : ‖z‖ ≤ 1) : (complexPolynomial q).eval z ≠ 0 := by
    rw [hq]
    exact outerPolynomial_zero_free hP hz
  have hqnorm (z : ℂ) (hz : ‖z‖ = 1) :
      ‖(complexPolynomial q).eval z‖ = ‖(complexPolynomial P).eval z‖ := by
    rw [hq]
    exact outerPolynomial_norm_circle _ hz
  have hq0 : q.coeff 0 ≠ 0 := by
    have hh := hqzero 0 (by simp)
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [complexPolynomial] using hh
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · refine ⟨-q, by simpa using neg_pos.mpr hneg, ?_, ?_⟩
    · intro z hz
      simpa [complexPolynomial] using hqzero z hz
    · intro z hz
      simpa [complexPolynomial] using hqnorm z hz
  · exact ⟨q, hpos, hqzero, hqnorm⟩

end Erdos1132.Counterexample
