import Erdos1132.Counterexample.OuterPolynomial
import Erdos1132.Counterexample.AmplitudeWeight

/-!
# Reciprocal positive polynomials as zero-free amplitudes

Multiplication by a power of `z` turns `q((z + z⁻¹)/2)` into a real
polynomial. Reflection of its interior roots preserves the boundary modulus.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Polynomial Complex Finset Set
open scoped ComplexConjugate BigOperators

namespace Erdos1132.Counterexample

def joukowskyPolynomial (q : ℝ[X]) : ℝ[X] :=
  ∑ j ∈ range (q.natDegree+1),
    C (q.coeff j/(2:ℝ)^j) * X^(q.natDegree-j) * (X^2+1)^j

theorem joukowskyPolynomial_eval_circle (q : ℝ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    (complexPolynomial (joukowskyPolynomial q)).eval z =
      z^q.natDegree * ((q.eval z.re : ℝ) : ℂ) := by
  have hzprod : z*conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hzsum : z+conj z = 2*(z.re : ℂ) := by simpa using Complex.add_conj z
  have hid : z^2+1 = (2*(z.re : ℂ))*z := by
    linear_combination z*hzsum-hzprod
  rw [complexPolynomial, joukowskyPolynomial, Polynomial.map_sum, Polynomial.eval_finsetSum]
  have hq : ((q.eval z.re : ℝ) : ℂ) =
      ∑ j ∈ range (q.natDegree+1), (q.coeff j : ℂ)*(z.re : ℂ)^j := by
    rw [q.eval_eq_sum_range]
    push_cast
    rfl
  rw [hq, Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjd : j ≤ q.natDegree := by have := mem_range.mp hj; omega
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_add, Polynomial.map_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one,
    Complex.ofRealHom_eq_coe, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [hid, mul_pow, mul_pow]
  have hpow : z^(q.natDegree-j)*z^j = z^q.natDegree := by
    rw [← pow_add, Nat.sub_add_cancel hjd]
  calc
    _ = (q.coeff j : ℂ)*(z.re : ℂ)^j*(z^(q.natDegree-j)*z^j) := by field_simp
    _ = _ := by rw [hpow]; ring

theorem realPart_mem_unit_interval {z : ℂ} (hz : ‖z‖ ≤ 1) : z.re ∈ Set.Icc (-1) 1 := by
  have hh := (Complex.abs_re_le_norm z).trans hz
  exact abs_le.mp hh

/-- Every reciprocal of a polynomial positive on `[-1,1]` is exactly the
amplitude of a real polynomial zero-free on the closed unit disk. -/
theorem exists_polynomial_reciprocal_amplitude (q : ℝ[X])
    (hq : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 < q.eval x) :
    ∃ h : ℝ[X], 0 < h.coeff 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, amplitudeWeight h x = (q.eval x)⁻¹ := by
  have hJ : ∀ z : ℂ, ‖z‖ = 1 → (complexPolynomial (joukowskyPolynomial q)).eval z ≠ 0 := by
    intro z hz
    rw [joukowskyPolynomial_eval_circle q hz]
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
    apply mul_ne_zero (pow_ne_zero _ hz0)
    exact Complex.ofReal_ne_zero.mpr (hq _ (realPart_mem_unit_interval hz.le)).ne'
  obtain ⟨h, hh0, hhzero, hhnorm⟩ := exists_real_outer_polynomial (joukowskyPolynomial q) hJ
  refine ⟨h, hh0, hhzero, ?_⟩
  intro x hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have hcircle : (circlePoint (Real.arccos x)).re = x := by
    simp [circlePoint, Complex.exp_re, hcos]
  have hh := hhnorm (circlePoint (Real.arccos x)) (norm_circlePoint _)
  rw [joukowskyPolynomial_eval_circle q (norm_circlePoint _), norm_mul, norm_pow,
    norm_circlePoint, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
    hcircle, abs_of_pos (hq x hx)] at hh
  rw [← hcos, amplitudeWeight_cos, hh, hcos]

end Erdos1132.Counterexample
