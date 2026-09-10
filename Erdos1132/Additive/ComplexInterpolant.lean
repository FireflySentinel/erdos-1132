import Erdos1132.Additive.TaoPotential

/-! # Complex growth of interpolants with bounded nodal data

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Finset Set Complex
open scoped BigOperators
namespace Erdos1132.Nodes
variable {n : ℕ} (X : Erdos1132.Nodes n)

def interpolant (a : Fin n → ℝ) : ℝ[X] := ∑ i, C (a i)*X.cardinal i

theorem degree_interpolant_lt (a : Fin n → ℝ) : (X.interpolant a).degree < n := by
  simpa only [Lagrange.interpolate_apply, interpolant, cardinal, card_univ, Fintype.card_fin]
    using Lagrange.degree_interpolate_lt (s := Finset.univ) a X.injective.injOn

theorem interpolant_eval_le (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) (x : ℝ) :
    |(X.interpolant a).eval x| ≤ X.lebesgue x := by
  simp only [interpolant, eval_finsetSum, eval_mul, eval_C]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)

theorem nodePolynomial_eval₂_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) z ≠ 0 := by
  simp only [nodePolynomial, Lagrange.nodal, eval₂_finsetProd, eval₂_sub, eval₂_X, eval₂_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ he
  have h := congrArg Complex.im he
  apply hz
  simpa using h

theorem cardinal_eval₂_identity (i : Fin n) (z : ℂ) :
    (z-X.point i)*(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z =
      X.weight i*X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) z := by
  have he := congrArg (fun P : ℝ[X] => P.eval₂ (algebraMap ℝ ℂ) z) (X.cardinal_mul_linear i)
  simpa only [eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] using! he

theorem interpolant_complex_bound (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) z‖ ≤
      X.totalWeight*‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) z‖/z.im := by
  apply (le_div_iff₀ hz).mpr
  have hsum : ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) z‖ ≤
      ∑ i, ‖(a i : ℂ)*(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖ := by
    simp only [interpolant, eval₂_finsetSum, eval₂_mul, eval₂_C]
    simpa only using! (norm_sum_le (s := Finset.univ)
      (f := fun i => (algebraMap ℝ ℂ) (a i)*(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z))
  have ht := mul_le_mul_of_nonneg_right hsum hz.le
  apply ht.trans
  rw [sum_mul]
  unfold totalWeight
  rw [sum_mul]
  apply sum_le_sum
  intro i _
  have he := congrArg norm (X.cardinal_eval₂_identity i z)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at he
  have hi : z.im ≤ ‖z-(X.point i : ℂ)‖ := by
    simpa only [sub_im, ofReal_im, sub_zero] using Complex.im_le_norm (z-(X.point i : ℂ))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |a i| * ‖(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖*z.im ≤
        ‖(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖*z.im := by
      have hm := mul_le_mul_of_nonneg_right (ha i)
        (mul_nonneg (norm_nonneg ((X.cardinal i).eval₂ (algebraMap ℝ ℂ) z)) hz.le)
      simpa only [mul_assoc, one_mul] using hm
    _ ≤ ‖z-(X.point i : ℂ)‖*‖(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖ := by
      nlinarith [norm_nonneg ((X.cardinal i).eval₂ (algebraMap ℝ ℂ) z)]
    _ = _ := he

theorem normalized_complex_polynomial (hn : 0 < n) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    X.totalWeight*‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ =
      Real.exp ((n : ℝ)*(X.potentialNormalization-X.complexLogPotential x h)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hp : 0 < ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ := by
    apply norm_pos_iff.mpr
    apply X.nodePolynomial_eval₂_ne_zero
    simpa using hh.ne'
  rw [X.complexLogPotential_eq_polynomial hh, potentialNormalization]
  have he : (n : ℝ)*(Real.log X.totalWeight/n -
      -Real.log ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖/n) =
      Real.log X.totalWeight+Real.log ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ := by
    field_simp
    ring
  rw [he, Real.exp_add, Real.exp_log (X.totalWeight_pos hn), Real.exp_log hp]

end Erdos1132.Nodes

namespace Erdos1132

theorem uniform_complex_interpolant_growth {l r d : ℝ} (hlr : l < r)
    (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc l r, X.lebesgue y ≤ n) →
      ∀ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) →
      ∀ x ∈ Icc (l+d) (r-d), ∀ h : ℝ, 1/(n : ℝ) ≤ h →
        ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ ≤
          Real.exp (Real.pi*n*h*X.exteriorDensity l r X.potentialNormalization x 0+
            C*(1+Real.log n+n*h^3))/h := by
  obtain ⟨C, hC, hpot⟩ := uniform_complex_potential_expansion hlr hI hd
  refine ⟨C, hC, ?_⟩
  intro n X hn hΛ a ha x hx h hh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hh0 : 0 < h := (one_div_pos.mpr hnR).trans_le hh
  have hg := X.interpolant_complex_bound a ha (z := (x : ℂ)+h*I) (by simpa using hh0)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
    mul_zero, add_zero, zero_add] at hg
  rw [X.normalized_complex_polynomial hn hh0] at hg
  apply hg.trans
  apply div_le_div_of_nonneg_right _ hh0.le
  apply Real.exp_le_exp.mpr
  have hp := (abs_le.mp (hpot n X hn hΛ x hx h hh)).1
  have hm := mul_le_mul_of_nonneg_left hp hnR.le
  have he : (n : ℝ)*potentialErrorSize n = 1+Real.log n := by
    unfold potentialErrorSize
    field_simp
  nlinarith

end Erdos1132
