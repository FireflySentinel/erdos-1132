import Erdos1132.Shared.Cauchy
import Erdos1132.Shared.Chebyshev

/-! # Chebyshev approximation and signed Cauchy cancellation

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset

namespace Erdos1132.Nodes

variable {n : ℕ} (X : Nodes n)

theorem signedMass_cancellation_complex {p : ℂ[X]} (hp : p.degree < (n - 1 : ℕ)) :
    ∑ i, (X.signedMass i : ℂ) * p.eval (X.point i : ℂ) = 0 := by
  have hinj : Function.Injective (fun i => (X.point i : ℂ)) :=
    Complex.ofReal_injective.comp X.injective
  have hpn : p.degree < (n : ℕ) :=
    hp.trans_le (by exact_mod_cast Nat.sub_le n 1)
  have h := Lagrange.coeff_eq_sum hinj.injOn (s := univ) (P := p)
    (by simpa using hpn)
  have hc : p.coeff (n - 1) = 0 := Polynomial.coeff_eq_zero_of_degree_lt hp
  simp only [card_univ, Fintype.card_fin, hc] at h
  have hw : ∑ i, (X.weight i : ℂ) * p.eval (X.point i : ℂ) = 0 := by
    apply Eq.trans ?_ h.symm
    apply sum_congr rfl
    intro i _
    simp [weight, Lagrange.nodalWeight, prod_inv_distrib, div_eq_mul_inv, mul_comm]
  simp only [signedMass, Complex.ofReal_div, div_mul_eq_mul_div, ← sum_div, hw, zero_div]

/-- Polynomial cancellation applied to the divided difference at `z`. -/
theorem cauchy_polynomial_identity {p : ℂ[X]} (hp : p.degree ≤ (n - 1 : ℕ))
    {z : ℂ} (hz : ∀ i, z ≠ (X.point i : ℂ)) :
    p.eval z * X.signedCauchy z =
      ∑ i, (X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ) := by
  let q := p /ₘ (Polynomial.X - C z)
  have hq : q.degree < (n - 1 : ℕ) := by
    by_cases hp0 : p = 0
    · simp [q, hp0]
    · exact (degree_divByMonic_lt p (Polynomial.X - C z) hp0 (by simp)).trans_le hp
  have hc := X.signedMass_cancellation_complex hq
  have hi (i : Fin n) :
      (X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ) =
        p.eval z * ((X.signedMass i : ℂ) / (z - X.point i)) -
          (X.signedMass i : ℂ) * q.eval (X.point i : ℂ) := by
    have h := congrArg (Polynomial.eval (X.point i : ℂ))
      (modByMonic_add_div p (Polynomial.X - C z))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at h
    have hzi := sub_ne_zero.mpr (hz i)
    field_simp
    linear_combination -(X.signedMass i : ℂ) * h
  simp_rw [hi]
  rw [sum_sub_distrib, hc, sub_zero, ← mul_sum]
  rfl

theorem cauchy_polynomial_bound (hn : 0 < n) {p : ℂ[X]}
    (hp : p.degree ≤ (n - 1 : ℕ)) (hb : ∀ i, ‖p.eval (X.point i : ℂ)‖ ≤ 1)
    {z : ℂ} {h : ℝ} (hh : 0 < h) (hz : h ≤ |z.im|) :
    ‖p.eval z‖ * ‖X.signedCauchy z‖ ≤ 1 / h := by
  have hzn (i : Fin n) : h ≤ ‖z - (X.point i : ℂ)‖ := by
    exact hz.trans (by simpa using Complex.abs_im_le_norm (z - (X.point i : ℂ)))
  have hzne (i : Fin n) : z ≠ (X.point i : ℂ) := by
    intro he
    simpa [he] using hh.trans_le (hzn i)
  rw [← norm_mul, X.cauchy_polynomial_identity hp hzne]
  calc
    ‖∑ i, (X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ)‖
        ≤ ∑ i, ‖(X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, X.mass i / h := by
      apply sum_le_sum
      intro i _
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, X.abs_signedMass hn]
      calc
        X.mass i / ‖z - (X.point i : ℂ)‖ * ‖p.eval (X.point i : ℂ)‖
            ≤ X.mass i / ‖z - (X.point i : ℂ)‖ :=
          mul_le_of_le_one_right (div_nonneg (X.mass_pos hn i).le (norm_nonneg _)) (hb i)
        _ ≤ X.mass i / h :=
          div_le_div_of_nonneg_left (X.mass_pos hn i).le hh (hzn i)
    _ = 1 / h := by rw [← sum_div, X.sum_mass hn]

theorem cauchy_chebyshev_bound (hn : 2 ≤ n) {z : ℂ} {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hz : h ≤ |z.im|) :
    ‖X.signedCauchy z‖ ≤ 1 / (h * Real.sinh ((n - 1 : ℕ) * h / 2)) := by
  have hp : (Polynomial.Chebyshev.T ℂ (n - 1 : ℕ)).degree ≤ (n - 1 : ℕ) := by
    simp [Polynomial.Chebyshev.degree_T]
  have hb := X.cauchy_polynomial_bound (by omega) hp
    (fun i => chebyshev_norm_le_one (n - 1) (X.mem_interval i)) hh hz
  have hl := chebyshev_norm_lower (n - 1) hh.le hh1 hz
  have hs : 0 < Real.sinh ((n - 1 : ℕ) * h / 2) := by
    apply Real.sinh_pos_iff.mpr
    have hnn : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 0 < n - 1 by omega)
    positivity
  have hm := (mul_le_mul_of_nonneg_right hl (norm_nonneg (X.signedCauchy z))).trans hb
  rw [← div_div]
  apply (le_div_iff₀ hs).mpr
  simpa [mul_comm] using hm

theorem cancellation_ratio_bound (hn : 2 ≤ n) {h x : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (hx : x ∈ Set.Icc (-1) 1) :
    ‖X.signedCauchy ((x : ℂ) + h * Complex.I)‖ /
        (X.probability (by omega)).gamma h x ≤
      (4 + h ^ 2) / (h ^ 2 * Real.sinh ((n - 1 : ℕ) * h / 2)) := by
  have hg := (X.probability (by omega)).gamma_lower hh hx X.mem_interval
  have hb := X.cauchy_chebyshev_bound hn hh hh1
    (z := (x : ℂ) + h * Complex.I) (by simp [abs_of_pos hh])
  have hd : 0 < h / (4 + h ^ 2) := by positivity
  calc
    _ ≤ ‖X.signedCauchy ((x : ℂ) + h * Complex.I)‖ / (h / (4 + h ^ 2)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hd hg
    _ ≤ (1 / (h * Real.sinh ((n - 1 : ℕ) * h / 2))) / (h / (4 + h ^ 2)) :=
      div_le_div_of_nonneg_right hb hd.le
    _ = _ := by field_simp

end Erdos1132.Nodes
