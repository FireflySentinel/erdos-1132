import Erdos1132.Counterexample.AmplitudeRoots

/-!
# Lagrange formulas for the constructed amplitude rows

The amplitude polynomial factors over its constructed roots. Cancellation of
its leading coefficient gives the exact Lebesgue-function formula.
-/

noncomputable section

open Set Polynomial Finset Filter
open scoped BigOperators

namespace Erdos1132.Counterexample

set_option maxHeartbeats 600000 in
theorem polynomial_eq_leadingCoeff_mul_nodal {n : ℕ} (Y : Nodes n) {P : ℝ[X]}
    (hdeg : P.natDegree ≤ n) (hroot : ∀ i, P.eval (Y.point i) = 0) :
    P = C P.leadingCoeff * Y.nodePolynomial := by
  have hdvd : Y.nodePolynomial ∣ P := by
    unfold Nodes.nodePolynomial Lagrange.nodal
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C Y.injective hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.mpr (hroot i)
  have hm : Y.nodePolynomial.Monic := Polynomial.monic_prod_X_sub_C Y.point univ
  have hn : P.natDegree ≤ Y.nodePolynomial.natDegree := by
    simpa [Nodes.nodePolynomial, Lagrange.natDegree_nodal] using hdeg
  exact Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hm hdvd hn

/-- The cardinal polynomial written using any nonzero degree-`n` polynomial
vanishing at the row's `n` nodes. -/
theorem cardinal_eq_polynomial_quotient {n : ℕ} (Y : Nodes n) {P : ℝ[X]}
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ n) (hroot : ∀ i, P.eval (Y.point i) = 0)
    {x : ℝ} (i : Fin n) (hx : x ≠ Y.point i) :
    (Y.cardinal i).eval x = P.eval x / (P.derivative.eval (Y.point i) * (x - Y.point i)) := by
  have hfac := polynomial_eq_leadingCoeff_mul_nodal Y hdeg hroot
  have hvalue : P.eval x = P.leadingCoeff * Y.nodePolynomial.eval x := by
    conv_lhs => rw [hfac]
    simp
  have hder : P.derivative.eval (Y.point i) =
      P.leadingCoeff * Y.nodePolynomial.derivative.eval (Y.point i) := by
    conv_lhs => rw [hfac]
    simp
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hd : Y.nodePolynomial.derivative.eval (Y.point i) ≠ 0 := by
    have hw := Y.weight_ne_zero i
    intro hz
    rw [Y.weight_eq_derivative, hz, inv_zero] at hw
    exact hw rfl
  change (Lagrange.basis univ Y.point i).eval x = _
  rw [Lagrange.eval_basis_not_at_node (mem_univ i) hx]
  change Y.nodePolynomial.eval x * (Y.weight i * (x - Y.point i)⁻¹) = _
  rw [Y.weight_eq_derivative, hvalue, hder]
  field_simp

theorem lebesgue_eq_polynomial_derivative_sum {n : ℕ} (Y : Nodes n) {P : ℝ[X]}
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ n) (hroot : ∀ i, P.eval (Y.point i) = 0)
    {x : ℝ} (hx : ∀ i, x ≠ Y.point i) :
    Y.lebesgue x = |P.eval x| *
      ∑ i : Fin n, 1 / (|P.derivative.eval (Y.point i)| * |x - Y.point i|) := by
  rw [Nodes.lebesgue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cardinal_eq_polynomial_quotient Y hP hdeg hroot i (hx i), abs_div, abs_mul]
  ring

/-- All roots of the amplitude polynomial are precisely the nodes of the
constructed row, and the Lebesgue function has the exact angular formula. -/
theorem eventually_exists_amplitude_rows (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ⊤ ψ ∧ ψ 0 = 0 ∧ ψ Real.pi = 0 ∧
      ∀ᶠ n : ℕ in atTop, ∃ Y : Nodes n, ∃ θ : Fin n → ℝ,
        (∀ i, θ i ∈ Set.Ioo 0 Real.pi ∧ Y.point i = Real.cos (θ i) ∧
          Y.point i ∈ Set.Ioo (-1) 1) ∧
        (∀ x : ℝ, (amplitudePolynomial h n).eval x = 0 ↔ ∃ i, x = Y.point i) ∧
        (∀ i, (amplitudePolynomial h n).derivative.eval (Y.point i) ≠ 0) ∧
        ∀ t : ℝ, (∀ i, Real.cos t ≠ Y.point i) →
          Y.lebesgue (Real.cos t) =
            ‖(complexPolynomial h).eval (circlePoint t)‖ * |Real.cos (n * t - ψ t)| *
              ∑ i : Fin n, Real.sin (θ i) /
                (‖(complexPolynomial h).eval (circlePoint (θ i))‖ *
                  (n - deriv ψ (θ i)) * |Real.cos t - Y.point i|) := by
  obtain ⟨ψ, hψc, hψ0, hψπ, hid, hrows⟩ := eventually_exists_amplitude_roots h hzero hpos
  refine ⟨ψ, hψc, hψ0, hψπ, ?_⟩
  filter_upwards [hrows] with n hn
  obtain ⟨hdeg, θ, hθ, hinj, hphase, hroot, hp, hw, hsimple⟩ := hn
  let Y : Nodes n := ⟨fun i => Real.cos (θ i), hinj, fun i => Real.cos_mem_Icc _⟩
  have hnd : (amplitudePolynomial h n).natDegree ≤ n :=
    (amplitudePolynomial_natDegree h hdeg hpos.ne').le
  have hP : amplitudePolynomial h n ≠ 0 := by
    intro hz
    have hdegree := amplitudePolynomial_degree h hdeg hpos.ne'
    rw [hz, Polynomial.degree_zero] at hdegree
    exact WithBot.bot_ne_coe hdegree
  have hfac := polynomial_eq_leadingCoeff_mul_nodal Y hnd hroot
  refine ⟨Y, θ, ?_, ?_, hsimple, ?_⟩
  · intro i
    refine ⟨hθ i, rfl, ?_, ?_⟩
    · simpa [Y] using Real.cos_lt_cos_of_nonneg_of_le_pi (hθ i).1.le le_rfl (hθ i).2
    · simpa [Y] using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (hθ i).2.le (hθ i).1
  · intro x
    rw [hfac, Polynomial.eval_mul, Polynomial.eval_C, mul_eq_zero]
    simp only [Polynomial.leadingCoeff_ne_zero.mpr hP, false_or]
    simp [Nodes.nodePolynomial, Lagrange.nodal, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]
  · intro t ht
    rw [lebesgue_eq_polynomial_derivative_sum Y hP hnd hroot ht]
    have hphaseid : (amplitudePolynomial h n).eval (Real.cos t) =
        ‖(complexPolynomial h).eval (circlePoint t)‖ * Real.cos (n * t - ψ t) := by
      exact hid n hdeg t
    rw [hphaseid, abs_mul, abs_of_nonneg (norm_nonneg _)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change 1 / (|(amplitudePolynomial h n).derivative.eval (Real.cos (θ i))| * _) = _
    rw [hw i]
    have hs : Real.sin (θ i) ≠ 0 := (Real.sin_pos_of_mem_Ioo (hθ i)).ne'
    field_simp

end Erdos1132.Counterexample
