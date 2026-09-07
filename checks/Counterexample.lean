import Erdos1132

/-! Exact statements and axiom checks for the Section 7 lemmas. -/

open Set Filter MeasureTheory Polynomial
open scoped BigOperators

/-- The contraction uses real powers with the paper's exact rational constants. -/
example : (254 / 255 : ℝ) * (8 / 7 : ℝ) ^ (1 / 256 : ℝ) ≤ 1 - 1 / 512 :=
  Erdos1132.Counterexample.contraction_factor_bound

/-- The scale estimate with the exponential choice of ρ written out. -/
example {A r : ℝ} (hA : 1 < A) (hr : 0 < r)
    (hsmall : r ≤ Real.exp (-1024 * (A + 40)) / 2) :
    16 ≤ Real.log (Real.exp 8 / r) ∧
      A + 2 < (1 / 512 : ℝ) * Real.log (1 / (4 * r)) - 32 :=
  ⟨Erdos1132.Counterexample.gapScale_log_parameter hA hr hsmall,
   Erdos1132.Counterexample.gapScale_lower_bound hA hr hsmall⟩

/-- The gap estimate for the explicit profile, with its integral written out. -/
example {r : ℝ → ℝ} {x s : ℝ}
    (hrm : Measurable r) (hx : x ∈ Icc (-1 : ℝ) 1)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hT : 16 ≤ 8 - Real.log s) (hrx : r x = s)
    (hr : ∀ y ∈ Icc (-1 : ℝ) 1, 0 ≤ r y ∧ r y ≤ 2)
    (hLip : ∀ y ∈ Icc (-1 : ℝ) 1, |r y - s| ≤ |x - y|)
    (hball : ∀ t ∈ Icc (4 * s) 2,
      ((volume.restrict (Icc (-1 : ℝ) 1)).restrict {y | r y ≠ 0}) {y | |x - y| ≤ t} ≤
        ENNReal.ofReal (127 / 128 : ℝ) *
          (volume.restrict (Icc (-1 : ℝ) 1)) {y | |x - y| ≤ t}) :
    let u : ℝ → ℝ := fun y => if r y = 0 then 0 else (8 - Real.log (r y)) ^ (-1 / 256 : ℝ)
    (1 / 512 : ℝ) * Real.log (1 / (4 * s)) - 32 ≤
      (∫ y in Icc (-1 : ℝ) 1, (u x - u y) / |x - y|) / u x := by
  exact Erdos1132.Counterexample.logarithmic_integral_lower_bound hrm hx hs hs4 hT hrx hr hLip hball

/-- The bound on `F`, with the explicit profile, cutoff index, and integral. -/
example {χ r : ℝ → ℝ} {A x δ : ℝ} {j : ℕ}
    (hj : 0 < j) (hx : x ∈ Icc (-1 : ℝ) 1)
    (hχm : Measurable χ) (hrm : Measurable r) (hδ : 0 < δ)
    (hχ : ∀ y ∈ Icc (-1 : ℝ) 1, 0 ≤ χ y ∧ χ y ≤ 1)
    (hzero : ∀ y ∈ Icc (-1 : ℝ) 1, |x - y| ≤ δ → χ y = 0)
    (hr : ∀ y ∈ Icc (-1 : ℝ) 1, 0 ≤ r y ∧ r y ≤ 2)
    (hdist : ∀ y ∈ Icc (-1 : ℝ) 1, r y ≤ |x - y|)
    (hA : ((⌈32 * (A + 1)⌉₊ + 64 * j * (2 * j) ^ 256 + j : ℕ) : ℝ) / 16 ≤
      ∫ y in Icc (-1 : ℝ) 1, χ y / |x - y|) :
    let u : ℝ → ℝ := fun y => if r y = 0 then 0 else (8 - Real.log (r y)) ^ (-1 / 256 : ℝ)
    let v : ℝ → ℝ := fun y => χ y * u y + (1 - χ y) * (1 / (j : ℝ))
    (A + 1) * v x ≤ ∫ y in Icc (-1 : ℝ) 1, (v x - v y) / |x - y| := by
  exact Erdos1132.Counterexample.explicit_smoothCutoff_lower_bound
    hj hx hχm hrm hδ hχ hzero hr hdist hA

/-- The positive approximation theorem, with the actual integral written out. -/
example {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (-1) 1) x)
    (hf' : ContinuousOn f' (Icc (-1 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Icc (-1 : ℝ) 1,
      0 < p.eval x ∧ |p.eval x - f x| < ε ∧
      |p.derivative.eval x - f' x| < ε ∧
      |(∫ y in Icc (-1 : ℝ) 1, (p.eval x - p.eval y) / |x - y|) / p.eval x -
        (∫ y in Icc (-1 : ℝ) 1, (f x - f y) / |x - y|) / f x| < ε := by
  exact Erdos1132.Counterexample.exists_positive_polynomial_C1_ratio_approximation
    hf hf' hpos hε

/-- Relative non-density, with the Lagrange product formula written out. -/
example (X : ∀ n : ℕ, Fin (n + 2) → ℝ)
    (distinct : ∀ n, Function.Injective (X n))
    (in_interval : ∀ n i, X n i ∈ Icc (-1) 1)
    {C b c : ℝ} (hbc : b < c) (hb : -1 ≤ b) (hc : c ≤ 1)
    (h : ∀ x ∈ Ioo b c, ∀ᶠ (n : ℕ) in atTop,
      (∑ i : Fin (n + 2),
        |∏ j ∈ Finset.univ.erase i, (x - X n j) / (X n i - X n j)|) ≤
          (2 / Real.pi) * Real.log (n + 2 : ℝ) - C) :
    ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
      (2 / Real.pi) * Real.log (n + 2 : ℝ) - C <
        ∑ i : Fin (n + 2),
          |∏ j ∈ Finset.univ.erase i, ((x : ℝ) - X n j) / (X n i - X n j)|} := by
  let Y : ∀ n : ℕ, Erdos1132.Nodes (n + 2) :=
    fun n => ⟨X n, distinct n, in_interval n⟩
  have hY : ∀ x ∈ Ioo b c, ∀ᶠ n in atTop,
      (Y n).lebesgue x ≤ (2 / Real.pi) * Real.log (n + 2 : ℝ) - C := by
    simpa only [Y, Erdos1132.Nodes.lebesgue, Erdos1132.Nodes.cardinal,
      Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
      div_eq_mul_inv, mul_comm] using h
  have hn := Erdos1132.Counterexample.not_dense_goodPoints_of_open_interval Y hbc hb hc hY
  simpa only [Erdos1132.Counterexample.goodPoints, Set.mem_ofPred_eq, Subtype.coe_prop,
    true_and, Y, Erdos1132.Nodes.lebesgue, Erdos1132.Nodes.cardinal,
    Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    div_eq_mul_inv, mul_comm] using hn

/--
info: 'Erdos1132.Counterexample.abs_logarithmicOperator_le_of_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Erdos1132.Counterexample.abs_logarithmicOperator_le_of_derivative

/-- info: 'Erdos1132.Counterexample.integrable_differenceKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.integrable_differenceKernel

/-- info: 'Erdos1132.Counterexample.logarithmicRatio_sub_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.logarithmicRatio_sub_bound

/-- info: 'Erdos1132.Counterexample.logarithmicOperator_local_eq_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.logarithmicOperator_local_eq_bound

/--
info: 'Erdos1132.Counterexample.exists_positive_polynomial_C1_ratio_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Erdos1132.Counterexample.exists_positive_polynomial_C1_ratio_approximation

/-- info: 'Erdos1132.Counterexample.gapRadius_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.gapRadius_lipschitz

/-- info: 'Erdos1132.Counterexample.amplitudePolynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.amplitudePolynomial_degree

/-- info: 'Erdos1132.Counterexample.fractional_power_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.fractional_power_bound

/-- info: 'Erdos1132.Counterexample.contraction_factor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.contraction_factor_bound

/-- info: 'Erdos1132.Counterexample.logarithmic_contraction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.logarithmic_contraction_bound

/-- info: 'Erdos1132.Counterexample.gapScale_log_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.gapScale_log_parameter

/-- info: 'Erdos1132.Counterexample.gapScale_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.gapScale_lower_bound

/-- info: 'Erdos1132.Counterexample.amplitudePolynomial_trig_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.amplitudePolynomial_trig_expansion

/-- info: 'Erdos1132.Counterexample.assembled_eventually_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.assembled_eventually_upper

/--
info: 'Erdos1132.Counterexample.not_dense_goodPoints_of_open_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Erdos1132.Counterexample.not_dense_goodPoints_of_open_interval

/-- info: 'Erdos1132.Counterexample.integral_radial_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.integral_radial_tail_le

/-- info: 'Erdos1132.Counterexample.integral_inverseDistance_annulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.integral_inverseDistance_annulus

/-- info: 'Erdos1132.Counterexample.logarithmic_integral_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.logarithmic_integral_lower_bound

/--
info: 'Erdos1132.Counterexample.logarithmic_integral_lower_bound_at_scale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Erdos1132.Counterexample.logarithmic_integral_lower_bound_at_scale

/-- info: 'Erdos1132.Counterexample.cutoffIndex_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.cutoffIndex_margin

/-- info: 'Erdos1132.Counterexample.explicit_smoothCutoff_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.explicit_smoothCutoff_lower_bound

/-- The constructed amplitude rows, with the polynomial and Lagrange products explicit. -/
example (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (h.map Complex.ofRealHom).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ⊤ ψ ∧ ψ 0 = 0 ∧ ψ Real.pi = 0 ∧
      ∀ᶠ n : ℕ in atTop, ∃ X : Fin n → ℝ, ∃ θ : Fin n → ℝ,
        Function.Injective X ∧
        (∀ i, θ i ∈ Ioo 0 Real.pi ∧ X i = Real.cos (θ i) ∧ X i ∈ Ioo (-1) 1) ∧
        (∀ x : ℝ,
          (∑ r ∈ Finset.range (h.natDegree + 1),
            h.coeff r * (Polynomial.Chebyshev.T ℝ (n - r : ℕ)).eval x) = 0 ↔ ∃ i, x = X i) ∧
        ∀ t : ℝ, (∀ i, Real.cos t ≠ X i) →
          (∑ i : Fin n, |∏ j ∈ Finset.univ.erase i,
            (Real.cos t - X j) / (X i - X j)|) =
            ‖(h.map Complex.ofRealHom).eval (Complex.exp ((t : ℂ) * Complex.I))‖ *
              |Real.cos (n * t - ψ t)| *
              ∑ i : Fin n, Real.sin (θ i) /
                (‖(h.map Complex.ofRealHom).eval (Complex.exp ((θ i : ℂ) * Complex.I))‖ *
                  (n - deriv ψ (θ i)) * |Real.cos t - X i|) := by
  obtain ⟨ψ, hc, h0, hπ, hrows⟩ :=
    Erdos1132.Counterexample.eventually_exists_amplitude_rows h hzero hpos
  refine ⟨ψ, hc, h0, hπ, ?_⟩
  filter_upwards [hrows] with n hn
  obtain ⟨Y, θ, hθ, hroots, _, hformula⟩ := hn
  refine ⟨Y.point, θ, Y.injective, hθ, ?_, ?_⟩
  · intro x
    simpa only [Erdos1132.Counterexample.amplitudePolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C] using hroots x
  · intro t ht
    simpa only [Erdos1132.Counterexample.complexPolynomial,
      Erdos1132.Counterexample.circlePoint, Erdos1132.Nodes.lebesgue,
      Erdos1132.Nodes.cardinal, Lagrange.basis, Lagrange.basisDivisor,
      Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv, mul_comm] using hformula t ht

/-- A common variation bound controls the quadrature error for every parameter and degree. -/
example {S : Type*} (R : ℕ → S → ℝ → ℝ) {V : ℝ}
    (hBV : ∀ n s, BoundedVariationOn (R n s) (Icc 0 Real.pi))
    (hi : ∀ n s, IntervalIntegrable (R n s) volume 0 Real.pi)
    (hV : ∀ n s, (eVariationOn (R n s) (Icc 0 Real.pi)).toReal ≤ V)
    (n : ℕ) (hn : 0 < n) (s : S) :
    |(Real.pi / n) * (∑ k ∈ Finset.range n,
        R n s (((k : ℝ) + 1 / 2) * (Real.pi / n))) -
        ∫ t in (0 : ℝ)..Real.pi, R n s t| ≤ Real.pi * V / n := by
  exact Erdos1132.Counterexample.uniform_midpoint_quadrature_error
    (R := fun p : ℕ × S => R p.1 p.2) Real.pi_pos.le
    (fun p => hBV p.1 p.2) (fun p => hi p.1 p.2) (fun p => hV p.1 p.2) (n, s) hn

/-- info: 'Erdos1132.Counterexample.exists_normalized_polynomial_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.exists_normalized_polynomial_log

/-- info: 'Erdos1132.Counterexample.exists_amplitude_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.exists_amplitude_phase

/-- info: 'Erdos1132.Counterexample.eventually_exists_amplitude_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.eventually_exists_amplitude_roots

/-- info: 'Erdos1132.Counterexample.cardinal_eq_polynomial_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.cardinal_eq_polynomial_quotient

/-- info: 'Erdos1132.Counterexample.eventually_exists_amplitude_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.eventually_exists_amplitude_rows

/-- info: 'Erdos1132.Counterexample.midpoint_quadrature_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.midpoint_quadrature_error_bound

/-- info: 'Erdos1132.Counterexample.uniform_midpoint_quadrature_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.uniform_midpoint_quadrature_error

/-- The complete Theorem 2, with distinct interior nodes and the Lagrange
products written out in the original degree convention. -/
example (M : ℝ) (hM : 0 < M) :
    ∃ X : ∀ n : ℕ, Fin n → ℝ,
      (∀ n, Function.Injective (X n)) ∧
      (∀ n i, X n i ∈ Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop,
        (∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, (x-X n j)/(X n i-X n j)|) ≤
          (2/Real.pi)*Real.log (n:ℝ)-M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 |
        ∃ᶠ (n : ℕ) in atTop, (2/Real.pi)*Real.log (n:ℝ)-C <
          ∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, ((x:ℝ)-X n j)/(X n i-X n j)|}) := by
  obtain ⟨X,hinternal,hupper,hnd⟩ := Erdos1132.Counterexample.theorem2_unshifted M hM
  refine ⟨fun n => (X n).point,fun n => (X n).injective,hinternal,?_,?_⟩
  · simpa only [Erdos1132.Nodes.lebesgue,Erdos1132.Nodes.cardinal,
      Lagrange.basis,Lagrange.basisDivisor,Polynomial.eval_prod,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,
      Polynomial.eval_X,div_eq_mul_inv,mul_comm] using hupper
  · simpa only [Erdos1132.Nodes.lebesgue,Erdos1132.Nodes.cardinal,
      Lagrange.basis,Lagrange.basisDivisor,Polynomial.eval_prod,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,
      Polynomial.eval_X,div_eq_mul_inv,mul_comm] using hnd

/-- info: 'Erdos1132.Counterexample.theorem2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.theorem2

/-- info: 'Erdos1132.Counterexample.theorem2_unshifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.theorem2_unshifted

/-- info: 'Erdos1132.Counterexample.exists_cantor_smooth_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1132.Counterexample.exists_cantor_smooth_sequence

/-- info: 'Erdos1132.Counterexample.exists_amplitude_logarithmicRatio_approximation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.Counterexample.exists_amplitude_logarithmicRatio_approximation

/-- info: 'Erdos1132.Counterexample.eventually_exists_amplitude_upper_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.Counterexample.eventually_exists_amplitude_upper_rows
