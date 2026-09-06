import Erdos1132

/-! Exact statements and axiom checks for the formalized parts of Section 7.
The analytic premises in the assembly lemma remain visible in its type;
this module contains no claim that Theorem 2 has been fully formalized. -/

open Set Filter MeasureTheory Polynomial
open scoped BigOperators

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
