import Erdos1132.Theorems

/-! The corollaries in main §7 and companion §5, with the Lagrange products written out. -/

open MeasureTheory Set Filter
open scoped BigOperators

/-- The set corollary with exactly `n` nodes in row `n`. -/
example (X : ∀ n : ℕ, Fin n → ℝ)
    (distinct : ∀ n, Function.Injective (X n))
    (in_interval : ∀ n i, X n i ∈ Icc (-1) 1)
    (E : Set ℝ) (hE : MeasurableSet E) (hEint : E ⊆ Ioo (-1) 1)
    (hEpos : 0 < volume E) (c : ℝ) (hc : 0 < c) (hcπ : c < 2 / Real.pi) :
    ∀ᶠ (n : ℕ) in atTop, ∃ x ∈ E,
      c * Real.log (n : ℝ) <
        ∑ i : Fin n,
          |∏ j ∈ Finset.univ.erase i, (x - X n j) / (X n i - X n j)| := by
  simpa only [Erdos1132.Nodes.lebesgue, Erdos1132.Nodes.cardinal,
    Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, div_eq_mul_inv, mul_comm] using
    Erdos1132.positive_measure_lower_bound
      (fun n => ⟨X n, distinct n, in_interval n⟩) hE hEint hEpos hc hcπ

/-- The array of the companion note's Theorem 1 admits no additive constant uniform over interior intervals. -/
example (M : ℝ) (hM : 0 < M) :
    ∃ X : ∀ n : ℕ, Erdos1132.Nodes n,
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ n in atTop,
        (X n).lebesgue x ≤ (2 / Real.pi) * Real.log (n : ℝ) - M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x}) ∧
      ¬∃ C : ℝ, ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 →
        ∀ᶠ (n : ℕ) in atTop, (2 / Real.pi) * Real.log (n : ℝ) - C ≤
          sSup ((fun x => ∑ i : Fin n,
            |∏ j ∈ Finset.univ.erase i,
              (x - (X n).point j) / ((X n).point i - (X n).point j)|) '' Icc l r) := by
  obtain ⟨X, hI, hupper, hnd, hinterval⟩ := Erdos1132.no_uniform_interval_constant M hM
  refine ⟨X, hI, hupper, hnd, ?_⟩
  have hL (n : ℕ) : (fun x => ∑ i : Fin n,
      |∏ j ∈ Finset.univ.erase i,
        (x - (X n).point j) / ((X n).point i - (X n).point j)|) = (X n).lebesgue := by
    funext x
    simp only [Erdos1132.Nodes.lebesgue, Erdos1132.Nodes.cardinal,
      Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, div_eq_mul_inv, mul_comm]
  simp_rw [hL]
  exact hinterval
