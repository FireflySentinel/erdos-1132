import Erdos1132.AdditiveMain

/-! Theorem 1 and the set corollary, with the node conditions and Lebesgue
function written out. Every denominator involves two distinct nodes. -/

open MeasureTheory Set Filter
open scoped BigOperators

example (X : ∀ n : ℕ, Fin (n + 2) → ℝ)
    (distinct : ∀ n, Function.Injective (X n))
    (in_interval : ∀ n i, X n i ∈ Icc (-1) 1) :
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1),
      ((2 / Real.pi : ℝ) : EReal) ≤
        limsup (fun n =>
          (((∑ i : Fin (n + 2),
            |∏ j ∈ Finset.univ.erase i, (x - X n j) / (X n i - X n j)|) /
            Real.log (n + 2 : ℝ) : ℝ) : EReal)) atTop := by
  simpa only [Erdos1132.Nodes.lebesgue, Erdos1132.Nodes.cardinal,
    Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Erdos1132.rowSize, div_eq_mul_inv, mul_comm] using
    Erdos1132.ae_lebesgue_limsup_shifted
      (fun n => ⟨X n, distinct n, in_interval n⟩)

/-! The set corollary: every sufficiently large row exceeds the bound somewhere in `E`. -/
example (X : ∀ n : ℕ, Fin (n + 2) → ℝ)
    (distinct : ∀ n, Function.Injective (X n))
    (in_interval : ∀ n i, X n i ∈ Icc (-1) 1)
    (E : Set ℝ) (hE : MeasurableSet E) (hEint : E ⊆ Ioo (-1) 1)
    (hEpos : 0 < volume E) (c : ℝ) (hc : 0 < c) (hcπ : c < 2 / Real.pi) :
    ∀ᶠ (n : ℕ) in atTop, ∃ x ∈ E,
      c * Real.log (n + 2 : ℝ) <
        ∑ i : Fin (n + 2),
          |∏ j ∈ Finset.univ.erase i, (x - X n j) / (X n i - X n j)| := by
  simpa only [Erdos1132.Nodes.lebesgue, Erdos1132.Nodes.cardinal,
    Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Erdos1132.rowSize, div_eq_mul_inv, mul_comm] using
    Erdos1132.eventually_exists_lower_bound
      (fun n => ⟨X n, distinct n, in_interval n⟩) hc hcπ hE
      (fun x hx => ⟨(hEint hx).1.le, (hEint hx).2.le⟩) hEpos

/-- Both conclusions of Theorem 1 with exactly `n` nodes in row `n`. -/
example (X : ∀ n : ℕ, Fin n → ℝ)
    (distinct : ∀ n, Function.Injective (X n))
    (in_interval : ∀ n i, X n i ∈ Icc (-1) 1) :
    Dense {x : Ioo (-1 : ℝ) 1 | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
      (2 / Real.pi) * Real.log (n : ℝ) - C <
        ∑ i : Fin n,
          |∏ j ∈ Finset.univ.erase i, ((x : ℝ) - X n j) / (X n i - X n j)|} ∧
    (∀ᵐ x ∂volume.restrict (Ioo (-1) 1),
      ((2 / Real.pi : ℝ) : EReal) ≤
        limsup (fun n =>
          (((∑ i : Fin n,
            |∏ j ∈ Finset.univ.erase i, (x - X n j) / (X n i - X n j)|) /
            Real.log (n : ℝ) : ℝ) : EReal)) atTop) := by
  simpa only [Erdos1132.Nodes.lebesgue, Erdos1132.Nodes.cardinal,
    Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, div_eq_mul_inv, mul_comm] using
    Erdos1132.theorem1 (fun n => ⟨X n, distinct n, in_interval n⟩)
