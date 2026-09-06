import Erdos1132.Main

/-! Theorem 1(ii), with the node conditions and Lebesgue function written out.
Row `n` has `n + 2` distinct nodes in `[-1, 1]`. The product formula is also
defined at the nodes: every denominator involves two distinct nodes. -/

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
