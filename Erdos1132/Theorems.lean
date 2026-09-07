import Erdos1132.Additive.Main
import Erdos1132.AlmostEverywhere.Main
import Erdos1132.Counterexample.Corollaries

/-! # Main theorems and consequences

Paper: Theorems 1 and 2 (§1) and the two corollaries in §8.

`Nodes n` records `n` distinct nodes in `[-1, 1]`; `Nodes.lebesgue` is
the sum of the absolute values of their Lagrange cardinal polynomials.
The statements in this file use the paper's convention of `n` nodes in row `n`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Erdos1132

/-- Theorem 1: a dense set with point-dependent additive constants, and the
sharp normalized lower bound almost everywhere, for every triangular array. -/
theorem theorem1 (X : ∀ n, Nodes n) :
    Dense {x : Ioo (-1 : ℝ) 1 | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
      (2 / Real.pi) * Real.log n - C < (X n).lebesgue x} ∧
    (∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
      ((2 / Real.pi : ℝ) : EReal) ≤
        limsup (fun n => (((X n).lebesgue x / Real.log (n : ℝ) : ℝ) : EReal)) atTop) :=
  ⟨dense_additive_lower_bound X, ae_lebesgue_limsup X⟩

/-- Theorem 2: one array has the prescribed eventual deficit at every fixed
interior point, and every finite-constant good-point set is non-dense. -/
theorem theorem2 (M : ℝ) (hM : 0 < M) :
    ∃ X : ∀ n : ℕ, Nodes n,
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ n in atTop,
        (X n).lebesgue x ≤ (2 / Real.pi) * Real.log (n : ℝ) - M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x}) :=
  Counterexample.theorem2 M hM

/-- The positive-measure corollary (§8): each fixed measurable set of positive
measure contains a point exceeding `c log n` in every sufficiently large row. -/
theorem positive_measure_lower_bound (X : ∀ n, Nodes n) {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : E ⊆ Ioo (-1 : ℝ) 1) (hEpos : 0 < volume E)
    {c : ℝ} (hc : 0 < c) (hcπ : c < 2 / Real.pi) :
    ∀ᶠ (n : ℕ) in atTop, ∃ x ∈ E, c * Real.log (n : ℝ) < (X n).lebesgue x :=
  eventually_exists_lower_bound_unshifted X hc hcπ hE
    (hEint.trans Ioo_subset_Icc_self) hEpos

/-- The interval-constant corollary (§8), for the same array as both assertions
of Theorem 2: no constant works on all compact interior intervals, even when
the starting row may depend on the interval. -/
theorem no_uniform_interval_constant (M : ℝ) (hM : 0 < M) :
    ∃ X : ∀ n : ℕ, Nodes n,
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ n in atTop,
        (X n).lebesgue x ≤ (2 / Real.pi) * Real.log (n : ℝ) - M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x}) ∧
      (¬∃ C : ℝ, ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 →
        ∀ᶠ (n : ℕ) in atTop, (2 / Real.pi) * Real.log (n : ℝ) - C ≤
          sSup ((X n).lebesgue '' Icc l r)) := by
  obtain ⟨X, hI, hupper, hnd⟩ := theorem2 M hM
  exact ⟨X, hI, hupper, hnd, Counterexample.no_uniform_interval_constant X hnd⟩

end Erdos1132
