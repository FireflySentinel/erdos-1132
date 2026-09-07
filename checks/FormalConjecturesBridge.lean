import Erdos1132

/-! # Explicit statements for Erdős Problem 1132

The main theorems imply the nested-sequence assertions and triangular-array
variants below, written using explicit Lagrange products.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos1132

/-- The Lebesgue function of one row of interpolation nodes. -/
noncomputable def rowLebesgue {n : ℕ} (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, (x - X j) / (X i - X j)|

private theorem rowLebesgue_eq {n : ℕ} (X : Nodes n) (x : ℝ) :
    rowLebesgue X.point x = X.lebesgue x := by
  simp only [rowLebesgue, Nodes.lebesgue, Nodes.cardinal,
    Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, div_eq_mul_inv, mul_comm]

/-- Dense additive lower bounds and sharp almost-everywhere growth for triangular arrays. -/
theorem erdos_1132.variants.triangular_arrays :
    ∀ X : ∀ n : ℕ, Fin n → ℝ, (∀ n, Function.Injective (X n)) →
      (∀ n i, X n i ∈ Icc (-1 : ℝ) 1) →
      Dense {x : Ioo (-1 : ℝ) 1 | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < rowLebesgue (X n) x} ∧
      (∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
        ((2 / Real.pi : ℝ) : EReal) ≤
          limsup (fun n => ((rowLebesgue (X n) x / Real.log (n : ℝ) : ℝ) : EReal)) atTop) := by
  intro X hinj hI
  let rows : ∀ n, Nodes n := fun n => ⟨X n, hinj n, hI n⟩
  simpa only [← rowLebesgue_eq] using theorem1 rows

/-- info: 'Erdos1132.erdos_1132.variants.triangular_arrays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.erdos_1132.variants.triangular_arrays

/-- A nested node sequence has a point with bounded additive loss infinitely often. -/
theorem erdos_1132.parts.i :
    True ↔ ∀ X : ℕ → ℝ, Function.Injective X →
      (∀ i, X i ∈ Icc (-1 : ℝ) 1) → ∃ x ∈ Ioo (-1 : ℝ) 1, ∃ C : ℝ,
        ∃ᶠ n : ℕ in atTop,
          (2 / Real.pi) * Real.log (n : ℝ) - C < rowLebesgue (fun i : Fin n => X i) x := by
  constructor
  · intro _ X hinj hI
    let : Nonempty (Ioo (-1 : ℝ) 1) := ⟨⟨0, by constructor <;> norm_num⟩⟩
    have h := (erdos_1132.variants.triangular_arrays (fun n i => X i)
      (fun n i j hij => Fin.ext (hinj hij)) (fun n i => hI i)).1
    obtain ⟨x, C, hx⟩ := h.nonempty
    exact ⟨x, x.property, C, hx⟩
  · intro _
    trivial

/-- info: 'Erdos1132.erdos_1132.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.erdos_1132.parts.i

/-- The sharp normalized lower bound holds almost everywhere for nested node sequences. -/
theorem erdos_1132.parts.ii :
    True ↔ ∀ X : ℕ → ℝ, Function.Injective X →
      (∀ i, X i ∈ Icc (-1 : ℝ) 1) →
      ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
        ((2 / Real.pi : ℝ) : EReal) ≤
          limsup (fun n : ℕ =>
            ((rowLebesgue (fun i : Fin n => X i) x / Real.log (n : ℝ) : ℝ) : EReal)) atTop := by
  constructor
  · intro _ X hinj hI
    exact (erdos_1132.variants.triangular_arrays (fun n i => X i)
      (fun n i j hij => Fin.ext (hinj hij)) (fun n i => hI i)).2
  · intro _
    trivial

/-- info: 'Erdos1132.erdos_1132.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.erdos_1132.parts.ii

/-- Triangular arrays with an arbitrary pointwise deficit and no dense uniform additive bound. -/
theorem erdos_1132.variants.nonuniform_arrays :
    ∀ M : ℝ, 0 < M → ∃ X : ∀ n : ℕ, Fin n → ℝ,
      (∀ n, Function.Injective (X n)) ∧ (∀ n i, X n i ∈ Ioo (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ n : ℕ in atTop,
        rowLebesgue (X n) x ≤ (2 / Real.pi) * Real.log (n : ℝ) - M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ n : ℕ in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < rowLebesgue (X n) x}) := by
  intro M hM
  obtain ⟨X, hI, hupper, hnd⟩ := theorem2 M hM
  refine ⟨fun n => (X n).point, fun n => (X n).injective, hI, ?_, ?_⟩
  · simpa only [rowLebesgue_eq] using hupper
  · simpa only [rowLebesgue_eq] using hnd

/-- info: 'Erdos1132.erdos_1132.variants.nonuniform_arrays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.erdos_1132.variants.nonuniform_arrays

end Erdos1132
