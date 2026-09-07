import Erdos1132.LocalRecurrence
import Erdos1132.BaireBounds
import Erdos1132.Main

/-! # The sharp additive lower bound on a dense set

This is Theorem 1(i), with exactly `n` distinct interpolation nodes in row `n`.
The additive constant can depend on the chosen point.
-/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace Erdos1132

theorem dense_additive_lower_bound (X : ∀ n, Nodes n) :
    Dense {x : Ioo (-1:ℝ) 1 | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
      (2/Real.pi)*Real.log n-C < (X n).lebesgue x} := by
  apply dense_additive_good_of_local_recurrence (fun n x => (X n).lebesgue x)
    (fun n => (X n).continuous_lebesgue) (fun n => (2/Real.pi)*Real.log n)
  intro l r hlr hI C hupper
  have hI' : Icc l r ⊆ Icc (-1:ℝ) 1 := hI.trans Ioo_subset_Icc_self
  obtain ⟨D, hD, hrec⟩ := local_additive_recurrence X hlr hI' hupper
  obtain ⟨x, hx, hxf⟩ := nonempty_of_measure_ne_zero hrec.ne'
  exact ⟨x, hx, D, hxf⟩

/-- Both conclusions of Theorem 1 for every array of distinct nodes. -/
theorem theorem1 (X : ∀ n, Nodes n) :
    Dense {x : Ioo (-1:ℝ) 1 | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
      (2/Real.pi)*Real.log n-C < (X n).lebesgue x} ∧
    (∀ᵐ x ∂volume.restrict (Ioo (-1:ℝ) 1),
      ((2 / Real.pi : ℝ) : EReal) ≤
        limsup (fun n => (((X n).lebesgue x / Real.log (n:ℝ) : ℝ) : EReal)) atTop) :=
  ⟨dense_additive_lower_bound X, ae_lebesgue_limsup X⟩

end Erdos1132
