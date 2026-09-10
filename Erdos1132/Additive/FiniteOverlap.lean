import Erdos1132.Additive.SecondMoment

/-! # Lower bounds for a finite union with bounded multiplicity

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset
open scoped BigOperators
namespace Erdos1132

theorem eventCount_eq_card {α ι : Type*} (s : Finset ι) (A : ι → Set α) (x : α)
    [DecidablePred (fun i => x ∈ A i)] :
    eventCount s A x = ((s.filter (fun i => x ∈ A i)).card : ℝ) := by
  classical
  simp only [eventCount, Set.indicator_apply, Finset.card_filter]
  push_cast
  rfl

theorem finite_union_lower_of_multiplicity {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) {B : ℝ}
    (hB : ∀ x, eventCount s A x ≤ B) :
    (∑ i ∈ s, μ.real (A i)) ≤ B*μ.real (⋃ i ∈ s, A i) := by
  let U := ⋃ i ∈ s, A i
  have hu : MeasurableSet U := s.measurableSet_biUnion hA
  have hz (x : α) (hx : x ∉ U) : eventCount s A x = 0 := by
    apply sum_eq_zero
    intro i hi
    have hxi : x ∉ A i := fun h => hx (mem_iUnion₂.mpr ⟨i, hi, h⟩)
    simp [hxi]
  have hh : (∫ x in U, eventCount s A x ∂μ) ≤ ∫ _x in U, B ∂μ :=
    integral_mono (integrable_eventCount μ s A hA).integrableOn (integrable_const _) hB
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_eventCount μ s A hA] at hh
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm B] using hh

end Erdos1132
