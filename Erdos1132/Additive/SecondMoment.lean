import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

/-! # Second moments and recurrence of measurable sets

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped BigOperators ENNReal Topology
namespace Erdos1132

/-- Cauchy--Schwarz against the constant function, written without square roots. -/
theorem integral_sq_le_mass_mul_integral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, (f x)^2 ∂μ := by
  let m := μ.real univ
  let S := ∫ x, f x ∂μ
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  by_cases hm0 : m = 0
  · have hμ : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact (ENNReal.toReal_eq_zero_iff (μ univ) |>.mp hm0).resolve_right (measure_ne_top μ univ)
    simp [hμ]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have heq (x : α) : (m*f x-S)^2 = m^2*(f x)^2 - (2*m*S)*f x + S^2 := by ring
  have hnonneg : 0 ≤ ∫ x, (m*f x-S)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  simp_rw [heq] at hnonneg
  have hi1 : Integrable (fun x => m^2*(f x)^2) μ := hf2.const_mul _
  have hi2 : Integrable (fun x => (2*m*S)*f x) μ := hf.const_mul _
  have hi3 : Integrable (fun x => m^2*(f x)^2 - (2*m*S)*f x) μ := hi1.sub hi2
  rw [integral_add hi3 (integrable_const (S^2)),
    integral_sub hi1 hi2, integral_const_mul,
    integral_const_mul, integral_const] at hnonneg
  change 0 ≤ m^2 * (∫ x, (f x)^2 ∂μ) - (2*m*S)*S + m*S^2 at hnonneg
  have hprod : 0 ≤ m * (m * (∫ x, (f x)^2 ∂μ) - S^2) := by nlinarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod hmpos)

def eventCount {α ι : Type*} (s : Finset ι) (A : ι → Set α) (x : α) : ℝ :=
  ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) x

theorem eventCount_sq {α ι : Type*} (s : Finset ι) (A : ι → Set α) (x : α) :
    (eventCount s A x)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).indicator (fun _ => (1 : ℝ)) x := by
  rw [eventCount, pow_two, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  by_cases hx : x ∈ A i <;> by_cases hy : x ∈ A j <;> simp [hx, hy]

theorem integrable_eventCount {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) : Integrable (eventCount s A) μ := by
  apply integrable_finsetSum
  intro i hi
  exact (integrable_const _).indicator (hA i hi)

theorem integral_eventCount {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫ x, eventCount s A x ∂μ) = ∑ i ∈ s, μ.real (A i) := by
  unfold eventCount
  rw [integral_finsetSum s (fun i hi => (integrable_const _).indicator (hA i hi))]
  apply sum_congr rfl
  intro i hi
  simp [integral_indicator_const, hA i hi]

theorem integrable_eventCount_sq {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    Integrable (fun x => (eventCount s A x)^2) μ := by
  simp_rw [eventCount_sq]
  apply integrable_finsetSum
  intro i hi
  exact integrable_eventCount μ s (fun j => A i ∩ A j)
    (fun j hj => (hA i hi).inter (hA j hj))

theorem integral_eventCount_sq {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫ x, (eventCount s A x)^2 ∂μ) = ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
  simp_rw [eventCount_sq]
  change (∫ x, ∑ i ∈ s, eventCount s (fun j => A i ∩ A j) x ∂μ) = _
  rw [integral_finsetSum s (fun i hi => integrable_eventCount μ s
    (fun j => A i ∩ A j) (fun j hj => (hA i hi).inter (hA j hj)))]
  apply sum_congr rfl
  intro i hi
  exact integral_eventCount μ s (fun j => A i ∩ A j)
    (fun j hj => (hA i hi).inter (hA j hj))

/-- A finite family of events occupies at least the mass forced by its first
and second moments. -/
theorem finite_union_second_moment {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∑ i ∈ s, μ.real (A i))^2 ≤
      μ.real (⋃ i ∈ s, A i) * (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) := by
  let U := ⋃ i ∈ s, A i
  have hzero (x : α) (hx : x ∉ U) : eventCount s A x = 0 := by
    apply sum_eq_zero
    intro i hi
    have hxi : x ∉ A i := fun hh => hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hh⟩⟩)
    simp [hxi]
  have h := integral_sq_le_mass_mul_integral_sq (μ.restrict U)
    (integrable_eventCount μ s A hA).integrableOn
    (integrable_eventCount_sq μ s A hA).integrableOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx]; norm_num),
    integral_eventCount μ s A hA, integral_eventCount_sq μ s A hA] at h
  simpa only [Measure.real, Measure.restrict_apply_univ] using h

/-- A uniform second-moment bound on finite subfamilies of every tail gives
a positive-measure set of points belonging to infinitely many events. -/
theorem measure_frequently_pos_of_second_moment
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) {C : ℝ} (hC : 0 < C)
    (htail : ∀ N : ℕ, ∃ s : Finset ℕ, (∀ n ∈ s, N ≤ n) ∧
      0 < ∑ n ∈ s, μ.real (A n) ∧
      (∑ n ∈ s, ∑ m ∈ s, μ.real (A n ∩ A m)) ≤ C * (∑ n ∈ s, μ.real (A n))^2) :
    0 < μ {x | ∃ᶠ n in atTop, x ∈ A n} := by
  let T (N : ℕ) : Set α := ⋃ n ≥ N, A n
  have hTm (N : ℕ) : MeasurableSet (T N) :=
    MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ => hA n))
  have hTanti : Antitone T := by
    intro N M hNM x hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨n, hNM.trans hn, hx⟩
  have hTlower (N : ℕ) : ENNReal.ofReal (1/C) ≤ μ (T N) := by
    obtain ⟨s, hs, hsum, hsecond⟩ := htail N
    have hm := finite_union_second_moment μ s A (fun n _ => hA n)
    have hmass : 0 ≤ μ.real (⋃ n ∈ s, A n) := ENNReal.toReal_nonneg
    have hbound := hm.trans (mul_le_mul_of_nonneg_left hsecond hmass)
    have hmul : 1 ≤ μ.real (⋃ n ∈ s, A n) * C := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hsum)).mp
      nlinarith only [hbound]
    have hdiv : 1/C ≤ μ.real (⋃ n ∈ s, A n) := (div_le_iff₀ hC).mpr hmul
    have hsub : (⋃ n ∈ s, A n) ⊆ T N := by
      intro x hx
      obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨n, hs n hn, hx⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr
      (hdiv.trans (measureReal_mono hsub (measure_ne_top μ _)))
  have hfreq : {x | ∃ᶠ n in atTop, x ∈ A n} = ⋂ N, T N := by
    ext x
    simp only [mem_ofPred_eq, frequently_atTop, mem_iInter, T, mem_iUnion, exists_prop]
  rw [hfreq, hTanti.measure_iInter (fun N => (hTm N).nullMeasurableSet)
    ⟨0, measure_ne_top μ _⟩]
  exact (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hC)).trans_le (le_iInf hTlower)

end Erdos1132
