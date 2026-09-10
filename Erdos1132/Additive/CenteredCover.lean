import Erdos1132.Additive.FiniteOverlap
import Erdos1132.Additive.IsolatedPacking

/-! # Measures of unions of short intervals around displaced isolated nodes

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Finset MeasureTheory
open scoped BigOperators
namespace Erdos1132

def centeredCover {ι : Type*} (s : Finset ι) (y : ι → ℝ) (r : ℝ) : Set ℝ :=
  ⋃ i ∈ s, Icc (y i-r) (y i+r)

theorem isCompact_centeredCover {ι : Type*} (s : Finset ι) (y : ι → ℝ) (r : ℝ) :
    IsCompact (centeredCover s y r) := s.isCompact_biUnion (fun i hi => isCompact_Icc)

theorem measurableSet_centeredCover {ι : Type*} (s : Finset ι) (y : ι → ℝ) (r : ℝ) :
    MeasurableSet (centeredCover s y r) := (isCompact_centeredCover s y r).measurableSet

theorem measure_centeredCover_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (centeredCover s y r) ≤ 2*r*(s.card:ℝ) := by
  have hh := measureReal_biUnion_finset_le (μ := volume) s (fun i => Icc (y i-r) (y i+r))
  have hm (i : ι) : volume.real (Icc (y i-r) (y i+r)) = 2*r := by
    rw [Real.volume_real_Icc, max_eq_left (by linarith)]
    ring
  simp_rw [hm] at hh
  simpa only [sum_const, nsmul_eq_mul, mul_comm (2*r)] using! hh

theorem measure_centeredCover_lower {ι : Type*} (s : Finset ι) (y : ι → ℝ) {r B : ℝ}
    (hr : 0 ≤ r)
    (hcount : ∀ x, ((s.filter (fun i => x ∈ Icc (y i-r) (y i+r))).card:ℝ) ≤ B) :
    2*r*(s.card:ℝ) ≤ B*volume.real (centeredCover s y r) := by
  classical
  let U := centeredCover s y r
  have hu := measurableSet_centeredCover s y r
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (isCompact_centeredCover s y r).measure_ne_top
  have hh := finite_union_lower_of_multiplicity μ s (fun i => Icc (y i-r) (y i+r))
    (fun i hi => measurableSet_Icc) (fun x => by rw [eventCount_eq_card]; exact hcount x)
  have hm (i : ι) (hi : i ∈ s) : μ.real (Icc (y i-r) (y i+r)) = 2*r := by
    have hsub : Icc (y i-r) (y i+r) ⊆ U := fun x hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
    dsimp only [μ]
    rw [measureReal_restrict_apply measurableSet_Icc, inter_eq_left.mpr hsub,
      Real.volume_real_Icc, max_eq_left (by linarith)]
    ring
  have hsum : (∑ i ∈ s, μ.real (Icc (y i-r) (y i+r))) = 2*r*(s.card:ℝ) := by
    rw [sum_congr rfl hm]
    simp only [sum_const, nsmul_eq_mul]
    ring
  rw [hsum] at hh
  change _ ≤ B*(volume.restrict U).real U at hh
  simpa only [measureReal_restrict_apply_self] using hh

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem displaced_isolated_card_bound (s : Finset (Fin n)) (y : Fin n → ℝ)
    {a b δ h : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) (hmove : ∀ i ∈ s, |y i-X.point i| ≤ h) :
    δ*((s.filter (fun i => y i ∈ Icc a b)).card:ℝ) ≤ 2*(b-a)+4*h+2*δ := by
  classical
  have hp := X.isolated_interval_card_bound (s.filter (fun i => y i ∈ Icc a b))
    (by linarith : a-h ≤ b+h) hδ
    (fun i hi => by
      have hm := abs_le.mp (hmove i (mem_filter.mp hi).1)
      have hy := (mem_filter.mp hi).2
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    (fun i hi => hiso i (mem_filter.mp hi).1)
  convert! hp using 1 <;> ring

theorem displaced_cover_multiplicity (s : Finset (Fin n)) (y : Fin n → ℝ)
    {δ h r : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) (hmove : ∀ i ∈ s, |y i-X.point i| ≤ h)
    (x : ℝ) :
    ((s.filter (fun i => x ∈ Icc (y i-r) (y i+r))).card:ℝ) ≤ (4*r+4*h+2*δ)/δ := by
  classical
  have he : s.filter (fun i => x ∈ Icc (y i-r) (y i+r)) =
      s.filter (fun i => y i ∈ Icc (x-r) (x+r)) := by
    ext i
    simp only [mem_filter, Set.mem_Icc]
    constructor <;> rintro ⟨hi, h1, h2⟩ <;> exact ⟨hi, by linarith, by linarith⟩
  rw [he]
  have hp := X.displaced_isolated_card_bound s y (by linarith : x-r ≤ x+r) hδ hh hiso hmove
  apply (le_div_iff₀ hδ).mpr
  nlinarith

theorem displaced_cover_intersection_bound (s : Finset (Fin n)) (y : Fin n → ℝ)
    {δ h r a b : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) (hr : 0 ≤ r) (hab : a ≤ b)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) (hmove : ∀ i ∈ s, |y i-X.point i| ≤ h) :
    volume.real (centeredCover s y r ∩ Icc a b) ≤
      (2*r/δ)*(2*(b-a)+4*r+4*h+2*δ) := by
  classical
  let T := s.filter (fun i => y i ∈ Icc (a-r) (b+r))
  have hsub : centeredCover s y r ∩ Icc a b ⊆ centeredCover T y r := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp hx.1
    refine mem_iUnion₂.mpr ⟨i, mem_filter.mpr ⟨hi, ?_⟩, hix⟩
    exact ⟨by linarith [hx.2.1, hix.2], by linarith [hx.2.2, hix.1]⟩
  have hm := (measureReal_mono (μ := volume) hsub (isCompact_centeredCover T y r).measure_ne_top).trans
    (measure_centeredCover_le T y hr)
  have hc := X.displaced_isolated_card_bound s y (by linarith : a-r ≤ b+r) hδ hh hiso hmove
  have hc' : (T.card:ℝ) ≤ (2*(b-a)+4*r+4*h+2*δ)/δ := by
    apply (le_div_iff₀ hδ).mpr
    change δ*(T.card:ℝ) ≤ _ at hc
    nlinarith
  exact hm.trans ((mul_le_mul_of_nonneg_left hc' (by positivity)).trans_eq (by ring))

end Nodes
end Erdos1132
