import Erdos1132.Additive.NodeIsolation
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Local counting bounds from empty intervals on one side of every point

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Finset MeasureTheory
open scoped BigOperators
namespace Erdos1132

theorem separated_interval_card_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hx : ∀ i ∈ s, x i ∈ Icc a b)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i-x j|) :
    δ*(s.card:ℝ) ≤ b-a+δ := by
  let A (i : ι) := Ico (x i) (x i+δ)
  have hd : (s : Set ι).PairwiseDisjoint A := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t ht ht'
    have hs := hsep i hi j hj hij
    have hh : |x i-x j| < δ := abs_lt.mpr ⟨by linarith [ht'.1, ht.2], by linarith [ht.1, ht'.2]⟩
    exact hs.not_gt hh
  have hsub : (⋃ i ∈ s, A i) ⊆ Ico a (b+δ) := by
    intro t ht
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨(hx i hi).1.trans ht.1, by linarith [ht.2, (hx i hi).2]⟩
  have hh := measureReal_mono (μ := volume) hsub (by exact measure_Ico_lt_top.ne)
  rw [measureReal_biUnion_finset hd (fun i hi => measurableSet_Ico)
    (fun i hi => measure_Ico_lt_top.ne)] at hh
  have hm (i : ι) : volume.real (A i) = δ := by
    simp [A, Real.volume_real_Ico, hδ.le]
  simp_rw [hm] at hh
  have hbig : volume.real (Ico a (b+δ)) = b-a+δ := by
    rw [Real.volume_real_Ico, max_eq_left (by linarith)]
    ring
  rw [hbig] at hh
  simpa only [sum_const, nsmul_eq_mul, mul_comm δ] using hh

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem isolated_interval_card_bound (s : Finset (Fin n)) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hx : ∀ i ∈ s, X.point i ∈ Icc a b)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) :
    δ*(s.card:ℝ) ≤ 2*(b-a)+2*δ := by
  classical
  let P (i : Fin n) := ∀ j, X.point i < X.point j → X.point i+δ ≤ X.point j
  let R := s.filter P
  let L := s.filter (fun i => ¬P i)
  have hR (i : Fin n) (hi : i ∈ R) : P i := (mem_filter.mp hi).2
  have hL (i : Fin n) (hi : i ∈ L) : ∀ j, X.point j < X.point i → X.point j+δ ≤ X.point i :=
    (hiso i (mem_filter.mp hi).1).resolve_left (mem_filter.mp hi).2
  have hsepR : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → δ ≤ |X.point i-X.point j| := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne (X.injective.ne hij) with hh | hh
    · rw [abs_of_neg (sub_neg.mpr hh)]
      linarith [hR i hi j hh]
    · rw [abs_of_pos (sub_pos.mpr hh)]
      linarith [hR j hj i hh]
  have hsepL : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → δ ≤ |X.point i-X.point j| := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne (X.injective.ne hij) with hh | hh
    · rw [abs_of_neg (sub_neg.mpr hh)]
      linarith [hL j hj i hh]
    · rw [abs_of_pos (sub_pos.mpr hh)]
      linarith [hL i hi j hh]
  have hbR := separated_interval_card_bound R X.point hab hδ
    (fun i hi => hx i (mem_filter.mp hi).1) hsepR
  have hbL := separated_interval_card_bound L X.point hab hδ
    (fun i hi => hx i (mem_filter.mp hi).1) hsepL
  have hc : (R.card:ℝ)+(L.card:ℝ) = (s.card:ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := s) P
  nlinarith

end Nodes
end Erdos1132
