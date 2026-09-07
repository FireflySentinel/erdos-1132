import Mathlib.Tactic

/-! # Many large values from a bounded weighted deficit

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open Finset
open scoped BigOperators
namespace Erdos1132

theorem weighted_good_mass {ι : Type*} [Fintype ι]
    (w T : ι → ℝ) {U D C : ℝ} (hD : 0 < D)
    (hw : ∀ i, 0 ≤ w i) (hupper : ∀ i, 0 < w i → T i ≤ U)
    (hdef : (∑ i, w i*(U-T i)) ≤ C) :
    (∑ i, w i)-C/D ≤ ∑ i ∈ univ.filter (fun i => 0 < w i ∧ U-D ≤ T i), w i := by
  classical
  let G := univ.filter (fun i => 0 < w i ∧ U-D ≤ T i)
  have hpoint (i : ι) : w i ≤ (if i ∈ G then w i else 0)+w i*(U-T i)/D := by
    have hnn : 0 ≤ w i*(U-T i) := by
      by_cases hi : w i = 0
      · simp [hi]
      · exact mul_nonneg (hw i) (sub_nonneg.mpr (hupper i (lt_of_le_of_ne (hw i) (Ne.symm hi))))
    by_cases hi : i ∈ G
    · rw [if_pos hi]
      have hh := div_nonneg hnn hD.le
      linarith
    · rw [if_neg hi, zero_add]
      by_cases hw0 : w i = 0
      · simp [hw0]
      have hwp : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hw0)
      have hbad : T i < U-D := by
        by_contra hh
        exact hi (mem_filter.mpr ⟨mem_univ i, hwp, le_of_not_gt hh⟩)
      apply (le_div_iff₀ hD).mpr
      nlinarith
  have hs := sum_le_sum (s := univ) (fun i _ => hpoint i)
  simp only [sum_add_distrib, ← sum_filter, ← sum_div] at hs
  have hd := div_le_div_of_nonneg_right hdef hD.le
  dsimp only [G] at hs
  simp only [filter_mem_eq_inter, univ_inter] at hs
  linarith

theorem many_large_values_of_weighted_deficit {n : ℕ} (hn : 0 < n)
    (w T : Fin n → ℝ) {U D C W B : ℝ} (hD : 0 < D) (hW : 0 < W) (hB : 0 < B)
    (hw : ∀ i, 0 ≤ w i) (hwb : ∀ i, w i ≤ B/(n:ℝ))
    (hupper : ∀ i, 0 < w i → T i ≤ U)
    (htotal : 3*W/4 ≤ ∑ i, w i) (hdef : (∑ i, w i*(U-T i)) ≤ C)
    (hsmall : C/D ≤ W/4) :
    (W/(2*B))*(n:ℝ) ≤
      ((univ.filter (fun i => 0 < w i ∧ U-D ≤ T i)).card : ℝ) := by
  classical
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let G := univ.filter (fun i => 0 < w i ∧ U-D ≤ T i)
  have hg := weighted_good_mass w T hD hw hupper hdef
  have hm : W/2 ≤ ∑ i ∈ G, w i := by dsimp [G]; linarith
  have hbound : (∑ i ∈ G, w i) ≤ (G.card:ℝ)*(B/(n:ℝ)) := by
    calc
      _ ≤ ∑ _i ∈ G, B/(n:ℝ) := sum_le_sum (fun i hi => hwb i)
      _ = _ := by simp
  have hh := (le_div_iff₀ hnR).mp (show W/2 ≤ (G.card:ℝ)*B/(n:ℝ) by
    simpa only [mul_div_assoc] using hm.trans hbound)
  have hc : W*(n:ℝ)/(2*B) ≤ (G.card:ℝ) := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  convert! hc using 1 <;> ring

end Erdos1132
