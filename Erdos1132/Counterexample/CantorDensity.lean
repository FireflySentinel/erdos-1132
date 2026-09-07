import Erdos1132.Counterexample.CantorMeasure

/-!
# Uniform density of the compact Cantor set

A small retained parent supplies enough measure directly. In a larger
parent, a consecutive block of complete children lies inside the query
interval, and each retains at least half its measure in the limit.

Paper: §7.1, the compact set and its gaps.
-/

noncomputable section

open Set Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace Erdos1132.Counterexample

theorem measure_full_children_lower {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) {A B : ℝ} {p q : ℕ}
    (_hpq : p ≤ q) (hqm : q ≤ cantorBranching ρ k)
    (hsub : ∀ i ∈ Finset.Ico p q,
      childInterval (cantorLeft ρ k w) (cantorLength ρ (k+1)) (cantorGapLength ρ k) i ⊆ Icc A B) :
    ENNReal.ofReal (((q-p : ℕ) : ℝ)*cantorLength ρ (k+1)/2) ≤
      volume (cantorSet ρ ∩ Icc A B) := by
  classical
  let f := fun i : ℕ => cantorSet ρ ∩
    childInterval (cantorLeft ρ k w) (cantorLength ρ (k+1)) (cantorGapLength ρ k) i
  have hlow (i : ℕ) (hi : i ∈ Finset.Ico p q) :
      ENNReal.ofReal (cantorLength ρ (k+1)/2) ≤ volume (f i) := by
    have him : i < cantorBranching ρ k := (Finset.mem_Ico.mp hi).2.trans_le hqm
    exact measure_cantorSet_inter_parent_half hρ hρ4 (k+1) (w, ⟨i, him⟩)
  have hdis : (↑(Finset.Ico p q) : Set ℕ).PairwiseDisjoint f := by
    intro i _ j _ hij
    exact (childInterval_pairwise_disjoint (L := cantorLeft ρ k w)
      (cantorLength_pos hρ hρ4 (k+1)) (cantorGapLength_pos hρ hρ4 k) hij).mono
      inter_subset_right inter_subset_right
  have hmeas (i : ℕ) : MeasurableSet (f i) :=
    (isClosed_cantorSet ρ).measurableSet.inter measurableSet_Icc
  have hsum := Finset.sum_le_sum (fun i hi => hlow i hi)
  have hconst : (∑ _i ∈ Finset.Ico p q, ENNReal.ofReal (cantorLength ρ (k+1)/2)) =
      ENNReal.ofReal (((q-p : ℕ) : ℝ)*cantorLength ρ (k+1)/2) := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [hconst, ← measure_biUnion_finset hdis (fun i _ => hmeas i)] at hsum
  apply hsum.trans (measure_mono ?_)
  intro x hx
  obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
  exact ⟨hx.1, hsub i hi hx.2⟩

theorem cantor_uniform_density {ρ x r : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hx : x ∈ cantorSet ρ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (r/32) ≤ volume (cantorSet ρ ∩ Icc (x-r) (x+r)) := by
  have hex : ∃ k : ℕ, cantorLength ρ k ≤ r/16 := by
    have hh := (cantorLength_tendsto_zero hρ hρ4).eventually
      (gt_mem_nhds (show 0 < r/16 by positivity))
    obtain ⟨k, hk⟩ := hh.exists
    exact ⟨k, hk.le⟩
  have hfind := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro hz
    rw [hz, cantorLength] at hfind
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hsmall : cantorLength ρ (k+1) ≤ r/16 := by simpa only [hk] using hfind
  have hlarge : r/16 < cantorLength ρ k := by
    apply lt_of_not_ge
    exact Nat.find_min hex (by omega)
  obtain ⟨u, hu⟩ := mem_iUnion.mp (mem_iInter.mp hx (k+1))
  let w : CantorWord ρ k := u.1
  have hxp : x ∈ cantorInterval ρ k w := cantor_child_subset hρ hρ4 k u hu
  let L := cantorLeft ρ k w
  let a := cantorLength ρ (k+1)
  let b := cantorGapLength ρ k
  have ha : 0 < a := cantorLength_pos hρ hρ4 (k+1)
  have hb : 0 < b := cantorGapLength_pos hρ hρ4 k
  have hba : b ≤ a := cantorGapLength_le_child hρ hρ4 k
  by_cases hparent : cantorLength ρ k ≤ r
  · apply le_trans _ ((measure_cantorSet_inter_parent_half hρ hρ4 k w).trans (measure_mono ?_))
    · apply ENNReal.ofReal_le_ofReal
      linarith
    · intro y hy
      refine ⟨hy.1, ?_⟩
      have hyy := hy.2
      change L ≤ y ∧ y ≤ L+cantorLength ρ k at hyy
      change L ≤ x ∧ x ≤ L+cantorLength ρ k at hxp
      constructor <;> linarith
  · let A := max L (x-r)
    let B := min (L+cantorLength ρ k) (x+r)
    have hAB : r ≤ B-A := by
      change L ≤ x ∧ x ≤ L+cantorLength ρ k at hxp
      dsimp [A, B]
      rcases le_total L (x-r) with hh | hh <;>
        rcases le_total (L+cantorLength ρ k) (x+r) with hj | hj
      · rw [max_eq_right hh, min_eq_left hj]; linarith
      · rw [max_eq_right hh, min_eq_right hj]; linarith
      · rw [max_eq_left hh, min_eq_left hj]; linarith
      · rw [max_eq_left hh, min_eq_right hj]; linarith
    have hBpar : B ≤ L+(cantorBranching ρ k : ℝ)*a+(cantorBranching ρ k-1 : ℕ)*b := by
      have hh := min_le_left (L+cantorLength ρ k) (x+r)
      have hsum := cantor_subdivision_length hρ hρ4 k
      change B ≤ _ at hh
      dsimp [a, b]
      linarith
    have hm : 0 < cantorBranching ρ k := by have := cantorBranching_ge hρ hρ4 k; omega
    obtain ⟨p, q, hpq, hqm, hsub, hmass⟩ := exists_full_children_block hm ha hb.le hba
      (le_max_left _ _) hBpar (show 4*a ≤ B-A by linarith)
    have hlow := measure_full_children_lower hρ hρ4 k w hpq hqm hsub
    apply le_trans _ (hlow.trans (measure_mono ?_))
    · apply ENNReal.ofReal_le_ofReal
      change r/32 ≤ ((q-p : ℕ) : ℝ)*a/2
      linarith
    · intro y hy
      refine ⟨hy.1, ?_⟩
      exact ⟨(le_max_right _ _).trans hy.2.1, hy.2.2.trans (min_le_right _ _)⟩

end Erdos1132.Counterexample
