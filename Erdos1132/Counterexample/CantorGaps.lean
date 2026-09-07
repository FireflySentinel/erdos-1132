import Erdos1132.Counterexample.CantorLevels

/-!
# The gaps removed at each level

Every gap lies inside its parent, is disjoint from the next retained level,
and has both endpoints in the compact limit set.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Erdos1132.Counterexample

def cantorStageGap (ρ : ℝ) (k : ℕ) (w : CantorWord ρ k) (i : ℕ) : Set ℝ :=
  subdivisionGap (cantorLeft ρ k w) (cantorLength ρ (k+1)) (cantorGapLength ρ k) i

def cantorGapLeft (ρ : ℝ) (k : ℕ) (w : CantorWord ρ k) (i : ℕ) : ℝ :=
  childLeft (cantorLeft ρ k w) (cantorLength ρ (k+1)) (cantorGapLength ρ k) i + cantorLength ρ (k+1)

def cantorGapRight (ρ : ℝ) (k : ℕ) (w : CantorWord ρ k) (i : ℕ) : ℝ :=
  childLeft (cantorLeft ρ k w) (cantorLength ρ (k+1)) (cantorGapLength ρ k) (i+1)

theorem cantorGap_length (ρ : ℝ) (k : ℕ) (w : CantorWord ρ k) (i : ℕ) :
    cantorGapRight ρ k w i-cantorGapLeft ρ k w i = cantorGapLength ρ k :=
  subdivisionGap_length _ _ _ _

theorem cantorStageGap_subset_parent {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) {i : ℕ} (hi : i+1 < cantorBranching ρ k) :
    cantorStageGap ρ k w i ⊆ cantorInterval ρ k w := by
  have hsub := subdivisionGap_subset_parent (L := cantorLeft ρ k w)
    (cantorLength_pos hρ hρ4 (k+1)).le (cantorGapLength_pos hρ hρ4 k).le hi
  have hsum := cantor_subdivision_length hρ hρ4 k
  intro x hx
  have hh := hsub hx
  refine ⟨hh.1, ?_⟩
  change x ≤ cantorLeft ρ k w+cantorLength ρ k
  linarith [hh.2]

theorem cantorStageGap_disjoint_nextLevel {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) {i : ℕ} (hi : i+1 < cantorBranching ρ k) :
    Disjoint (cantorStageGap ρ k w i) (cantorLevel ρ (k+1)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v, hv⟩ := mem_iUnion.mp hy
  by_cases he : w = v.1
  · have hd := gap_disjoint_children (L := cantorLeft ρ k w) (i := i) (j := v.2)
      (cantorLength_pos hρ hρ4 (k+1)) (cantorGapLength_pos hρ hρ4 k)
    apply Set.disjoint_left.mp hd hx
    simpa only [cantorInterval, cantorLeft, childInterval, he] using hv
  · exact Set.disjoint_left.mp (cantor_interval_pairwise_disjoint hρ hρ4 k he)
      (cantorStageGap_subset_parent hρ hρ4 k w hi hx) (cantor_child_subset hρ hρ4 k v hv)

theorem cantorStageGap_disjoint_set {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) {i : ℕ} (hi : i+1 < cantorBranching ρ k) :
    Disjoint (cantorStageGap ρ k w i) (cantorSet ρ) :=
  (cantorStageGap_disjoint_nextLevel hρ hρ4 k w hi).mono_right (iInter_subset _ (k+1))

theorem cantorStageGap_endpoints {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) {i : ℕ} (hi : i+1 < cantorBranching ρ k) :
    cantorGapLeft ρ k w i ∈ cantorSet ρ ∧ cantorGapRight ρ k w i ∈ cantorSet ρ := by
  constructor
  · exact cantor_right_mem_set hρ hρ4 (k+1) (w, ⟨i, by omega⟩)
  · exact cantor_left_mem_set hρ hρ4 (k+1) (w, ⟨i+1, hi⟩)

theorem cantorStageGap_disjoint_later {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    {k l i j : ℕ} (hkl : k < l) (w : CantorWord ρ k) (v : CantorWord ρ l)
    (hi : i+1 < cantorBranching ρ k) (hj : j+1 < cantorBranching ρ l) :
    Disjoint (cantorStageGap ρ k w i) (cantorStageGap ρ l v j) := by
  apply (cantorStageGap_disjoint_nextLevel hρ hρ4 k w hi).mono_right
  intro x hx
  apply cantorLevel_antitone hρ hρ4 (show k+1 ≤ l by omega)
  exact mem_iUnion.mpr ⟨v, cantorStageGap_subset_parent hρ hρ4 l v hj hx⟩

end Erdos1132.Counterexample
