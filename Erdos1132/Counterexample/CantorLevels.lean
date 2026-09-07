import Erdos1132.Counterexample.CantorScales
import Erdos1132.Counterexample.Subdivision
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Retained intervals and their compact limit

Finite words label the intervals at each level. The recursive construction
retains disjoint closed children inside every parent interval.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Erdos1132.Counterexample

def CantorWord (ρ : ℝ) : ℕ → Type
  | 0 => Unit
  | k+1 => CantorWord ρ k × Fin (cantorBranching ρ k)

instance cantorWordFintype (ρ : ℝ) (k : ℕ) : Fintype (CantorWord ρ k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k hk =>
    letI := hk
    exact inferInstanceAs (Fintype (CantorWord ρ k × Fin (cantorBranching ρ k)))

def cantorLeft (ρ : ℝ) : (k : ℕ) → CantorWord ρ k → ℝ
  | 0, _ => -1
  | k+1, w => childLeft (cantorLeft ρ k w.1) (cantorLength ρ (k+1)) (cantorGapLength ρ k) w.2

def cantorInterval (ρ : ℝ) (k : ℕ) (w : CantorWord ρ k) : Set ℝ :=
  Icc (cantorLeft ρ k w) (cantorLeft ρ k w+cantorLength ρ k)

def cantorLevel (ρ : ℝ) (k : ℕ) : Set ℝ := ⋃ w : CantorWord ρ k, cantorInterval ρ k w

def cantorSet (ρ : ℝ) : Set ℝ := ⋂ k : ℕ, cantorLevel ρ k

@[simp] theorem cantorLevel_zero (ρ : ℝ) : cantorLevel ρ 0 = Icc (-1) 1 := by
  change (⋃ _ : Unit, Icc (-1 : ℝ) (-1+2)) = Icc (-1) 1
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := mem_iUnion.mp hx
    norm_num at hu
    exact hu
  · intro hx
    exact mem_iUnion.mpr ⟨(), by norm_num; exact hx⟩

theorem cantor_child_subset {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ)
    (w : CantorWord ρ (k+1)) : cantorInterval ρ (k+1) w ⊆ cantorInterval ρ k w.1 := by
  have hh := childInterval_subset_parent (L := cantorLeft ρ k w.1)
    (cantorLength_pos hρ hρ4 (k+1)).le (cantorGapLength_pos hρ hρ4 k).le w.2.isLt
  have hsum := cantor_subdivision_length hρ hρ4 k
  intro x hx
  have hx' := hh hx
  refine ⟨hx'.1, ?_⟩
  change x ≤ cantorLeft ρ k w.1 + cantorLength ρ k
  linarith [hx'.2]

theorem cantorLevel_succ_subset {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorLevel ρ (k+1) ⊆ cantorLevel ρ k := by
  intro x hx
  obtain ⟨w, hw⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨w.1, cantor_child_subset hρ hρ4 k w hw⟩

theorem cantorLevel_antitone {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    Antitone (cantorLevel ρ) := antitone_nat_of_succ_le (cantorLevel_succ_subset hρ hρ4)

theorem cantor_interval_pairwise_disjoint {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    Pairwise (fun u v : CantorWord ρ k => Disjoint (cantorInterval ρ k u) (cantorInterval ρ k v)) := by
  induction k with
  | zero => intro u v huv; exact (huv (@Subsingleton.elim Unit inferInstance u v)).elim
  | succ k hk =>
    intro u v huv
    by_cases he : u.1 = v.1
    · have hne : u.2 ≠ v.2 := by
        intro hj
        exact huv (Prod.ext he hj)
      have hh := childInterval_pairwise_disjoint (L := cantorLeft ρ k u.1)
        (cantorLength_pos hρ hρ4 (k+1)) (cantorGapLength_pos hρ hρ4 k)
        (show u.2.val ≠ v.2.val from fun h => hne (Fin.ext h))
      change Disjoint (childInterval (cantorLeft ρ k u.1) _ _ u.2)
        (childInterval (cantorLeft ρ k v.1) _ _ v.2)
      simpa only [he] using hh
    · exact (hk he).mono (cantor_child_subset hρ hρ4 k u) (cantor_child_subset hρ hρ4 k v)

theorem isCompact_cantorLevel (ρ : ℝ) (k : ℕ) : IsCompact (cantorLevel ρ k) :=
  isCompact_iUnion (fun _ => isCompact_Icc)

theorem isClosed_cantorSet (ρ : ℝ) : IsClosed (cantorSet ρ) :=
  isClosed_iInter (fun k => (isCompact_cantorLevel ρ k).isClosed)

theorem cantorSet_subset_interval (ρ : ℝ) : cantorSet ρ ⊆ Icc (-1) 1 := by
  intro x hx
  have hh := mem_iInter.mp hx 0
  simpa only [cantorLevel_zero] using hh

theorem isCompact_cantorSet (ρ : ℝ) : IsCompact (cantorSet ρ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_cantorSet ρ) (cantorSet_subset_interval ρ)


theorem cantor_left_child {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) :
    ∃ u : CantorWord ρ (k+1), cantorLeft ρ (k+1) u = cantorLeft ρ k w := by
  have hm : 0 < cantorBranching ρ k := by have := cantorBranching_ge hρ hρ4 k; omega
  refine ⟨(w, ⟨0, hm⟩), ?_⟩
  simp [cantorLeft, childLeft]

theorem cantor_right_child {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) :
    ∃ u : CantorWord ρ (k+1), cantorLeft ρ (k+1) u+cantorLength ρ (k+1) =
      cantorLeft ρ k w+cantorLength ρ k := by
  have hm : 0 < cantorBranching ρ k := by have := cantorBranching_ge hρ hρ4 k; omega
  refine ⟨(w, ⟨cantorBranching ρ k-1, by omega⟩), ?_⟩
  change childLeft (cantorLeft ρ k w) (cantorLength ρ (k+1)) (cantorGapLength ρ k)
    (cantorBranching ρ k-1) + cantorLength ρ (k+1) = _
  have hh := cantor_subdivision_length hρ hρ4 k
  have hm1 : 1 ≤ cantorBranching ρ k := hm
  unfold childLeft
  rw [Nat.cast_sub hm1, Nat.cast_one] at hh ⊢
  nlinarith

theorem cantor_left_descendant {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k d : ℕ) (w : CantorWord ρ k) :
    ∃ u : CantorWord ρ (k+d), cantorLeft ρ (k+d) u = cantorLeft ρ k w := by
  induction d with
  | zero => exact ⟨w, rfl⟩
  | succ d hd =>
    obtain ⟨v, hv⟩ := hd
    obtain ⟨u, hu⟩ := cantor_left_child hρ hρ4 (k+d) v
    exact ⟨u, hu.trans hv⟩

theorem cantor_right_descendant {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k d : ℕ) (w : CantorWord ρ k) :
    ∃ u : CantorWord ρ (k+d), cantorLeft ρ (k+d) u+cantorLength ρ (k+d) =
      cantorLeft ρ k w+cantorLength ρ k := by
  induction d with
  | zero => exact ⟨w, rfl⟩
  | succ d hd =>
    obtain ⟨v, hv⟩ := hd
    obtain ⟨u, hu⟩ := cantor_right_child hρ hρ4 (k+d) v
    exact ⟨u, hu.trans hv⟩

theorem cantor_left_mem_set {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) : cantorLeft ρ k w ∈ cantorSet ρ := by
  apply mem_iInter.mpr
  intro n
  by_cases hnk : n ≤ k
  · apply cantorLevel_antitone hρ hρ4 hnk
    exact mem_iUnion.mpr ⟨w, ⟨le_rfl, le_add_of_nonneg_right (cantorLength_pos hρ hρ4 k).le⟩⟩
  · have hkn : k ≤ n := by omega
    have hdesc := cantor_left_descendant hρ hρ4 k (n-k) w
    have he : k+(n-k) = n := Nat.add_sub_of_le hkn
    rw [he] at hdesc
    obtain ⟨u, hu⟩ := hdesc
    apply mem_iUnion.mpr
    refine ⟨u, ?_⟩
    rw [← hu]
    exact ⟨le_rfl, le_add_of_nonneg_right (cantorLength_pos hρ hρ4 n).le⟩

theorem cantor_right_mem_set {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) : cantorLeft ρ k w+cantorLength ρ k ∈ cantorSet ρ := by
  apply mem_iInter.mpr
  intro n
  by_cases hnk : n ≤ k
  · apply cantorLevel_antitone hρ hρ4 hnk
    exact mem_iUnion.mpr ⟨w, ⟨le_add_of_nonneg_right (cantorLength_pos hρ hρ4 k).le, le_rfl⟩⟩
  · have hkn : k ≤ n := by omega
    have hdesc := cantor_right_descendant hρ hρ4 k (n-k) w
    have he : k+(n-k) = n := Nat.add_sub_of_le hkn
    rw [he] at hdesc
    obtain ⟨u, hu⟩ := hdesc
    apply mem_iUnion.mpr
    refine ⟨u, ?_⟩
    rw [← hu]
    exact ⟨le_add_of_nonneg_right (cantorLength_pos hρ hρ4 n).le, le_rfl⟩

theorem cantor_endpoints {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    (-1 : ℝ) ∈ cantorSet ρ ∧ (1 : ℝ) ∈ cantorSet ρ := by
  constructor
  · exact cantor_left_mem_set hρ hρ4 0 ()
  · simpa only [cantorLeft, cantorLength, show (-1 : ℝ)+2 = 1 by norm_num] using
      cantor_right_mem_set hρ hρ4 0 ()

end Erdos1132.Counterexample
