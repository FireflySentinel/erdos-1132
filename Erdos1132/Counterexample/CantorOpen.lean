import Erdos1132.Counterexample.CantorGaps
import Erdos1132.Counterexample.CantorDensity

/-! # The open complement and its explicit gap decomposition

Companion note: §2.1, the compact set and its gaps.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Erdos1132.Counterexample

def cantorOpen (ρ : ℝ) : Set ℝ := Ioo (-1) 1 \ cantorSet ρ

def CantorGapIndex (ρ : ℝ) := Σ k : ℕ, CantorWord ρ k × Fin (cantorBranching ρ k-1)

def cantorGap (ρ : ℝ) (g : CantorGapIndex ρ) : Set ℝ :=
  cantorStageGap ρ g.1 g.2.1 g.2.2

def gapLeft (ρ : ℝ) (g : CantorGapIndex ρ) : ℝ :=
  cantorGapLeft ρ g.1 g.2.1 g.2.2

def gapRight (ρ : ℝ) (g : CantorGapIndex ρ) : ℝ :=
  cantorGapRight ρ g.1 g.2.1 g.2.2

theorem isOpen_cantorOpen (ρ : ℝ) : IsOpen (cantorOpen ρ) :=
  isOpen_Ioo.sdiff (isClosed_cantorSet ρ)

theorem cantorOpen_eq_diff {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    cantorOpen ρ = Icc (-1) 1 \ cantorSet ρ := by
  ext x
  constructor
  · exact fun hx => ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2⟩
  · rintro ⟨hx, hn⟩
    refine ⟨⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hn⟩
    · intro he; subst x; exact hn (cantor_endpoints hρ hρ4).1
    · intro he; subst x; exact hn (cantor_endpoints hρ hρ4).2

theorem measure_cantorOpen_le {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    volume (cantorOpen ρ) ≤ ENNReal.ofReal (2*ρ) := by
  have hF := measure_cantorSet_inter_parent_lower hρ hρ4 0 ()
  have he : cantorInterval ρ 0 () = Icc (-1) 1 := by norm_num [cantorInterval, cantorLeft, cantorLength]
  rw [he, inter_eq_left.mpr (cantorSet_subset_interval ρ)] at hF
  simp only [cantorLength] at hF
  have hfin : volume (cantorSet ρ) ≠ ⊤ := (isCompact_cantorSet ρ).measure_ne_top
  rw [cantorOpen_eq_diff hρ hρ4, MeasureTheory.measure_sdiff (cantorSet_subset_interval ρ)
    (isClosed_cantorSet ρ).measurableSet.nullMeasurableSet hfin, Real.volume_Icc]
  have hh := tsub_le_tsub_left hF (ENNReal.ofReal (1-(-1 : ℝ)))
  have hn : 0 ≤ (1-ρ)*2 := by nlinarith
  rw [← ENNReal.ofReal_sub _ hn] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem cantorGap_eq_Ioo (ρ : ℝ) (g : CantorGapIndex ρ) :
    cantorGap ρ g = Ioo (gapLeft ρ g) (gapRight ρ g) := rfl

theorem gapIndex_valid {ρ : ℝ} (g : CantorGapIndex ρ) :
    g.2.2.val+1 < cantorBranching ρ g.1 := by have := g.2.2.isLt; omega

theorem gap_endpoints_mem {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (g : CantorGapIndex ρ) :
    gapLeft ρ g ∈ cantorSet ρ ∧ gapRight ρ g ∈ cantorSet ρ :=
  cantorStageGap_endpoints hρ hρ4 _ _ (gapIndex_valid g)

theorem gap_width_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (g : CantorGapIndex ρ) :
    gapLeft ρ g < gapRight ρ g := by
  have hh := cantorGap_length ρ g.1 g.2.1 g.2.2
  have hp := cantorGapLength_pos hρ hρ4 g.1
  change cantorGapLeft ρ g.1 g.2.1 g.2.2 < cantorGapRight ρ g.1 g.2.1 g.2.2
  linarith

theorem cantorGap_subset_open {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (g : CantorGapIndex ρ) :
    cantorGap ρ g ⊆ cantorOpen ρ := by
  intro x hx
  have he := gap_endpoints_mem hρ hρ4 g
  have hl := cantorSet_subset_interval ρ he.1
  have hr := cantorSet_subset_interval ρ he.2
  refine ⟨⟨hl.1.trans_lt hx.1, hx.2.trans_le hr.2⟩, ?_⟩
  exact fun hF => Set.disjoint_left.mp
    (cantorStageGap_disjoint_set hρ hρ4 _ _ (gapIndex_valid g)) hx hF

theorem exists_cantorGap {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∈ cantorOpen ρ) :
    ∃ g : CantorGapIndex ρ, x ∈ cantorGap ρ g := by
  classical
  have hex : ∃ n, x ∉ cantorLevel ρ n := by
    by_contra hh
    push Not at hh
    exact hx.2 (mem_iInter.mpr hh)
  let n := Nat.find hex
  have hn : x ∉ cantorLevel ρ n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro he
    rw [he, cantorLevel_zero] at hn
    exact hn ⟨hx.1.1.le, hx.1.2.le⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : x ∈ cantorLevel ρ k := by
    by_contra hh
    exact Nat.find_min hex (show k < n by omega) hh
  rw [hk] at hn
  obtain ⟨w, hw⟩ := mem_iUnion.mp hprev
  have hsum := cantor_subdivision_length hρ hρ4 k
  have hparent : x ∈ Icc (cantorLeft ρ k w)
      (cantorLeft ρ k w + cantorBranching ρ k*cantorLength ρ (k+1) +
        (cantorBranching ρ k-1 : ℕ)*cantorGapLength ρ k) := by
    refine ⟨hw.1, ?_⟩
    have hw2 : x ≤ cantorLeft ρ k w+cantorLength ρ k := hw.2
    linarith
  have hm : 0 < cantorBranching ρ k := by have := cantorBranching_ge hρ hρ4 k; omega
  rcases parent_covered_by_children_and_gaps hm (cantorLength_pos hρ hρ4 (k+1))
      (cantorGapLength_pos hρ hρ4 k) hparent with hc | hg
  · obtain ⟨i, hi, hxi⟩ := hc
    exact (hn (mem_iUnion.mpr ⟨(w, ⟨i, hi⟩), hxi⟩)).elim
  · obtain ⟨i, hi, hxi⟩ := hg
    exact ⟨⟨k, w, ⟨i, by omega⟩⟩, hxi⟩

theorem cantorOpen_eq_iUnion {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    cantorOpen ρ = ⋃ g : CantorGapIndex ρ, cantorGap ρ g := by
  ext x
  exact ⟨fun hx => mem_iUnion.mpr (exists_cantorGap hρ hρ4 hx),
    fun hx => by obtain ⟨g, hg⟩ := mem_iUnion.mp hx; exact cantorGap_subset_open hρ hρ4 g hg⟩

theorem cantorGap_pairwise_disjoint {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    Pairwise (fun g h : CantorGapIndex ρ => Disjoint (cantorGap ρ g) (cantorGap ρ h)) := by
  rintro ⟨k, w, i⟩ ⟨l, v, j⟩ hne
  change Disjoint (cantorStageGap ρ k w i) (cantorStageGap ρ l v j)
  rcases lt_trichotomy k l with hkl | he | hlk
  · exact cantorStageGap_disjoint_later hρ hρ4 hkl w v (by have := i.isLt; omega) (by have := j.isLt; omega)
  · subst l
    by_cases hwv : w = v
    · subst v
      have hij : i.val ≠ j.val := by intro hij; have := Fin.ext hij; subst j; exact hne rfl
      exact subdivisionGap_pairwise_disjoint (L := cantorLeft ρ k w)
        (cantorLength_pos hρ hρ4 (k+1)) (cantorGapLength_pos hρ hρ4 k) hij
    · exact (cantor_interval_pairwise_disjoint hρ hρ4 k hwv).mono
        (cantorStageGap_subset_parent hρ hρ4 k w (by have := i.isLt; omega))
        (cantorStageGap_subset_parent hρ hρ4 k v (by have := j.isLt; omega))
  · exact (cantorStageGap_disjoint_later hρ hρ4 hlk v w (by have := j.isLt; omega) (by have := i.isLt; omega)).symm

end Erdos1132.Counterexample
