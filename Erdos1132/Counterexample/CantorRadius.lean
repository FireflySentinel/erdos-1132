import Erdos1132.Counterexample.CantorOpen
import Erdos1132.Counterexample.GapGeometry
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # A globally Lipschitz radius, polynomial on each gap

Companion note: §2.2, the logarithmic integral estimate.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace Erdos1132.Counterexample

private def selectedGap (ρ x : ℝ) (h : ∃ g : CantorGapIndex ρ, x ∈ cantorGap ρ g) : CantorGapIndex ρ :=
  Classical.choose h

def cantorRadius (ρ x : ℝ) : ℝ := by
  classical
  exact if h : ∃ g : CantorGapIndex ρ, x ∈ cantorGap ρ g then
    gapRadius (gapLeft ρ (selectedGap ρ x h)) (gapRight ρ (selectedGap ρ x h)) x
  else 0

theorem cantorRadius_eq_on_gap {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (g : CantorGapIndex ρ) (hx : x ∈ cantorGap ρ g) :
    cantorRadius ρ x = gapRadius (gapLeft ρ g) (gapRight ρ g) x := by
  classical
  have hex : ∃ g : CantorGapIndex ρ, x ∈ cantorGap ρ g := ⟨g, hx⟩
  rw [cantorRadius, dif_pos hex]
  have he : selectedGap ρ x hex = g := by
    by_contra hn
    exact Set.disjoint_left.mp (cantorGap_pairwise_disjoint hρ hρ4 hn)
      (Classical.choose_spec hex) hx
  rw [he]

theorem cantorRadius_zero {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∉ cantorOpen ρ) :
    cantorRadius ρ x = 0 := by
  classical
  unfold cantorRadius
  apply dif_neg
  rintro ⟨g, hg⟩
  exact hx (cantorGap_subset_open hρ hρ4 g hg)

theorem cantorRadius_nonneg {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (x : ℝ) :
    0 ≤ cantorRadius ρ x := by
  by_cases hx : x ∈ cantorOpen ρ
  · obtain ⟨g, hg⟩ := exists_cantorGap hρ hρ4 hx
    rw [cantorRadius_eq_on_gap hρ hρ4 g hg]
    exact (gapRadius_pos hg).le
  · rw [cantorRadius_zero hρ hρ4 hx]

theorem cantorRadius_pos_iff {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    0 < cantorRadius ρ x ↔ x ∈ cantorOpen ρ := by
  constructor
  · intro hh
    by_contra hx
    rw [cantorRadius_zero hρ hρ4 hx] at hh
    exact lt_irrefl _ hh
  · intro hx
    obtain ⟨g, hg⟩ := exists_cantorGap hρ hρ4 hx
    rw [cantorRadius_eq_on_gap hρ hρ4 g hg]
    exact gapRadius_pos hg

theorem gapRadius_le_dist_outside {b c x y : ℝ} (hx : x ∈ Ioo b c) (hy : y ∉ Ioo b c) :
    gapRadius b c x ≤ |x-y| := by
  have hh := gapRadius_le_distance (hx.1.trans hx.2) ⟨hx.1.le, hx.2.le⟩
  change gapRadius b c x ≤ min (x-b) (c-x) at hh
  have hy' : y ≤ b ∨ c ≤ y := by simpa only [mem_Ioo, not_and_or, not_lt] using hy
  rcases hy' with hy | hy
  · exact (hh.trans (min_le_left _ _)).trans (by linarith [le_abs_self (x-y)])
  · exact (hh.trans (min_le_right _ _)).trans (by linarith [neg_le_abs (x-y)])

theorem cantorRadius_lipschitz_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (x y : ℝ) :
    |cantorRadius ρ x-cantorRadius ρ y| ≤ |x-y| := by
  have hnonx := cantorRadius_nonneg hρ hρ4 x
  have hnony := cantorRadius_nonneg hρ hρ4 y
  by_cases hx : x ∈ cantorOpen ρ
  · obtain ⟨g, hg⟩ := exists_cantorGap hρ hρ4 hx
    by_cases hy : y ∈ cantorGap ρ g
    · rw [cantorRadius_eq_on_gap hρ hρ4 g hg, cantorRadius_eq_on_gap hρ hρ4 g hy]
      exact gapRadius_lipschitz (gap_width_pos hρ hρ4 g) ⟨hg.1.le,hg.2.le⟩ ⟨hy.1.le,hy.2.le⟩
    · have hxB : cantorRadius ρ x ≤ |x-y| := by
        rw [cantorRadius_eq_on_gap hρ hρ4 g hg]
        exact gapRadius_le_dist_outside hg hy
      have hyB : cantorRadius ρ y ≤ |x-y| := by
        by_cases hyU : y ∈ cantorOpen ρ
        · obtain ⟨h, hh⟩ := exists_cantorGap hρ hρ4 hyU
          have hne : h ≠ g := by intro he; subst h; exact hy hh
          have hxh : x ∉ cantorGap ρ h := fun hxh =>
            Set.disjoint_left.mp (cantorGap_pairwise_disjoint hρ hρ4 hne) hxh hg
          rw [cantorRadius_eq_on_gap hρ hρ4 h hh]
          simpa only [abs_sub_comm] using (gapRadius_le_dist_outside hh hxh : gapRadius (gapLeft ρ h) (gapRight ρ h) y ≤ |y-x|)
        · rw [cantorRadius_zero hρ hρ4 hyU]; exact abs_nonneg _
      rw [abs_le]
      constructor <;> linarith
  · rw [cantorRadius_zero hρ hρ4 hx, zero_sub, abs_neg, abs_of_nonneg hnony]
    by_cases hy : y ∈ cantorOpen ρ
    · obtain ⟨g, hg⟩ := exists_cantorGap hρ hρ4 hy
      have hxo : x ∉ cantorGap ρ g := fun hh => hx (cantorGap_subset_open hρ hρ4 g hh)
      rw [cantorRadius_eq_on_gap hρ hρ4 g hg]
      simpa only [abs_sub_comm] using (gapRadius_le_dist_outside hg hxo : gapRadius (gapLeft ρ g) (gapRight ρ g) y ≤ |y-x|)
    · rw [cantorRadius_zero hρ hρ4 hy]; exact abs_nonneg _

theorem cantorRadius_lipschitz {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    LipschitzWith 1 (cantorRadius ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using cantorRadius_lipschitz_bound hρ hρ4 x y

theorem cantorRadius_continuous {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    Continuous (cantorRadius ρ) := (cantorRadius_lipschitz hρ hρ4).continuous

theorem cantorLength_le_two {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorLength ρ k ≤ 2 := by
  have hh := cantorLength_bound hρ hρ4 k
  have hp : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem cantorGapLength_le_proportion {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorGapLength ρ k ≤ ρ := by
  have hm := cantorBranching_ge hρ hρ4 k
  have hden : (1 : ℝ) ≤ (cantorBranching ρ k-1 : ℕ) := by exact_mod_cast (show 1 ≤ cantorBranching ρ k-1 by omega)
  have hh := div_le_self (mul_nonneg (cantorProportion_pos hρ k).le (cantorLength_pos hρ hρ4 k).le) hden
  have hp := cantorProportion_le hρ k
  have hl := cantorLength_le_two hρ hρ4 k
  have hb := mul_le_mul hp hl (cantorLength_pos hρ hρ4 k).le (by linarith : 0 ≤ ρ/2)
  change cantorGapLength ρ k ≤ _ at hh
  linarith

theorem cantorRadius_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (x : ℝ) :
    cantorRadius ρ x ≤ ρ/4 := by
  by_cases hx : x ∈ cantorOpen ρ
  · obtain ⟨g, hg⟩ := exists_cantorGap hρ hρ4 hx
    rw [cantorRadius_eq_on_gap hρ hρ4 g hg]
    have hh := gapRadius_le_quarter_length (x := x) (gap_width_pos hρ hρ4 g)
    have hw : gapRight ρ g-gapLeft ρ g = cantorGapLength ρ g.1 := cantorGap_length _ _ _ _
    rw [hw] at hh
    linarith [cantorGapLength_le_proportion hρ hρ4 g.1]
  · rw [cantorRadius_zero hρ hρ4 hx]; positivity

theorem exists_nearby_cantor_endpoint {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∈ cantorOpen ρ) :
    ∃ z ∈ cantorSet ρ, |x-z| ≤ 2*cantorRadius ρ x := by
  obtain ⟨g, hg⟩ := exists_cantorGap hρ hρ4 hx
  rw [cantorRadius_eq_on_gap hρ hρ4 g hg]
  have hd := gapDistance_le_twice_radius (gap_width_pos hρ hρ4 g) ⟨hg.1.le,hg.2.le⟩
  have he := gap_endpoints_mem hρ hρ4 g
  change gapLeft ρ g < x ∧ x < gapRight ρ g at hg
  by_cases hh : x-gapLeft ρ g ≤ gapRight ρ g-x
  · refine ⟨gapLeft ρ g, he.1, ?_⟩
    simpa only [gapDistance, min_eq_left hh, abs_of_pos (sub_pos.mpr hg.1)] using hd
  · refine ⟨gapRight ρ g, he.2, ?_⟩
    rw [abs_of_neg (sub_neg.mpr hg.2)]
    simpa only [gapDistance, min_eq_right (le_of_not_ge hh), neg_sub] using hd

theorem cantorRadius_locally_polynomial {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∈ cantorOpen ρ) :
    ∃ b c : ℝ, b < x ∧ x < c ∧
      cantorRadius ρ =ᶠ[𝓝 x] gapRadius b c := by
  obtain ⟨g, hg⟩ := exists_cantorGap hρ hρ4 hx
  refine ⟨gapLeft ρ g, gapRight ρ g, hg.1, hg.2, ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds hg] with y hy
  exact cantorRadius_eq_on_gap hρ hρ4 g hy

end Erdos1132.Counterexample
