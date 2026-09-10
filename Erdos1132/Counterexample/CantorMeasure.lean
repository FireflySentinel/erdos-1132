import Erdos1132.Counterexample.CantorDescendants

/-!
# Measure retained inside each Cantor interval

Summability of the removed proportions gives a uniform lower bound for the
measure of the compact limit inside every retained interval.

Companion note: §2.1, the compact set and its gaps.
-/

noncomputable section

open Set MeasureTheory Filter Finset
open scoped Topology BigOperators

namespace Erdos1132.Counterexample

def cantorDescendantMass (ρ : ℝ) (k d : ℕ) : ℝ :=
  (cantorDescendantCount ρ k d : ℝ)*cantorLength ρ (k+d)

theorem cantorDescendantMass_nonneg {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k d : ℕ) :
    0 ≤ cantorDescendantMass ρ k d :=
  mul_nonneg (Nat.cast_nonneg _) (cantorLength_pos hρ hρ4 _).le

theorem cantorDescendantMass_succ {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k d : ℕ) :
    cantorDescendantMass ρ k (d+1) =
      (1-cantorProportion ρ (k+d))*cantorDescendantMass ρ k d := by
  have hm : (cantorBranching ρ (k+d) : ℝ) ≠ 0 := by
    have hh := cantorBranching_ge hρ hρ4 (k+d)
    exact_mod_cast (show cantorBranching ρ (k+d) ≠ 0 by omega)
  change (cantorDescendantCount ρ k (d+1) : ℝ)*cantorLength ρ ((k+d)+1) = _
  rw [cantorDescendantCount, Nat.cast_mul, cantorLength]
  dsimp only [cantorDescendantMass]
  field_simp

theorem cantorDescendantMass_le {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k d : ℕ) :
    cantorDescendantMass ρ k d ≤ cantorLength ρ k := by
  induction d with
  | zero => simp [cantorDescendantMass, cantorDescendantCount]
  | succ d hd =>
    rw [cantorDescendantMass_succ hρ hρ4]
    have hh := mul_nonneg (cantorProportion_pos hρ (k+d)).le
      (cantorDescendantMass_nonneg hρ hρ4 k d)
    nlinarith

theorem cantorDescendantMass_lower {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k d : ℕ) :
    (1-∑ j ∈ range d, cantorProportion ρ (k+j))*cantorLength ρ k ≤
      cantorDescendantMass ρ k d := by
  induction d with
  | zero => simp [cantorDescendantMass, cantorDescendantCount]
  | succ d hd =>
    rw [sum_range_succ, cantorDescendantMass_succ hρ hρ4]
    have hh := mul_le_mul_of_nonneg_left (cantorDescendantMass_le hρ hρ4 k d)
      (cantorProportion_pos hρ (k+d)).le
    nlinarith

theorem cantorProportion_tail_sum_le {ρ : ℝ} (hρ : 0 < ρ) (k d : ℕ) :
    (∑ j ∈ range d, cantorProportion ρ (k+j)) ≤ ρ := by
  have hh : ∀ j, cantorProportion ρ (k+j) ≤ cantorProportion ρ j := by
    intro j
    unfold cantorProportion
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hsum := (cantorProportion_sum ρ).summable.sum_le_tsum (range d)
    (fun j _ => (cantorProportion_pos hρ j).le)
  rw [(cantorProportion_sum ρ).tsum_eq] at hsum
  exact (sum_le_sum (fun j _ => hh j)).trans hsum

theorem cantorDescendantMass_lower_uniform {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k d : ℕ) : (1-ρ)*cantorLength ρ k ≤ cantorDescendantMass ρ k d := by
  apply le_trans _ (cantorDescendantMass_lower hρ hρ4 k d)
  apply mul_le_mul_of_nonneg_right _ (cantorLength_pos hρ hρ4 k).le
  linarith [cantorProportion_tail_sum_le hρ k d]

theorem cantorSet_inter_parent_eq {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) :
    cantorSet ρ ∩ cantorInterval ρ k w =
      ⋂ d : ℕ, cantorLevel ρ (k+d) ∩ cantorInterval ρ k w := by
  ext x
  constructor
  · rintro ⟨hx, hw⟩
    exact mem_iInter.mpr (fun d => ⟨mem_iInter.mp hx (k+d), hw⟩)
  · intro hx
    have hbase := mem_iInter.mp hx 0
    refine ⟨mem_iInter.mpr (fun n => ?_), hbase.2⟩
    by_cases hnk : n ≤ k
    · apply cantorLevel_antitone hρ hρ4 hnk
      simpa only [Nat.add_zero] using hbase.1
    · have hh := (mem_iInter.mp hx (n-k)).1
      simpa only [Nat.add_sub_of_le (show k ≤ n by omega)] using hh

theorem measure_cantorSet_inter_parent_lower {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) :
    ENNReal.ofReal ((1-ρ)*cantorLength ρ k) ≤ volume (cantorSet ρ ∩ cantorInterval ρ k w) := by
  have ha : Antitone (fun d : ℕ => cantorLevel ρ (k+d) ∩ cantorInterval ρ k w) := by
    intro i j hij
    exact inter_subset_inter_left _ (cantorLevel_antitone hρ hρ4 (Nat.add_le_add_left hij k))
  have hm : ∀ d : ℕ, MeasurableSet (cantorLevel ρ (k+d) ∩ cantorInterval ρ k w) :=
    fun d => (isCompact_cantorLevel ρ (k+d)).measurableSet.inter measurableSet_Icc
  have hfin : volume (cantorLevel ρ (k+0) ∩ cantorInterval ρ k w) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp [cantorInterval, Real.volume_Icc])
      (measure_mono inter_subset_right)
  rw [cantorSet_inter_parent_eq hρ hρ4 k w, ha.measure_iInter (fun d => (hm d).nullMeasurableSet) ⟨0, hfin⟩]
  apply le_iInf
  intro d
  rw [measure_cantorLevel_inter_parent hρ hρ4 k d w]
  exact ENNReal.ofReal_le_ofReal (cantorDescendantMass_lower_uniform hρ hρ4 k d)

theorem measure_cantorSet_inter_parent_half {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) :
    ENNReal.ofReal (cantorLength ρ k/2) ≤ volume (cantorSet ρ ∩ cantorInterval ρ k w) := by
  apply le_trans _ (measure_cantorSet_inter_parent_lower hρ hρ4 k w)
  apply ENNReal.ofReal_le_ofReal
  nlinarith [cantorLength_pos hρ hρ4 k]

end Erdos1132.Counterexample
