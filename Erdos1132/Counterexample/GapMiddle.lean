import Erdos1132.Counterexample.CantorRadius
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Middle halves of gaps and an explicit one-sided block

Companion note: §2.1, the compact set and its gaps.
-/
noncomputable section
open Set MeasureTheory Finset
open scoped BigOperators
namespace Erdos1132.Counterexample

def gapMiddle (ρ : ℝ) (g : CantorGapIndex ρ) : Set ℝ :=
  Icc (gapLeft ρ g+(gapRight ρ g-gapLeft ρ g)/4)
    (gapRight ρ g-(gapRight ρ g-gapLeft ρ g)/4)

theorem gapMiddle_subset_gap {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (g : CantorGapIndex ρ) :
    gapMiddle ρ g ⊆ cantorGap ρ g := by
  intro x hx
  have hp := gap_width_pos hρ hρ4 g
  change gapLeft ρ g < x ∧ x < gapRight ρ g
  constructor <;> linarith [hx.1,hx.2]

theorem gapMiddle_pairwise_disjoint {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    Pairwise (fun g h : CantorGapIndex ρ => Disjoint (gapMiddle ρ g) (gapMiddle ρ h)) := by
  intro g h hne
  exact (cantorGap_pairwise_disjoint hρ hρ4 hne).mono
    (gapMiddle_subset_gap hρ hρ4 g) (gapMiddle_subset_gap hρ hρ4 h)

theorem integral_gapMiddle_inverse_lower {ρ x D : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hx : x ∈ cantorSet ρ) (g : CantorGapIndex ρ) (hD : 0 < D)
    (hbound : ∀ y ∈ gapMiddle ρ g, |x-y| ≤ D) :
    cantorGapLength ρ g.1/(2*D) ≤ ∫ y in gapMiddle ρ g, 1/|x-y| := by
  have hne : ∀ y ∈ gapMiddle ρ g, |x-y| ≠ 0 := by
    intro y hy he
    have hyx : y = x := (sub_eq_zero.mp (abs_eq_zero.mp he)).symm
    subst y
    exact (cantorGap_subset_open hρ hρ4 g (gapMiddle_subset_gap hρ hρ4 g hy)).2 hx
  have hi : IntegrableOn (fun y => 1/|x-y|) (gapMiddle ρ g) :=
    (continuousOn_const.div (continuous_const.sub continuous_id).abs.continuousOn hne).integrableOn_Icc
  have hh := setIntegral_mono_on (f := fun _ : ℝ => 1/D) continuous_const.integrableOn_Icc hi
    measurableSet_Icc (fun y hy => one_div_le_one_div_of_le (lt_of_le_of_ne (abs_nonneg _) (hne y hy).symm) (hbound y hy))
  rw [setIntegral_const] at hh
  have hm : volume.real (gapMiddle ρ g) = cantorGapLength ρ g.1/2 := by
    rw [gapMiddle, Real.volume_real_Icc]
    have hw : gapRight ρ g-gapLeft ρ g = cantorGapLength ρ g.1 := cantorGap_length _ _ _ _
    rw [show gapRight ρ g-(gapRight ρ g-gapLeft ρ g)/4-
        (gapLeft ρ g+(gapRight ρ g-gapLeft ρ g)/4) = (gapRight ρ g-gapLeft ρ g)/2 by ring,
      hw, max_eq_left (by positivity [cantorGapLength_pos hρ hρ4 g.1])]
  change volume.real (gapMiddle ρ g)*(1/D) ≤ _ at hh
  rw [hm] at hh
  change cantorGapLength ρ g.1/2*(1/D) ≤ ∫ y in gapMiddle ρ g, 1/|x-y| at hh
  convert hh using 1 <;> ring

def directionalGap (m i j : ℕ) : ℕ := if 2*i < m then i+j else i-1-j

theorem directionalGap_valid {m i j : ℕ} (hm : 32 ≤ m) (hi : i < m) (hj : j < m/4) :
    directionalGap m i j+1 < m := by
  unfold directionalGap
  split_ifs <;> omega

theorem directionalGap_injective {m i : ℕ} (hm : 32 ≤ m) (_hi : i < m) :
    Function.Injective (fun j : Fin (m/4) => directionalGap m i j) := by
  intro j k he
  apply Fin.ext
  unfold directionalGap at he
  split_ifs at he with hside
  · dsimp at he; omega
  · dsimp at he
    have hj := j.isLt; have hk := k.isLt
    omega

theorem directionalGap_distance {L a b x y : ℝ} {m i j : ℕ}
    (hm : 32 ≤ m) (hi : i < m) (hj : j < m/4) (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ childInterval L a b i)
    (hy : y ∈ subdivisionGap L a b (directionalGap m i j)) :
    |x-y| ≤ ((j:ℝ)+1)*(a+b) := by
  have hstep : 0 < a+b := add_pos ha hb
  change childLeft L a b i ≤ x ∧ x ≤ childLeft L a b i+a at hx
  change childLeft L a b (directionalGap m i j)+a < y ∧
    y < childLeft L a b (directionalGap m i j+1) at hy
  unfold directionalGap at hy
  split_ifs at hy with hside
  · simp only [childLeft, Nat.cast_add, Nat.cast_one] at hx hy
    have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    have hprod := mul_nonneg hj0 hstep.le
    rw [abs_of_neg (by nlinarith [hy.1,hx.2] : x-y < 0)]
    nlinarith [hy.2,hx.1]
  · have hjle : j ≤ i-1 := by omega
    have hi1 : 1 ≤ i := by omega
    simp only [childLeft, Nat.cast_add, Nat.cast_sub hjle, Nat.cast_sub hi1, Nat.cast_one] at hx hy
    have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    have hprod := mul_nonneg hj0 hstep.le
    rw [abs_of_pos (by nlinarith [hy.2,hx.1] : 0 < x-y)]
    nlinarith [hy.1,hx.2]

theorem cantor_step_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorLength ρ (k+1)+cantorGapLength ρ k ≤ 2*cantorLength ρ k/cantorBranching ρ k := by
  have ha : cantorLength ρ (k+1) ≤ cantorLength ρ k/cantorBranching ρ k := by
    rw [cantorLength]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith [mul_pos (cantorProportion_pos hρ k) (cantorLength_pos hρ hρ4 k)]
  have hb := cantorGapLength_le_child hρ hρ4 k
  rw [mul_div_assoc]
  linarith

theorem quarter_harmonic_bound {δ : ℝ} {m : ℕ} (hδ : 0 < δ) (hδ8 : δ ≤ 1/8)
    (hm : 32 ≤ m) (hlog : 1 ≤ δ*Real.log m) :
    (1/16 : ℝ) ≤ δ/4 * (harmonic (m/4) : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq : (m:ℝ)/4 ≤ (m/4+1 : ℕ) := by
    have hh : m ≤ 4*(m/4+1) := by omega
    have hhR : (m:ℝ) ≤ 4*(m/4+1 : ℕ) := by exact_mod_cast hh
    linarith
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (m:ℝ)/4) hq
  rw [Real.log_div hm0.ne' (by norm_num)] at hh
  have hH := log_add_one_le_harmonic (m/4)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hmul := mul_le_mul_of_nonneg_left (hh.trans hH) hδ.le
  have hloss := mul_le_mul_of_nonneg_left hlog4 hδ.le
  nlinarith

end Erdos1132.Counterexample
