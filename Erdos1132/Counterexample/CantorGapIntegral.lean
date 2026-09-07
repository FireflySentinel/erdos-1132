import Erdos1132.Counterexample.GapMiddle

/-! # The inverse-distance contribution of every Cantor stage

Paper: §7.1, the compact set and its gaps.
-/
noncomputable section
open Set MeasureTheory Finset
open scoped BigOperators
namespace Erdos1132.Counterexample

theorem sum_comp_injective_le {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  rw [← Finset.sum_image (fun a _ b _ hab => he hab)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun b _ _ => hf b)

def stageDirectionalGap {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ)
    (w : CantorWord ρ k) (i : Fin (cantorBranching ρ k))
    (j : Fin (cantorBranching ρ k/4)) : CantorGapIndex ρ :=
  ⟨k,w,⟨directionalGap (cantorBranching ρ k) i j, by
    have hh := directionalGap_valid (cantorBranching_ge hρ hρ4 k) i.isLt j.isLt
    omega⟩⟩

theorem stageDirectionalGap_injective {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k : ℕ) (w : CantorWord ρ k) (i : Fin (cantorBranching ρ k)) :
    Function.Injective (stageDirectionalGap hρ hρ4 k w i) := by
  intro j l he
  have hh := congrArg (fun g : CantorGapIndex ρ => g.2.2.val) he
  exact directionalGap_injective (cantorBranching_ge hρ hρ4 k) i.isLt hh

theorem stageDirectionalGap_integral_lower {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hxF : x ∈ cantorSet ρ) (k : ℕ) (w : CantorWord ρ k)
    (i : Fin (cantorBranching ρ k)) (hx : x ∈ cantorInterval ρ (k+1) (w,i))
    (j : Fin (cantorBranching ρ k/4)) :
    cantorProportion ρ k/4 * (1/((j:ℝ)+1)) ≤
      ∫ y in gapMiddle ρ (stageDirectionalGap hρ hρ4 k w i j), 1/|x-y| := by
  let D := 2*((j:ℝ)+1)*cantorLength ρ k/cantorBranching ρ k
  have hm := cantorBranching_ge hρ hρ4 k
  have hm0 : (0:ℝ) < cantorBranching ρ k := by exact_mod_cast (show 0 < cantorBranching ρ k by omega)
  have hj0 : 0 < (j:ℝ)+1 := by positivity
  have hD : 0 < D := by dsimp [D]; positivity [cantorLength_pos hρ hρ4 k]
  have hbound : ∀ y ∈ gapMiddle ρ (stageDirectionalGap hρ hρ4 k w i j), |x-y| ≤ D := by
    intro y hy
    have hh := directionalGap_distance hm i.isLt j.isLt (cantorLength_pos hρ hρ4 (k+1))
      (cantorGapLength_pos hρ hρ4 k) hx (gapMiddle_subset_gap hρ hρ4 _ hy)
    have hs := mul_le_mul_of_nonneg_left (cantor_step_bound hρ hρ4 k) hj0.le
    change |x-y| ≤ D
    apply hh.trans
    convert hs using 1 <;> dsimp [D] <;> ring
  have hh := integral_gapMiddle_inverse_lower hρ hρ4 hxF
    (stageDirectionalGap hρ hρ4 k w i j) hD hbound
  change cantorGapLength ρ k/(2*D) ≤ _ at hh
  apply le_trans _ hh
  have hlo := div_le_div_of_nonneg_right (cantorGapLength_lower hρ hρ4 k)
    (show 0 ≤ 2*D by positivity)
  apply le_trans _ hlo
  dsimp [D]
  have hlen := cantorLength_pos hρ hρ4 k
  apply le_of_eq
  field_simp
  <;> ring

theorem cantor_stage_gap_integral_lower {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hx : x ∈ cantorSet ρ) (k : ℕ) :
    (1/16 : ℝ) ≤ ∑ w : CantorWord ρ k, ∑ i : Fin (cantorBranching ρ k-1),
      ∫ y in gapMiddle ρ ⟨k,w,i⟩, 1/|x-y| := by
  classical
  obtain ⟨v, hv⟩ := mem_iUnion.mp (mem_iInter.mp hx (k+1))
  let e : Fin (cantorBranching ρ k/4) → Fin (cantorBranching ρ k-1) :=
    fun j => (stageDirectionalGap hρ hρ4 k v.1 v.2 j).2.2
  have he : Function.Injective e := by
    intro a b hab
    apply directionalGap_injective (cantorBranching_ge hρ hρ4 k) v.2.isLt
    exact congrArg Fin.val hab
  have hsmall := sum_le_sum (s := (univ : Finset (Fin (cantorBranching ρ k/4))))
    (fun j _ => stageDirectionalGap_integral_lower hρ hρ4 hx k v.1 v.2 hv j)
  have hsum : (∑ j : Fin (cantorBranching ρ k/4), cantorProportion ρ k/4*(1/((j:ℝ)+1))) =
      cantorProportion ρ k/4*(harmonic (cantorBranching ρ k/4):ℝ) := by
    rw [← mul_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1/((j:ℝ)+1))]
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, one_div]
  rw [hsum] at hsmall
  have hquarter := quarter_harmonic_bound (cantorProportion_pos hρ k)
    (cantorProportion_le_eighth hρ hρ4 k) (cantorBranching_ge hρ hρ4 k)
    (cantorProportion_log_branching hρ k)
  have heSum := sum_comp_injective_le e he
    (fun i => ∫ y in gapMiddle ρ ⟨k,v.1,i⟩, 1/|x-y|)
    (fun _ => integral_nonneg (fun _ => by positivity))
  have hparent := single_le_sum (f := fun w : CantorWord ρ k =>
    ∑ i : Fin (cantorBranching ρ k-1), ∫ y in gapMiddle ρ ⟨k,w,i⟩, 1/|x-y|)
    (fun w _ => sum_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))) (mem_univ v.1)
  exact hquarter.trans (hsmall.trans (heSum.trans hparent))

end Erdos1132.Counterexample
