import Erdos1132.Counterexample.CantorLevels

/-!
# Descendants inside a retained interval

A word has one ancestor at every earlier level. The descendants are counted
recursively, and their intervals give the exact part of a later level that
lies inside the ancestor interval.

Companion note: §2.1, the compact set and its gaps.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Erdos1132.Counterexample

def cantorAncestor (ρ : ℝ) (k : ℕ) : (d : ℕ) → CantorWord ρ (k+d) → CantorWord ρ k
  | 0, w => w
  | d+1, w => cantorAncestor ρ k d w.1

def CantorDescendant (ρ : ℝ) (k : ℕ) (w : CantorWord ρ k) (d : ℕ) :=
  {u : CantorWord ρ (k+d) // cantorAncestor ρ k d u = w}

instance cantorDescendantFintype (ρ : ℝ) (k : ℕ) (w : CantorWord ρ k) (d : ℕ) :
    Fintype (CantorDescendant ρ k w d) := by
  classical
  exact inferInstanceAs (Fintype {u : CantorWord ρ (k+d) // cantorAncestor ρ k d u = w})

def cantorDescendantCount (ρ : ℝ) (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | d+1 => cantorDescendantCount ρ k d * cantorBranching ρ (k+d)

theorem cantorDescendant_card (ρ : ℝ) (k d : ℕ) (w : CantorWord ρ k) :
    Fintype.card (CantorDescendant ρ k w d) = cantorDescendantCount ρ k d := by
  induction d with
  | zero =>
    let e : CantorDescendant ρ k w 0 ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨w, rfl⟩
        left_inv := fun u => Subtype.ext u.property.symm
        right_inv := fun u => Subsingleton.elim _ _ }
    simpa [cantorDescendantCount] using Fintype.card_congr e
  | succ d hd =>
    let e : CantorDescendant ρ k w (d+1) ≃
        CantorDescendant ρ k w d × Fin (cantorBranching ρ (k+d)) :=
      { toFun := fun u => (⟨u.val.1, u.property⟩, u.val.2)
        invFun := fun u => ⟨(u.1.val, u.2), u.1.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa only [Fintype.card_prod, Fintype.card_fin, hd, cantorDescendantCount] using
      Fintype.card_congr e

theorem cantor_interval_subset_ancestor {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k d : ℕ) (u : CantorWord ρ (k+d)) :
    cantorInterval ρ (k+d) u ⊆ cantorInterval ρ k (cantorAncestor ρ k d u) := by
  induction d with
  | zero => exact Subset.rfl
  | succ d hd =>
    exact (cantor_child_subset hρ hρ4 (k+d) u).trans (hd u.1)

theorem cantorLevel_inter_parent {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k d : ℕ) (w : CantorWord ρ k) :
    cantorLevel ρ (k+d) ∩ cantorInterval ρ k w =
      ⋃ u : CantorDescendant ρ k w d, cantorInterval ρ (k+d) u.val := by
  ext x
  constructor
  · rintro ⟨hx, hw⟩
    obtain ⟨u, hu⟩ := mem_iUnion.mp hx
    have he : cantorAncestor ρ k d u = w := by
      by_contra hne
      exact Set.disjoint_left.mp (cantor_interval_pairwise_disjoint hρ hρ4 k hne)
        (cantor_interval_subset_ancestor hρ hρ4 k d u hu) hw
    exact mem_iUnion.mpr ⟨⟨u, he⟩, hu⟩
  · intro hx
    obtain ⟨u, hu⟩ := mem_iUnion.mp hx
    refine ⟨mem_iUnion.mpr ⟨u.val, hu⟩, ?_⟩
    have hh := cantor_interval_subset_ancestor hρ hρ4 k d u.val hu
    simpa only [u.property] using hh

theorem measure_cantorLevel_inter_parent {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (k d : ℕ) (w : CantorWord ρ k) :
    volume (cantorLevel ρ (k+d) ∩ cantorInterval ρ k w) =
      ENNReal.ofReal ((cantorDescendantCount ρ k d : ℝ)*cantorLength ρ (k+d)) := by
  classical
  rw [cantorLevel_inter_parent hρ hρ4 k d w]
  rw [measure_iUnion]
  · simp only [cantorInterval, Real.volume_Icc, add_sub_cancel_left, tsum_fintype,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cantorDescendant_card]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro u v huv
    exact cantor_interval_pairwise_disjoint hρ hρ4 (k+d) (fun he => huv (Subtype.ext he))
  · intro u
    exact measurableSet_Icc

end Erdos1132.Counterexample
