import Erdos1132.Counterexample.CantorGapIntegral
import Erdos1132.Counterexample.SmoothLowerBound

/-! # Finite compact collections of gap middle halves

Companion note: §2.3, smooth positive approximations.
-/
noncomputable section
open Set MeasureTheory Finset
open scoped BigOperators
namespace Erdos1132.Counterexample

def FiniteGapIndex (ρ : ℝ) (N : ℕ) := Σ k : Fin N, CantorWord ρ k × Fin (cantorBranching ρ k-1)

instance finiteGapIndexFintype (ρ : ℝ) (N : ℕ) : Fintype (FiniteGapIndex ρ N) :=
  inferInstanceAs (Fintype (Σ k : Fin N, CantorWord ρ k × Fin (cantorBranching ρ k-1)))

def finiteGapIndexToGap (ρ : ℝ) (N : ℕ) (g : FiniteGapIndex ρ N) : CantorGapIndex ρ :=
  ⟨g.1.val,g.2⟩

def cantorGapCompact (ρ : ℝ) (N : ℕ) : Set ℝ :=
  ⋃ g : FiniteGapIndex ρ N, gapMiddle ρ (finiteGapIndexToGap ρ N g)

theorem finiteGapIndexToGap_injective (ρ : ℝ) (N : ℕ) : Function.Injective (finiteGapIndexToGap ρ N) := by
  rintro ⟨k,u⟩ ⟨l,v⟩ he
  have hkl : k = l := Fin.ext (congrArg Sigma.fst he)
  subst l
  have huv : u = v := by
    change (⟨k.val,u⟩ : CantorGapIndex ρ) = ⟨k.val,v⟩ at he
    exact eq_of_heq (Sigma.mk.inj he).2
  subst v
  rfl

theorem isCompact_cantorGapCompact (ρ : ℝ) (N : ℕ) : IsCompact (cantorGapCompact ρ N) :=
  isCompact_iUnion (fun _ => isCompact_Icc)

theorem cantorGapCompact_subset_open {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (N : ℕ) :
    cantorGapCompact ρ N ⊆ cantorOpen ρ := by
  intro x hx
  obtain ⟨g,hg⟩ := mem_iUnion.mp hx
  exact cantorGap_subset_open hρ hρ4 _ (gapMiddle_subset_gap hρ hρ4 _ hg)

theorem cantorGapCompact_nonempty {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) {N : ℕ} (hN : 0 < N) :
    (cantorGapCompact ρ N).Nonempty := by
  have hm := cantorBranching_ge hρ hρ4 0
  let g : FiniteGapIndex ρ N := ⟨⟨0,hN⟩,(),⟨0,by change 0 < cantorBranching ρ 0-1; omega⟩⟩
  have hp := gap_width_pos hρ hρ4 (finiteGapIndexToGap ρ N g)
  refine ⟨(gapLeft ρ (finiteGapIndexToGap ρ N g)+gapRight ρ (finiteGapIndexToGap ρ N g))/2,
    mem_iUnion.mpr ⟨g, ?_⟩⟩
  constructor <;> linarith

theorem integrableOn_gapMiddle_inverse {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hx : x ∈ cantorSet ρ) (g : CantorGapIndex ρ) :
    IntegrableOn (fun y => 1/|x-y|) (gapMiddle ρ g) := by
  apply ContinuousOn.integrableOn_Icc
  apply continuousOn_const.div (continuous_const.sub continuous_id).abs.continuousOn
  intro y hy he
  have hxy : x = y := sub_eq_zero.mp (abs_eq_zero.mp he)
  subst y
  exact (cantorGap_subset_open hρ hρ4 _ (gapMiddle_subset_gap hρ hρ4 _ hy)).2 hx

theorem integral_cantorGapCompact_lower {ρ x : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hx : x ∈ cantorSet ρ) (N : ℕ) :
    (N:ℝ)/16 ≤ ∫ y in cantorGapCompact ρ N, 1/|x-y| := by
  classical
  have hdis : Pairwise (fun g h : FiniteGapIndex ρ N =>
      Disjoint (gapMiddle ρ (finiteGapIndexToGap ρ N g)) (gapMiddle ρ (finiteGapIndexToGap ρ N h))) :=
    fun g h hne => gapMiddle_pairwise_disjoint hρ hρ4
      (fun he => hne (finiteGapIndexToGap_injective ρ N he))
  have hmeas : ∀ g : FiniteGapIndex ρ N, MeasurableSet (gapMiddle ρ (finiteGapIndexToGap ρ N g)) := fun _ => measurableSet_Icc
  rw [cantorGapCompact, integral_iUnion_fintype hmeas hdis
    (fun g => integrableOn_gapMiddle_inverse hρ hρ4 hx _)]
  change (N:ℝ)/16 ≤ ∑ g : (Σ k : Fin N, CantorWord ρ k × Fin (cantorBranching ρ k-1)),
    ∫ y in gapMiddle ρ ⟨g.1.val,g.2⟩, 1/|x-y|
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, finiteGapIndexToGap]
  have hh := sum_le_sum (s := (univ : Finset (Fin N)))
    (fun k _ => cantor_stage_gap_integral_lower hρ hρ4 hx k)
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div] using hh

theorem cutoff_integral_lower_of_one_on_gapCompact {ρ x : ℝ} {χ : ℝ → ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hx : x ∈ cantorSet ρ) (N : ℕ)
    (hχ : ∀ y ∈ interval, 0 ≤ χ y)
    (hi : IntegrableOn (fun y => χ y/|x-y|) interval)
    (hone : ∀ y ∈ cantorGapCompact ρ N, χ y = 1) :
    (N:ℝ)/16 ≤ ∫ y in interval, χ y/|x-y| := by
  have hsub : cantorGapCompact ρ N ⊆ interval := by
    intro y hy
    have hh := cantorGapCompact_subset_open hρ hρ4 N hy
    exact ⟨hh.1.1.le,hh.1.2.le⟩
  have hh := setIntegral_mono_set (s := cantorGapCompact ρ N) hi
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy; exact div_nonneg (hχ y hy) (abs_nonneg _))
    (Filter.Eventually.of_forall hsub)
  have he : (∫ y in cantorGapCompact ρ N, χ y/|x-y|) =
      ∫ y in cantorGapCompact ρ N, 1/|x-y| := by
    apply setIntegral_congr_fun (isCompact_cantorGapCompact ρ N).measurableSet
    intro y hy
    dsimp
    rw [hone y hy]
  rw [he] at hh
  exact (integral_cantorGapCompact_lower hρ hρ4 hx N).trans hh

end Erdos1132.Counterexample
