import Erdos1132.Counterexample.CantorProfile

/-! # Arbitrarily large logarithmic ratios on open subintervals of one gap

Paper: §7.2, the logarithmic integral estimate.
-/
noncomputable section
open Set
namespace Erdos1132.Counterexample

/-- Every prescribed ratio is exceeded throughout a small interval beside
the endpoint of the first gap of the fixed Cantor construction. -/
theorem exists_interval_cantor_ratio_gt {A : ℝ} (hA : 1 < A) (D : ℝ) :
    ∃ b c : ℝ, b < c ∧ -1 ≤ b ∧ c ≤ 1 ∧ Ioo b c ⊆ cantorOpen (gapScale A) ∧
      ∀ x ∈ Ioo b c,
        D < logarithmicOperator (cantorProfile (gapScale A)) x/cantorProfile (gapScale A) x := by
  let ρ := gapScale A
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ4 : ρ ≤ 1/4 := gapScale_le_quarter hA
  have hm := cantorBranching_ge hρ hρ4 0
  let g : CantorGapIndex ρ := ⟨0,(),⟨0,by omega⟩⟩
  let b := gapLeft ρ g
  let c := gapRight ρ g
  have hbc : b < c := gap_width_pos hρ hρ4 g
  have he := gap_endpoints_mem hρ hρ4 g
  have hb : -1 ≤ b := (cantorSet_subset_interval ρ he.1).1
  have hc : c ≤ 1 := (cantorSet_subset_interval ρ he.2).2
  let d := min ((c-b)/2) (Real.exp (-512*(D+33))/4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdb : d ≤ (c-b)/2 := min_le_left _ _
  have hde : d ≤ Real.exp (-512*(D+33))/4 := min_le_right _ _
  have hsub : Ioo b (b+d) ⊆ cantorOpen ρ := by
    intro x hx
    apply cantorGap_subset_open hρ hρ4 g
    change b < x ∧ x < c
    exact ⟨hx.1,by linarith [hx.2]⟩
  refine ⟨b,b+d,by linarith,hb,by linarith,hsub,?_⟩
  intro x hx
  have hxg : x ∈ cantorGap ρ g := ⟨hx.1,by change x < c; linarith [hx.2]⟩
  have hr := (cantorRadius_pos_iff hρ hρ4).mpr (hsub hx)
  have hrd : cantorRadius ρ x < d := by
    rw [cantorRadius_eq_on_gap hρ hρ4 g hxg]
    have hh := gapRadius_le_distance hbc (show x ∈ Icc b c from ⟨hx.1.le,by linarith [hx.2]⟩)
    have hh' := hh.trans (min_le_left (x-b) (c-x))
    linarith [hx.2]
  have hsmall : 4*cantorRadius ρ x < Real.exp (-512*(D+33)) := by linarith
  have hlog := Real.log_lt_log (by positivity : 0 < 4*cantorRadius ρ x) hsmall
  rw [Real.log_exp] at hlog
  have hlarge : D < (1/512:ℝ)*Real.log (1/(4*cantorRadius ρ x))-32 := by
    rw [one_div (4*cantorRadius ρ x), Real.log_inv]
    linarith
  exact hlarge.trans_le (cantor_logarithmic_integral_lower_bound hA (hsub hx))

end Erdos1132.Counterexample
