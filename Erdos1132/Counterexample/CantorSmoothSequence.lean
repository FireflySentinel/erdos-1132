import Erdos1132.Counterexample.CantorProfile
import Erdos1132.Counterexample.CantorGapCompact
import Erdos1132.Counterexample.SmoothApproximation

/-! # The positive smooth amplitude sequence of Section 7 -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Erdos1132.Counterexample

/-- The actual smooth sequence has the eventual logarithmic lower bound at
every point and converges in logarithmic ratio on every open gap. -/
theorem exists_cantor_smooth_sequence {A : ℝ} (hA : 1 < A) :
    ∃ v : ℕ → ℝ → ℝ,
      (∀ j, ContDiff ℝ ∞ (v j)) ∧
      (∀ j x, 0 < v j x ∧ v j x ≤ 1) ∧
      (∀ x ∈ interval, ∀ᶠ j in atTop, A+1 ≤ logarithmicOperator (v j) x/v j x) ∧
      (∀ x ∈ cantorOpen (gapScale A),
        Tendsto (fun j => logarithmicOperator (v j) x/v j x) atTop
          (𝓝 (logarithmicOperator (cantorProfile (gapScale A)) x/cantorProfile (gapScale A) x))) := by
  let ρ := gapScale A
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ4 : ρ ≤ 1/4 := gapScale_le_quarter hA
  let U := cantorOpen ρ
  let u := cantorProfile ρ
  obtain ⟨χ,hχsmooth,hχb,hχone,hχzero,hχlocal⟩ := exists_smooth_cutoff_sequence
    (isOpen_cantorOpen ρ) (fun j => cantorGapCompact ρ (cutoffIndex A (j+1)))
    (fun j => isCompact_cantorGapCompact ρ _) (fun j => cantorGapCompact_subset_open hρ hρ4 _)
  have hχ0 : ∀ j x, x ∉ U → χ j x = 0 := by
    intro j x hx
    obtain ⟨d,hd,hdy⟩ := hχzero j x hx
    exact hdy x (by simpa using hd.le)
  have hχ1 : ∀ x ∈ U, ∀ᶠ j in atTop, χ j x = 1 := by
    intro x hx
    obtain ⟨r,hr,hj⟩ := hχlocal x hx
    filter_upwards [hj] with j hj
    exact hj x (by simpa using hr)
  let v := cutoffApproximation χ u
  have hvs : ∀ j, ContDiff ℝ ∞ (v j) := fun j => smoothCutoff_contDiff (hχsmooth j)
    (fun x hx => cantorProfile_contDiffAt hρ hρ4 hx) (hχzero j)
  have hvb : ∀ j x, 0 < v j x ∧ v j x ≤ 1 := by
    intro j x
    have hh := smoothCutoff_bounds (hχb j x) (cantorProfile_bounds hρ hρ4 x)
      (show 0 ≤ 1/((j:ℝ)+1) ∧ 1/((j:ℝ)+1) ≤ 1 from
        ⟨by positivity, div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by positivity)⟩)
    refine ⟨?_,hh.2⟩
    by_cases hx : x ∈ U
    · exact smoothCutoff_pos (hχb j x) (cantorProfile_pos hρ hρ4 hx) (by positivity)
    · simp only [v,cutoffApproximation,smoothCutoff,hχ0 j x hx,zero_mul,sub_zero,one_mul,zero_add]
      positivity
  have hvL1 := cutoffApproximation_L1_tendsto (cantorProfile_measurable hρ hρ4)
    (cantorProfile_bounds hρ hρ4) (fun j => (hχsmooth j).continuous.measurable) hχb
    (fun x hx => cantorProfile_zero hρ hρ4 hx) hχ0 hχ1
  have hvpoint : ∀ x, Tendsto (fun j => v j x) atTop (𝓝 (u x)) :=
    cutoffApproximation_pointwise (fun x hx => cantorProfile_zero hρ hρ4 hx) hχ0 hχ1
  have hratio : ∀ x ∈ U, Tendsto (fun j => logarithmicOperator (v j) x/v j x) atTop
      (𝓝 (logarithmicOperator u x/u x)) := by
    intro x hx
    obtain ⟨r,hr,hloc⟩ := hχlocal x hx
    have hlocal : ∀ᶠ j in atTop, ∀ y ∈ interval, |x-y| < r → v j y = u y := by
      filter_upwards [hloc] with j hj
      intro y _ hy
      simp only [v,cutoffApproximation,smoothCutoff,hj y hy,one_mul,sub_self,zero_mul,add_zero]
    have hLi : ∀ j, IntegrableOn (differenceKernel (v j) x) interval :=
      fun j => smooth_kernel_integrable (hvs j) ⟨hx.1.1.le,hx.1.2.le⟩
    have hvi : ∀ j, IntegrableOn (fun y => v j y-u y) interval := fun j =>
      (hvs j).continuous.continuousOn.integrableOn_Icc.sub (cantorProfile_integrable hρ hρ4)
    have hL := logarithmicOperator_tendsto_of_local_equality ⟨hx.1.1.le,hx.1.2.le⟩ hr hLi
      (cantorProfile_kernel_integrable hA hx) hvi hvL1 hlocal
    exact hL.div (hvpoint x) (cantorProfile_pos hρ hρ4 hx).ne'
  refine ⟨v,hvs,hvb,?_,hratio⟩
  intro x hx
  by_cases hxF : x ∈ cantorSet ρ
  · apply Filter.Eventually.of_forall
    intro j
    have hxU : x ∉ U := fun hh => hh.2 hxF
    obtain ⟨d,hd,hdy⟩ := hχzero j x hxU
    have hdist : ∀ y ∈ interval, cantorRadius ρ y ≤ |x-y| := by
      intro y _
      have hh := cantorRadius_lipschitz_bound hρ hρ4 y x
      rw [cantorRadius_zero hρ hρ4 hxU,sub_zero,abs_of_nonneg (cantorRadius_nonneg hρ hρ4 y),abs_sub_comm] at hh
      exact hh
    have hAi := integrableOn_cutoff_inverseDistance (hχsmooth j).continuous.measurable hd
      (fun y _ => hχb j y) (fun y _ hy => hdy y hy)
    have hAbound := cutoff_integral_lower_of_one_on_gapCompact hρ hρ4 hxF (cutoffIndex A (j+1))
      (fun y _ => (hχb j y).1) hAi (hχone j)
    have hmain := explicit_smoothCutoff_lower_bound (show 0 < j+1 by omega) hx
      (hχsmooth j).continuous.measurable (cantorRadius_continuous hρ hρ4).measurable hd
      (fun y _ => hχb j y) (fun y _ hy => hdy y hy)
      (fun y _ => ⟨cantorRadius_nonneg hρ hρ4 y, by linarith [cantorRadius_bound hρ hρ4 y]⟩)
      hdist hAbound
    have he : smoothCutoff (χ j) (logGapFunction (cantorRadius ρ)) (1/((j+1:ℕ):ℝ)) = v j := by
      simp only [v,cutoffApproximation,u,cantorProfile,Nat.cast_add,Nat.cast_one]
    rw [he] at hmain
    exact (le_div_iff₀ (hvb j x).1).mpr hmain
  · have hxU : x ∈ U := by change x ∈ cantorOpen ρ; rw [cantorOpen_eq_diff hρ hρ4]; exact ⟨hx,hxF⟩
    have hgt : A+1 < logarithmicOperator u x/u x := by
      have hh := cantor_logarithmicRatio_gt hA hxU
      change A+2 < logarithmicOperator u x/u x at hh
      linarith
    filter_upwards [(hratio x hxU).eventually (Ioi_mem_nhds hgt)] with j hj
    exact hj.le

end Erdos1132.Counterexample
