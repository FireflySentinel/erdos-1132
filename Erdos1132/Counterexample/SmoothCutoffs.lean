import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Smooth cutoffs adapted to compact subsets of an open set

Companion note: §2.3, smooth positive approximations.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Erdos1132.Counterexample

private theorem exists_small_cutoff_scale {f : ℝ → ℝ} {K : Set ℝ}
    (hf : Continuous f) (hK : IsCompact K) (hpos : ∀ x ∈ K, 0 < f x) (j : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/((j:ℝ)+1) ∧ ∀ x ∈ K, 2*τ ≤ f x := by
  by_cases hne : K.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    refine ⟨min (f z/2) (1/((j:ℝ)+1)), lt_min (by positivity [hpos z hz]) (by positivity), min_le_right _ _, ?_⟩
    intro x hx
    have hh : f z ≤ f x := hmin hx
    have ht := min_le_left (f z/2) (1/((j:ℝ)+1))
    linarith
  · refine ⟨1/((j:ℝ)+1), by positivity, le_rfl, ?_⟩
    intro x hx
    exact (hne ⟨x,hx⟩).elim

/-- The cutoffs equal one on the prescribed compact sets, vanish in a
neighborhood of every point outside the open set, and are eventually
identically one near every point of the open set. -/
theorem exists_smooth_cutoff_sequence {U : Set ℝ} (hU : IsOpen U)
    (K : ℕ → Set ℝ) (hK : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U) :
    ∃ χ : ℕ → ℝ → ℝ,
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧
      (∀ j x, 0 ≤ χ j x ∧ χ j x ≤ 1) ∧
      (∀ j x, x ∈ K j → χ j x = 1) ∧
      (∀ j x, x ∉ U → ∃ d > 0, ∀ y, |x-y| ≤ d → χ j y = 0) ∧
      (∀ x ∈ U, ∃ r > 0, ∀ᶠ j in atTop, ∀ y, |x-y| < r → χ j y = 1) := by
  obtain ⟨f,hsupp,hf,hrange⟩ := hU.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hpos : ∀ x ∈ U, 0 < f x := by
    intro x hx
    have hn : f x ≠ 0 := by rwa [← hsupp] at hx
    exact lt_of_le_of_ne (hrange (mem_range_self x)).1 hn.symm
  have hzero : ∀ x ∉ U, f x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hsupp ▸ hn)
  choose τ hτ hτb hτK using fun j => exists_small_cutoff_scale hf.continuous (hK j)
    (fun x hx => hpos x (hKU j hx)) j
  let χ : ℕ → ℝ → ℝ := fun j x => Real.smoothTransition (f x/τ j-1)
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact Real.smoothTransition.contDiff.comp ((hf.div_const (τ j)).sub contDiff_const)
  · intro j x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro j x hx
    apply Real.smoothTransition.one_of_one_le
    have hh := (le_div_iff₀ (hτ j)).mpr (hτK j x hx)
    linarith
  · intro j x hx
    have hnear : ∀ᶠ y in 𝓝 x, f y < τ j := hf.continuous.continuousAt.eventually
      (Iio_mem_nhds (by rw [hzero x hx]; exact hτ j))
    obtain ⟨d,hd,hdy⟩ := Metric.eventually_nhds_iff.mp hnear
    refine ⟨d/2, by positivity, fun y hy => ?_⟩
    have hh : f y < τ j := hdy (by rw [Real.dist_eq, abs_sub_comm]; linarith)
    apply Real.smoothTransition.zero_of_nonpos
    have hh' := (div_lt_one (hτ j)).mpr hh
    linarith
  · intro x hx
    have hfx := hpos x hx
    have hnear : ∀ᶠ y in 𝓝 x, f x/2 < f y := hf.continuous.continuousAt.eventually
      (Ioi_mem_nhds (by linarith))
    obtain ⟨r,hr,hry⟩ := Metric.eventually_nhds_iff.mp hnear
    refine ⟨r,hr,?_⟩
    have hevent : ∀ᶠ j : ℕ in atTop, 1/((j:ℝ)+1) < f x/4 :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds (by positivity))
    filter_upwards [hevent] with j hj
    intro y hy
    have hfy : f x/2 < f y := hry (by simpa only [Real.dist_eq, abs_sub_comm] using hy)
    have hh : 2*τ j ≤ f y := by linarith [hτb j]
    apply Real.smoothTransition.one_of_one_le
    have hd := (le_div_iff₀ (hτ j)).mpr hh
    linarith

end Erdos1132.Counterexample
