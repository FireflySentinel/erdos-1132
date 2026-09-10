import Erdos1132.Additive.TaoPotential

/-! # Positivity of the density forced by a decrease of the logarithmic potential

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Set Filter Real
open scoped Topology
namespace Erdos1132

theorem density_lower_of_two_heights {C e h ρ α U₁ U₂ : ℝ}
    (hh : 0 < h) (hCh : C*h ≤ 1/256) (hCe : C*e ≤ h^2/1024)
    (hdrop : h^2/32 ≤ U₁-U₂)
    (h₁ : |U₁-α+Real.pi*(h/2)*ρ| ≤ C*(e+(h/2)^3))
    (h₂ : |U₂-α+Real.pi*h*ρ| ≤ C*(e+h^3)) :
    h/(64*Real.pi) ≤ ρ := by
  have h₁' := (abs_le.mp h₁).2
  have h₂' := (abs_le.mp h₂).1
  have hcubic := mul_le_mul_of_nonneg_right hCh (sq_nonneg h)
  have hmain : h^2/64 ≤ Real.pi*h*ρ/2 := by nlinarith
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  have hfactor : h*(h-64*Real.pi*ρ) ≤ 0 := by nlinarith
  have hl : h-64*Real.pi*ρ ≤ 0 := by
    by_contra he
    exact (mul_pos hh (lt_of_not_ge he)).not_ge hfactor
  nlinarith

/-- The density is bounded below uniformly for all sufficiently large rows of
any array with the stated eventual intervalwise Lebesgue bound. -/
theorem eventually_exterior_density_positive (X : ∀ n, Nodes n) {a b d : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d)
    (hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (a+d) (b-d),
      c ≤ (X n).exteriorDensity a b (X n).potentialNormalization x 0 := by
  obtain ⟨C, hC, hest⟩ := uniform_complex_potential_expansion hab hI hd
  let h := min 1 (1/(256*(C+1)))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hh1 : h ≤ 1 := min_le_left _ _
  have hCh : C*h ≤ 1/256 := by
    have hhmax : h ≤ 1/(256*(C+1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 256*(C+1))).mp hhmax
    nlinarith
  have hε : ∀ᶠ n : ℕ in atTop, C*potentialErrorSize n ≤ h^2/1024 := by
    have ht : Tendsto (fun n => C*potentialErrorSize n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_potentialErrorSize.const_mul C
    exact (ht.eventually (Iio_mem_nhds (by positivity : 0 < h^2/1024))).mono (fun _ hn => hn.le)
  have hinv : ∀ᶠ n : ℕ in atTop, 1/(n : ℝ) ≤ h/2 :=
    (tendsto_one_div_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds (by positivity : (0 : ℝ) < h/2))).mono (fun _ hn => hn.le)
  refine ⟨h/(64*Real.pi), by positivity, ?_⟩
  filter_upwards [hΛ, hε, hinv, eventually_gt_atTop (0 : ℕ)] with n hnΛ hnε hni hn
  intro x hx
  have h1 := hest n (X n) hn hnΛ x hx (h/2) hni
  have h2 := hest n (X n) hn hnΛ x hx h (hni.trans (by linarith))
  have hdrop := (X n).complexLogPotential_height_drop hn
    (hI (mem_interval_of_inset hd.le hx)) hh hh1
  exact density_lower_of_two_heights hh hCh hnε hdrop h1 h2

end Erdos1132
