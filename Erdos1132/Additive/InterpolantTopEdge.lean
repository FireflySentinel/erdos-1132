import Erdos1132.Additive.ComplexInterpolant

/-! # The upper-edge estimate at the local exponential type

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Set Complex
namespace Erdos1132

theorem uniform_interpolant_top_edge {l r d : ℝ} (hlr : l < r)
    (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∃ D > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc l r, X.lebesgue y ≤ n) →
      ∀ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) →
      ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ L H ε : ℝ, 0 ≤ L → L ≤ d → 1/(n : ℝ) ≤ H →
        Real.pi*n*H*D*L+C*(1+Real.log n+n*H^3)-Real.log H ≤ Real.pi*n*H*ε →
        ∀ u : ℝ, |u| ≤ L →
          ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+H*I)‖ ≤
            Real.exp ((Real.pi*n*(X.exteriorDensity l r X.potentialNormalization x 0+ε))*H) := by
  obtain ⟨C, hC, hgrowth⟩ := uniform_complex_interpolant_growth hlr hI hd
  obtain ⟨D, hD, hdensity⟩ := uniform_exterior_density_bounds hlr hI hd
  refine ⟨C, hC, D, hD, ?_⟩
  intro n X hn hΛ a ha x hx L H ε hL hLd hH hgap u hu
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hH0 : 0 < H := (one_div_pos.mpr hnR).trans_le hH
  have hx' : x ∈ Icc (l+d) (r-d) := by constructor <;> linarith [hx.1, hx.2]
  have hu' : x+u ∈ Icc (l+d) (r-d) := by
    constructor <;> linarith [hx.1, hx.2, (abs_le.mp hu).1, (abs_le.mp hu).2]
  have hg := hgrowth n X hn hΛ a ha (x+u) hu' H hH
  have hlip := (hdensity n X hn hΛ).2 (x+u) hu' x hx'
  simp only [add_sub_cancel_left] at hlip
  have hρ : X.exteriorDensity l r X.potentialNormalization (x+u) 0 ≤
      X.exteriorDensity l r X.potentialNormalization x 0+D*L := by
    have hh := (abs_le.mp hlip).2
    have hm := mul_le_mul_of_nonneg_left hu hD.le
    linarith
  have hmain := mul_le_mul_of_nonneg_left hρ (show 0 ≤ Real.pi*n*H by positivity)
  have he : Real.exp (Real.pi*n*H*X.exteriorDensity l r X.potentialNormalization (x+u) 0+
      C*(1+Real.log n+n*H^3))/H =
      Real.exp (Real.pi*n*H*X.exteriorDensity l r X.potentialNormalization (x+u) 0+
        C*(1+Real.log n+n*H^3)-Real.log H) := by
    rw [Real.exp_sub, Real.exp_log hH0]
  rw [he] at hg
  apply hg.trans
  apply Real.exp_le_exp.mpr
  nlinarith

end Erdos1132
