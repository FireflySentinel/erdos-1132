import Erdos1132.Additive.InterpolantTopEdge
import Erdos1132.Additive.PolynomialRectangle
import Erdos1132.Additive.BernsteinScales

/-! # Uniform local growth for all interpolants with bounded nodal data

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Set Complex Filter
open scoped Topology
namespace Erdos1132

def localRectangleLoss (l r : ℝ) (n : ℕ) : ℝ :=
  4*((2+4/(r-l))*(n : ℝ)^2)*Real.exp (-(eighthRoot n)^2/2)

def localFrequency {n : ℕ} (X : Nodes n) (l r x : ℝ) : ℝ :=
  Real.pi*n*(X.exteriorDensity l r X.potentialNormalization x 0+1/eighthRoot n)

/-- The potential estimate and the real interval bound give a common complex
rectangle for every bounded choice of interpolation data. -/
theorem eventually_interpolant_local_growth {l r d : ℝ} (hlr : l < r)
    (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∀ᶠ (n : ℕ) in atTop, ∀ X : Nodes n,
      (∀ y ∈ Icc l r, X.lebesgue y ≤ n) →
      ∀ A : ℝ, 1 ≤ A → (∀ y ∈ Icc l r, X.lebesgue y ≤ A) →
      ∀ x ∈ Icc (l+2*d) (r-2*d), 0 ≤ X.exteriorDensity l r X.potentialNormalization x 0 →
      ∀ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) →
      ∀ u v : ℝ, |u| ≤ (1/(eighthRoot n)^2)/2 → |v| ≤ 1/(eighthRoot n)^4 →
        ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤
          A*Real.exp (localRectangleLoss l r n)*Real.exp (localFrequency X l r x*|v|) := by
  obtain ⟨C, hC, D, hD, htop⟩ := uniform_interpolant_top_edge hlr hI hd
  filter_upwards [eventually_top_edge_scales hC.le hD.le hd] with n hn
  rcases hn with ⟨hn0, ht0, hL, hH0, hH1, hHn, hgap⟩
  intro X hX A hA hXA x hx hρ a ha u v hu hv
  let t := eighthRoot (n : ℝ)
  have hL0 : 0 < 1/t^2 := by positivity
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hω : 0 ≤ localFrequency X l r x := by
    dsimp [localFrequency]
    positivity
  have hleft : l ≤ x-1/t^2 := by linarith [hx.1]
  have hright : x+1/t^2 ≤ r := by linarith [hx.2]
  have htop' (s : ℝ) (hs : |s| ≤ 1/t^2) :
      ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x+s : ℝ)+((1/t^4 : ℝ) : ℂ)*I)‖ ≤
        A*Real.exp (localFrequency X l r x*(1/t^4)) := by
    have hh := htop n X hn0 hX a ha x hx (1/t^2) (1/t^4) (1/t) hL0.le hL hHn hgap s hs
    have hm := mul_le_mul_of_nonneg_right hA
      (Real.exp_pos (localFrequency X l r x*(1/t^4))).le
    exact hh.trans (by simpa only [one_mul, localFrequency] using hm)
  have hg := polynomial_rectangle_growth hn0 hlr hI hL0 hH0 hH1 hA0 hω
    hleft hright (X.degree_interpolant_lt a)
    (fun y hy => (X.interpolant_eval_le a ha y).trans (hXA y hy)) htop' hu hv
  have he : -(1/t^2)/(2*(1/t^4)) = -t^2/2 := by field_simp
  rw [he] at hg
  exact hg

end Erdos1132
