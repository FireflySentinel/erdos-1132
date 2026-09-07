import Erdos1132.Additive.EquispacedInterpolation
import Erdos1132.Additive.LocalPhragmenLindelof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Local exponential growth for a real polynomial

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Finset Set Complex
open scoped ComplexConjugate
namespace Erdos1132

theorem real_polynomial_eval₂_conj (p : ℝ[X]) (z : ℂ) :
    p.eval₂ (algebraMap ℝ ℂ) (conj z) = conj (p.eval₂ (algebraMap ℝ ℂ) z) := by
  exact Polynomial.aeval_conj p z

theorem real_polynomial_eval₂_real (p : ℝ[X]) (x : ℝ) :
    p.eval₂ (algebraMap ℝ ℂ) (x : ℂ) = (p.eval x : ℝ) := by
  exact p.eval₂_at_apply (algebraMap ℝ ℂ) x

/-- The real interval bound supplies the bottom and vertical edges; only the
upper edge needs the logarithmic-potential estimate. -/
theorem polynomial_rectangle_growth {p : ℝ[X]} {n : ℕ} {l r x L H A ω : ℝ}
    (hn : 0 < n) (hlr : l < r) (hI : Set.Icc l r ⊆ Set.Icc (-1) 1)
    (hL : 0 < L) (hH : 0 < H) (hH1 : H ≤ 1) (hA : 0 < A) (hω : 0 ≤ ω)
    (hxL : l ≤ x-L) (hxR : x+L ≤ r) (hp : p.degree < n)
    (hreal : ∀ y ∈ Set.Icc l r, |p.eval y| ≤ A)
    (htop : ∀ u : ℝ, |u| ≤ L →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+H*I)‖ ≤ A*Real.exp (ω*H))
    {u v : ℝ} (hu : |u| ≤ L/2) (hv : |v| ≤ H) :
    ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤
      A*Real.exp (4*((2+4/(r-l))*(n : ℝ)^2)*Real.exp (-L/(2*H)))*Real.exp (ω*|v|) := by
  let B : ℝ := (2+4/(r-l))*(n : ℝ)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (t : ℝ) (ht : |t| ≤ L) : x+t ∈ Set.Icc l r := by
    constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  have hupper (s t : ℝ) (hs : |s| ≤ L/2) (ht0 : 0 ≤ t) (ht1 : t ≤ H) :
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+s : ℝ)+t*I)‖ ≤
        A*Real.exp (4*B*Real.exp (-L/(2*H)))*Real.exp (ω*t) := by
    let f : ℂ → ℂ := fun z => p.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+z)
    have hf : Differentiable ℂ f := by
      have ha : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
      exact ha.comp (differentiable_id.const_add (x : ℂ))
    have he (z : ℂ) : (x : ℂ)+z = ((x+z.re : ℝ) : ℂ)+z.im*I := by
      rw [ofReal_add, add_assoc, Complex.re_add_im]
    have hb (z : ℂ) (hz : |z.re| ≤ L) (hz0 : z.im = 0) : ‖f z‖ ≤ A := by
      dsimp [f]
      rw [he, hz0]
      simp only [ofReal_zero, zero_mul, add_zero, real_polynomial_eval₂_real,
        Complex.norm_real, Real.norm_eq_abs]
      exact hreal _ (hi _ hz)
    have htop' (z : ℂ) (hz : |z.re| ≤ L) (hzH : z.im = H) : ‖f z‖ ≤ A*Real.exp (ω*H) := by
      dsimp [f]
      rw [he, hzH]
      exact htop z.re hz
    have hside (z : ℂ) (hz : |z.re| = L) (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ H) :
        ‖f z‖ ≤ A*Real.exp B := by
      apply polynomial_complex_exponential_bound hn hlr hI hA.le hp hreal
      rw [he]
      have hx1 := abs_le.mpr (hI (hi z.re hz.le))
      have ht := norm_add_le ((x+z.re : ℝ) : ℂ) ((z.im : ℂ)*I)
      simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hz0] at ht
      linarith
    have hout := local_exponential_growth hL hH hA hB hω hf hb htop' hside
      (z := (s : ℂ)+t*I) (by simpa using hs) (by simpa using ht0) (by simpa using ht1)
    convert! hout using 1 <;> simp [f, ofReal_add, add_assoc]
  by_cases hv0 : 0 ≤ v
  · simpa only [abs_of_nonneg hv0] using hupper u v hu hv0 ((le_abs_self v).trans hv)
  · have hv' : v ≤ 0 := le_of_not_ge hv0
    have hn := hupper u (-v) hu (neg_nonneg.mpr hv') (by simpa [abs_of_nonpos hv'] using hv)
    have he : (((x+u : ℝ) : ℂ)+(-v : ℝ)*I) = conj (((x+u : ℝ) : ℂ)+v*I) := by simp
    rw [he, real_polynomial_eval₂_conj, norm_conj] at hn
    simpa only [abs_of_nonpos hv'] using hn

end Erdos1132
