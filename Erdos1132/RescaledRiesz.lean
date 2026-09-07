import Erdos1132.LocalRiesz
import Erdos1132.PolynomialRectangle

/-! # Local differentiation and peak estimates in the original polynomial coordinates -/

noncomputable section
open Polynomial Real Complex Set Metric
namespace Erdos1132

def rescaledPolynomial (p : ℝ[X]) (x ω M : ℝ) (z : ℂ) : ℂ :=
  p.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+z/(ω : ℂ))/(M : ℂ)

theorem rescaledPolynomial_differentiable (p : ℝ[X]) (x ω M : ℝ) :
    Differentiable ℂ (rescaledPolynomial p x ω M) := by
  have hp : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
  exact (hp.comp ((differentiable_id.div_const (ω : ℂ)).const_add (x : ℂ))).div_const _

theorem rescaledPolynomial_deriv (p : ℝ[X]) (x ω M : ℝ) :
    deriv (rescaledPolynomial p x ω M) 0 = ((p.derivative.eval x/(ω*M) : ℝ) : ℂ) := by
  have hi := ((hasDerivAt_id (0 : ℂ)).div_const (ω : ℂ)).const_add (x : ℂ)
  have hp := ((p.hasDerivAt_aeval _).comp 0 hi).div_const (M : ℂ)
  have he := hp.deriv
  change deriv (rescaledPolynomial p x ω M) 0 = _ at he
  rw [he]
  simp only [id_eq, zero_div, add_zero, aeval_def, real_polynomial_eval₂_real, one_div,
    ofReal_div, ofReal_mul]
  ring

theorem rescaledPolynomial_growth {p : ℝ[X]} {x ω M r h R : ℝ}
    (hω : 0 < ω) (hM : 0 < M) (hr : R ≤ ω*r) (hh : R ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|))
    {z : ℂ} (hzre : |z.re| ≤ R) (hzim : |z.im| ≤ R) :
    ‖rescaledPolynomial p x ω M z‖ ≤ Real.exp |z.im| := by
  have hu : |z.re/ω| ≤ r := by
    rw [abs_div, abs_of_pos hω]
    exact (div_le_iff₀ hω).mpr (by nlinarith)
  have hv : |z.im/ω| ≤ h := by
    rw [abs_div, abs_of_pos hω]
    exact (div_le_iff₀ hω).mpr (by nlinarith)
  have he : (x : ℂ)+z/(ω : ℂ) = ((x+z.re/ω : ℝ) : ℂ)+(z.im/ω : ℝ)*I := by
    apply Complex.ext <;> simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
  have hg := hgrowth (z.re/ω) (z.im/ω) hu hv
  have hab : ω*|z.im/ω| = |z.im| := by rw [abs_div, abs_of_pos hω]; field_simp
  rw [hab] at hg
  unfold rescaledPolynomial
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, he]
  exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm M] using hg)

/-- The Riesz derivative estimate after scaling the exponential type to one. -/
theorem polynomial_local_derivative_bound {p : ℝ[X]} {x ω M r h : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hω : 0 < ω) (hM : 0 < M)
    (hr : (m : ℝ)*Real.pi ≤ ω*r) (hh : (m : ℝ)*Real.pi ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|)) :
    |p.derivative.eval x| ≤ ω*M*(1+16/((m : ℝ)*Real.pi)) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have hF := rescaledPolynomial_differentiable p x ω M
  have hb := local_riesz_derivative_bound hm (fun z _ => hF.analyticAt z)
    (fun z hz => by
      have hn : ‖z‖ = (m : ℝ)*Real.pi := by simpa [mem_sphere, dist_eq_norm] using hz
      exact rescaledPolynomial_growth hω hM hr hh hgrowth
        ((Complex.abs_re_le_norm z).trans hn.le) ((Complex.abs_im_le_norm z).trans hn.le))
    (fun y hy => by
      have hg := rescaledPolynomial_growth hω hM hr hh hgrowth
        (z := (y : ℂ)) (by simpa using hy.le) (by simpa using hR.le)
      simpa using hg)
  rw [rescaledPolynomial_deriv, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos (mul_pos hω hM)] at hb
  exact (div_le_iff₀ (mul_pos hω hM)).mp hb |>.trans_eq (by ring)

/-- A derivative close to the sharp bound forces a high value a distance
`π/(2ω)` to the right. -/
theorem polynomial_local_near_equality {p : ℝ[X]} {x ω M r h δ : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hω : 0 < ω) (hM : 0 < M)
    (hr : (m : ℝ)*Real.pi ≤ ω*r) (hh : (m : ℝ)*Real.pi ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|))
    (hderiv : 1-δ ≤ p.derivative.eval x/(ω*M)) :
    M*(1-(Real.pi^2/4)*(δ+16/((m : ℝ)*Real.pi))) ≤ p.eval (x+Real.pi/(2*ω)) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have hF := rescaledPolynomial_differentiable p x ω M
  have hb := local_riesz_near_equality hm (fun z _ => hF.analyticAt z)
    (fun z hz => by
      have hn : ‖z‖ = (m : ℝ)*Real.pi := by simpa [mem_sphere, dist_eq_norm] using hz
      exact rescaledPolynomial_growth hω hM hr hh hgrowth
        ((Complex.abs_re_le_norm z).trans hn.le) ((Complex.abs_im_le_norm z).trans hn.le))
    (fun y hy => by
      have hg := rescaledPolynomial_growth hω hM hr hh hgrowth
        (z := (y : ℂ)) (by simpa using hy.le) (by simpa using hR.le)
      simpa using hg)
    (by simpa only [rescaledPolynomial_deriv, ofReal_re] using hderiv)
  have he : (rescaledPolynomial p x ω M (Real.pi/2)).re = p.eval (x+Real.pi/(2*ω))/M := by
    unfold rescaledPolynomial
    have hi : (x : ℂ)+(Real.pi/2 : ℂ)/(ω : ℂ) = ((x+Real.pi/(2*ω) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hi, real_polynomial_eval₂_real, ← ofReal_div, ofReal_re]
  rw [he] at hb
  simpa only [mul_comm M] using (le_div_iff₀ hM).mp hb

/-- The absolute derivative version, obtained by changing the sign of the real
polynomial when necessary. -/
theorem polynomial_local_peak_abs {p : ℝ[X]} {x ω M r h δ : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hω : 0 < ω) (hM : 0 < M)
    (hr : (m : ℝ)*Real.pi ≤ ω*r) (hh : (m : ℝ)*Real.pi ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|))
    (hderiv : 1-δ ≤ |p.derivative.eval x|/(ω*M)) :
    M*(1-(Real.pi^2/4)*(δ+16/((m : ℝ)*Real.pi))) ≤ |p.eval (x+Real.pi/(2*ω))| := by
  by_cases hp : 0 ≤ p.derivative.eval x
  · have hh := polynomial_local_near_equality hm hω hM hr hh hgrowth
      (by simpa only [abs_of_nonneg hp] using hderiv)
    exact hh.trans (le_abs_self _)
  · have hp' : p.derivative.eval x ≤ 0 := le_of_not_ge hp
    have hg : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
        ‖(-p).eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|) := by
      intro u v hu hv
      simpa only [eval₂_neg, norm_neg] using hgrowth u v hu hv
    have hd : 1-δ ≤ (-p).derivative.eval x/(ω*M) := by
      simpa only [derivative_neg, eval_neg, abs_of_nonpos hp'] using hderiv
    have hb := polynomial_local_near_equality hm hω hM hr hh hg hd
    simp only [eval_neg] at hb
    exact hb.trans (neg_le_abs _)

end Erdos1132
