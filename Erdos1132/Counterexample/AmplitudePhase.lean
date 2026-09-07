import Erdos1132.Counterexample.AmplitudePolynomial
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The phase of a zero-free real polynomial

A primitive of `h'/h` on a disk gives a normalized logarithm. Its imaginary
part on the unit circle supplies the phase used in Lemma 9.
-/

noncomputable section

open Set Metric Polynomial Complex
open scoped BigOperators

namespace Erdos1132.Counterexample

def complexPolynomial (h : ℝ[X]) : ℂ[X] := h.map Complex.ofRealHom

@[simp] theorem complexPolynomial_eval_real (h : ℝ[X]) (x : ℝ) :
    (complexPolynomial h).eval (x : ℂ) = ((Polynomial.eval x h : ℝ) : ℂ) := by
  exact Polynomial.eval_map_apply (p := h) (f := Complex.ofRealHom) x

@[simp] theorem complexPolynomial_derivative (h : ℝ[X]) :
    (complexPolynomial h).derivative = complexPolynomial h.derivative := by
  simp [complexPolynomial, Polynomial.derivative_map]

/-- A polynomial nonvanishing on the closed unit disk is nonvanishing on
some larger open disk. -/
theorem exists_zero_free_larger_disk (h : ℂ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) :
    ∃ R : ℝ, 1 < R ∧ ∀ z ∈ ball (0 : ℂ) R, h.eval z ≠ 0 := by
  have hopen : IsOpen {z : ℂ | h.eval z ≠ 0} :=
    isOpen_ne_fun h.continuous continuous_const
  obtain ⟨ε, hε, hsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open
    hopen (fun z hz => hzero z (by simpa using hz))
  rw [thickening_closedBall hε (by norm_num)] at hsub
  exact ⟨ε + 1, by linarith, hsub⟩

/-- The normalized primitive exponentiates to `h/h(0)` throughout the disk. -/
theorem exists_normalized_polynomial_log (h : ℂ[X]) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ z ∈ ball (0 : ℂ) R, h.eval z ≠ 0) :
    ∃ F : ℂ → ℂ, F 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt F (h.derivative.eval z / h.eval z) z) ∧
      ∀ z ∈ ball (0 : ℂ) R, h.eval z = h.eval 0 * Complex.exp (F z) := by
  have hd : DifferentiableOn ℂ (fun z => h.derivative.eval z / h.eval z) (ball 0 R) :=
    h.derivative.differentiableOn.div h.differentiableOn hzero
  obtain ⟨F, hF0, hF⟩ := hd.isExactOn_ball.with_val_at 0 0
  refine ⟨F, hF0, hF, ?_⟩
  let Q : ℂ → ℂ := fun z => h.eval z * Complex.exp (-F z)
  have hQ : ∀ z ∈ ball (0 : ℂ) R, HasDerivAt Q 0 z := by
    intro z hz
    convert! (h.hasDerivAt z).mul (hF z hz).neg.cexp using 1
    field_simp [hzero z hz]
    ring
  intro z hz
  have heq : Q z = Q 0 := isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun y hy => (hQ y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hQ y hy).deriv) hz (mem_ball_self hR)
  dsimp [Q] at heq
  rw [hF0, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg] at heq
  exact (div_eq_iff (Complex.exp_ne_zero _)).mp (by simpa only [div_eq_mul_inv] using heq)

/-- On the real diameter, the normalized logarithm has imaginary part zero. -/
theorem normalized_log_im_real (h : ℝ[X]) {R : ℝ} (hR : 0 < R)
    {F : ℂ → ℂ} (hF0 : F 0 = 0)
    (hF : ∀ z ∈ ball (0 : ℂ) R,
      HasDerivAt F ((complexPolynomial h).derivative.eval z / (complexPolynomial h).eval z) z)
    {x : ℝ} (hx : |x| < R) : (F (x : ℂ)).im = 0 := by
  let f : ℝ → ℝ := fun y => (F (y : ℂ)).im
  have hd : ∀ y ∈ ball (0 : ℝ) R, HasDerivAt f 0 y := by
    intro y hy
    have hyc : (y : ℂ) ∈ ball (0 : ℂ) R := by simpa using hy
    have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hF y hyc).comp_ofReal
    simpa [f, complexPolynomial_derivative] using! hh
  have heq : f x = f 0 := isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℝ) R).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) (by simpa using hx) (mem_ball_self hR)
  simpa [f, hF0] using heq

def circlePoint (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

@[simp] theorem norm_circlePoint (θ : ℝ) : ‖circlePoint θ‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I θ

@[simp] theorem circlePoint_zero : circlePoint 0 = 1 := by simp [circlePoint]

@[simp] theorem circlePoint_pi : circlePoint Real.pi = -1 := by
  simp [circlePoint, Complex.exp_mul_I]

theorem contDiff_circlePoint : ContDiff ℝ ⊤ circlePoint := by
  exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

theorem hasDerivAt_circlePoint (θ : ℝ) :
    HasDerivAt circlePoint (circlePoint θ * Complex.I) θ := by
  simpa [circlePoint] using! (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp

theorem complexPolynomial_eval_circlePoint (h : ℝ[X]) (θ : ℝ) :
    (complexPolynomial h).eval (circlePoint θ) =
      ∑ r ∈ Finset.range (h.natDegree + 1),
        (h.coeff r : ℂ) * circlePoint ((r : ℝ) * θ) := by
  rw [complexPolynomial, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simp only [circlePoint, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The trigonometric polynomial is the real part of the rotated boundary value. -/
theorem amplitudePolynomial_boundary_expansion (h : ℝ[X]) {n : ℕ}
    (hn : h.natDegree < n) (θ : ℝ) :
    (amplitudePolynomial h n).eval (Real.cos θ) =
      Real.cos (n * θ) * ((complexPolynomial h).eval (circlePoint θ)).re +
      Real.sin (n * θ) * ((complexPolynomial h).eval (circlePoint θ)).im := by
  rw [amplitudePolynomial_trig_expansion h hn, complexPolynomial_eval_circlePoint]
  simp [Complex.mul_re, Complex.mul_im, circlePoint, Complex.exp_re, Complex.exp_im]

/-- A smooth phase with zero endpoint values, constructed from the original
zero-free real polynomial. -/
theorem exists_amplitude_phase (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ⊤ ψ ∧ ψ 0 = 0 ∧ ψ Real.pi = 0 ∧
      (∀ θ, HasDerivAt ψ
        (((complexPolynomial h).derivative.eval (circlePoint θ) /
          (complexPolynomial h).eval (circlePoint θ)) *
          (circlePoint θ * Complex.I)).im θ) ∧
      ∀ n : ℕ, h.natDegree < n → ∀ θ : ℝ,
        (amplitudePolynomial h n).eval (Real.cos θ) =
          ‖(complexPolynomial h).eval (circlePoint θ)‖ * Real.cos (n * θ - ψ θ) := by
  obtain ⟨R, hR, hz⟩ := exists_zero_free_larger_disk (complexPolynomial h) hzero
  obtain ⟨F, hF0, hF, hexp⟩ := exists_normalized_polynomial_log (complexPolynomial h)
    (by linarith : 0 < R) hz
  have hcircle (θ : ℝ) : circlePoint θ ∈ ball (0 : ℂ) R := by simpa using hR
  have hFc : ContDiffOn ℂ ⊤ F (ball (0 : ℂ) R) :=
    (show DifferentiableOn ℂ F (ball 0 R) from
      fun z hz => (hF z hz).differentiableAt.differentiableWithinAt).contDiffOn isOpen_ball
  let ψ : ℝ → ℝ := fun θ => (F (circlePoint θ)).im
  have hψc : ContDiff ℝ ⊤ ψ :=
    Complex.imCLM.contDiff.comp
      ((hFc.restrict_scalars ℝ).comp_contDiff contDiff_circlePoint hcircle)
  have hreal (x : ℝ) (hx : |x| < R) : (F (x : ℂ)).im = 0 :=
    normalized_log_im_real h (by linarith : 0 < R) hF0 hF hx
  refine ⟨ψ, hψc, ?_, ?_, ?_, ?_⟩
  · simpa [ψ] using hreal 1 (by simpa using hR)
  · simpa [ψ] using hreal (-1) (by simpa using hR)
  · intro θ
    have hd := (hF _ (hcircle θ)).comp θ (hasDerivAt_circlePoint θ)
    simpa [ψ] using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hd
  · intro n hn θ
    have he := hexp _ (hcircle θ)
    have h0 : (complexPolynomial h).eval 0 = (h.coeff 0 : ℂ) := by
      simpa only [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero] using complexPolynomial_eval_real h 0
    rw [h0] at he
    have hnrm : ‖(complexPolynomial h).eval (circlePoint θ)‖ =
        h.coeff 0 * Real.exp (F (circlePoint θ)).re := by
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, Complex.norm_exp]
    rw [amplitudePolynomial_boundary_expansion h hn, hnrm, he, Real.cos_sub]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_re, Complex.exp_im, ψ]
    ring

end Erdos1132.Counterexample
