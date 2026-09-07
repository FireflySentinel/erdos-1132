import Erdos1132.Counterexample.PolynomialApproximation
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Quantitative approximation after taking reciprocals

Value and derivative errors are controlled using a common positive lower
bound. The estimates feed directly into stability of the logarithmic ratio.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set Polynomial

namespace Erdos1132.Counterexample

theorem reciprocal_value_error {p f m δ : ℝ}
    (hm : 0 < m) (hp : m ≤ p) (hf : m ≤ f) (herr : |p-f| ≤ δ) :
    |p⁻¹-f⁻¹| ≤ δ/m^2 := by
  have hp0 := hm.trans_le hp
  have hf0 := hm.trans_le hf
  have hid : p⁻¹-f⁻¹ = (f-p)/(p*f) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hp0 hf0), abs_sub_comm]
  apply div_le_div₀ (le_trans (abs_nonneg _) herr) herr (sq_pos_of_pos hm)
  simpa only [pow_two] using mul_le_mul hp hf hm.le hp0.le

theorem reciprocal_derivative_error {p f p' f' m F K δ : ℝ}
    (hm : 0 < m) (hF : 0 ≤ F) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hp : m ≤ p) (hf : m ≤ f) (hpF : p ≤ F+1) (hfF : f ≤ F)
    (hf' : |f'| ≤ K) (hval : |p-f| ≤ δ) (hder : |p'-f'| ≤ δ) :
    |(-p'/p^2)-(-f'/f^2)| ≤ δ/m^2 + K*δ*(2*F+1)/m^4 := by
  have hp0 := hm.trans_le hp
  have hf0 := hm.trans_le hf
  have hid : (-p'/p^2)-(-f'/f^2) =
      (f'-p')/p^2 + f'*(p-f)*(p+f)/(p^2*f^2) := by field_simp; ring
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_div, abs_of_pos (sq_pos_of_pos hp0), abs_sub_comm]
    exact div_le_div₀ hδ hder (sq_pos_of_pos hm) (pow_le_pow_left₀ hm.le hp 2)
  · rw [abs_div, abs_mul, abs_mul, abs_of_pos (add_pos hp0 hf0),
      abs_of_pos (mul_pos (sq_pos_of_pos hp0) (sq_pos_of_pos hf0))]
    apply div_le_div₀ (by positivity)
      (mul_le_mul (mul_le_mul hf' hval (abs_nonneg _) hK)
        (by linarith : p+f ≤ 2*F+1) (by positivity) (by positivity))
      (pow_pos hm 4)
    calc
      m^4 = m^2*m^2 := by ring
      _ ≤ p^2*f^2 := mul_le_mul (pow_le_pow_left₀ hm.le hp 2)
        (pow_le_pow_left₀ hm.le hf 2) (sq_nonneg _) (sq_nonneg _)


/-- Polynomial approximation followed by inversion preserves the values,
first derivatives and logarithmic ratios of a positive C¹ function. -/
theorem exists_reciprocal_polynomial_ratio_approximation {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x)
    (hc' : ContinuousOn f' interval) (hpos : ∀ x ∈ interval, 0 < f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], (∀ x ∈ interval, 0 < p.eval x) ∧
      ∀ x ∈ interval,
        |logarithmicOperator (fun y => (p.eval y)⁻¹) x / (p.eval x)⁻¹ -
          logarithmicOperator (fun y => (f y)⁻¹) x / (f x)⁻¹| < ε := by
  have hc : ContinuousOn f interval := fun x hx => (hf x hx).continuousWithinAt
  have hI : interval.Nonempty := nonempty_Icc.mpr (by norm_num)
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn hI hc
  obtain ⟨w, hw, hmax⟩ := isCompact_Icc.exists_isMaxOn hI hc
  obtain ⟨u, hu, hdermax⟩ := isCompact_Icc.exists_isMaxOn hI hc'.abs
  let m := f z/2
  let F := max (f w) 1
  let K := |f' u|
  have hm : 0 < m := by dsimp [m]; positivity [hpos z hz]
  have hF : 0 ≤ F := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  have hK : 0 ≤ K := abs_nonneg _
  have hfmin : ∀ x ∈ interval, 2*m ≤ f x := by
    intro x hx
    have hh : f z ≤ f x := hmin hx
    dsimp [m]
    linarith
  have hfF : ∀ x ∈ interval, f x ≤ F := fun x hx => (hmax hx).trans (le_max_left _ _)
  have hfK : ∀ x ∈ interval, |f' x| ≤ K := fun x hx => hdermax hx
  let μ := 1/(F+1)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  let D₀ := 1/m^2
  let D₁ := 1/m^2 + K*(2*F+1)/m^4
  let K₀ := K/m^2
  let D₂ := 2*D₁/μ + 2*K₀*D₀/(μ*μ)
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hD₂ : 0 ≤ D₂ := by dsimp [D₂]; positivity
  let δ := min (m/2) (min 1 (ε/(D₂+1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδm : δ ≤ m/2 := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδD : δ ≤ ε/(D₂+1) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : D₂*δ < ε := by
    have hh := (le_div_iff₀ (show 0 < D₂+1 by positivity)).mp hδD
    nlinarith
  obtain ⟨p, _, hp⟩ := exists_polynomial_C1_approximation hf hc' hδ
  have hpmin : ∀ x ∈ interval, m ≤ p.eval x := by
    intro x hx
    have hh := (abs_lt.mp (hp x hx).1).1
    linarith [hfmin x hx]
  have hfmin' : ∀ x ∈ interval, m ≤ f x := by
    intro x hx
    linarith [hfmin x hx]
  have hpF : ∀ x ∈ interval, p.eval x ≤ F+1 := by
    intro x hx
    have hh := (abs_lt.mp (hp x hx).1).2
    linarith [hfF x hx]
  have hpK : ∀ x ∈ interval, |p.derivative.eval x| ≤ K+δ := by
    intro x hx
    have hh := abs_add_le (p.derivative.eval x-f' x) (f' x)
    rw [sub_add_cancel] at hh
    linarith [(hp x hx).2, hfK x hx]
  have hvalue : ∀ x ∈ interval, |(p.eval x)⁻¹-(f x)⁻¹| ≤ D₀*δ := by
    intro x hx
    have hh := reciprocal_value_error hm (hpmin x hx) (hfmin' x hx) (hp x hx).1.le
    convert hh using 1
    dsimp [D₀]
    ring
  have hderror : ∀ x ∈ interval,
      |(-p.derivative.eval x/(p.eval x)^2)-(-f' x/(f x)^2)| ≤ D₁*δ := by
    intro x hx
    have hh := reciprocal_derivative_error hm hF hK hδ.le (hpmin x hx) (hfmin' x hx)
      (hpF x hx) (hfF x hx) (hfK x hx) (hp x hx).1.le (hp x hx).2.le
    convert hh using 1
    dsimp [D₁]
    ring
  have hpder : ∀ x ∈ interval, HasDerivWithinAt (fun y => (p.eval y)⁻¹)
      (-p.derivative.eval x/(p.eval x)^2) interval x :=
    fun x hx => (p.hasDerivWithinAt x interval).inv (hm.trans_le (hpmin x hx)).ne'
  have hfder : ∀ x ∈ interval, HasDerivWithinAt (fun y => (f y)⁻¹)
      (-f' x/(f x)^2) interval x := fun x hx => (hf x hx).inv (hpos x hx).ne'
  have hbf : ∀ x ∈ interval, |-f' x/(f x)^2| ≤ K₀ := by
    intro x hx
    rw [abs_div, abs_neg, abs_of_pos (sq_pos_of_pos (hpos x hx))]
    exact div_le_div₀ hK (hfK x hx) (sq_pos_of_pos hm) (pow_le_pow_left₀ hm.le (hfmin' x hx) 2)
  have hbp : ∀ x ∈ interval, |-p.derivative.eval x/(p.eval x)^2| ≤ (K+δ)/m^2 := by
    intro x hx
    rw [abs_div, abs_neg, abs_of_pos (sq_pos_of_pos (hm.trans_le (hpmin x hx)))]
    exact div_le_div₀ (by positivity) (hpK x hx) (sq_pos_of_pos hm)
      (pow_le_pow_left₀ hm.le (hpmin x hx) 2)
  have hlowp : ∀ x ∈ interval, μ ≤ (p.eval x)⁻¹ := by
    intro x hx
    simpa only [μ, one_div] using
      one_div_le_one_div_of_le (hm.trans_le (hpmin x hx)) (hpF x hx)
  have hlowf : ∀ x ∈ interval, μ ≤ (f x)⁻¹ := by
    intro x hx
    simpa only [μ, one_div] using
      one_div_le_one_div_of_le (hpos x hx) ((hfF x hx).trans (show F ≤ F+1 by linarith))
  refine ⟨p, fun x hx => hm.trans_le (hpmin x hx), ?_⟩
  intro x hx
  have hh := logarithmicRatio_sub_bound (by positivity : 0 ≤ (K+δ)/m^2) hK₀
    (mul_nonneg hD₁ hδ.le) (mul_nonneg hD₀ hδ.le) hμ hpder hfder hbp hbf
    hderror hvalue hlowp hlowf hx
  have he : 2*(D₁*δ)/μ + 2*K₀*(D₀*δ)/(μ*μ) = D₂*δ := by dsimp [D₂]; ring
  rw [he] at hh
  exact hh.trans_lt hsmall

end Erdos1132.Counterexample
