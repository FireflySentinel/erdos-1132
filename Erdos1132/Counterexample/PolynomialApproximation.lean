import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
import Erdos1132.Counterexample.LogarithmicOperator

/-!
# Polynomial approximation in the C¹ norm

The approximation argument in Section 7.4: approximate the derivative by a
polynomial and take a polynomial primitive. Strict positivity is preserved on
the compact interval. The spectral factorization and amplitude estimate of
Lemma 9 are not asserted here.
-/

noncomputable section

open Set Polynomial

namespace Erdos1132.Counterexample

theorem exists_polynomial_primitive (p : ℝ[X]) :
    ∃ q : ℝ[X], q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by simp [hP, hQ]⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / ((n : ℝ) + 1)), ?_⟩
    simp [show (n : ℝ) + 1 ≠ 0 by positivity]

/-- C¹ polynomial approximation on `[-1,1]`, with independent pointwise
errors for the value and the derivative, and exact agreement at `-1`. -/
theorem exists_polynomial_C1_approximation {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (-1) 1) x)
    (hf' : ContinuousOn f' (Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], p.eval (-1) = f (-1) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1,
        |p.eval x - f x| < ε ∧ |p.derivative.eval x - f' x| < ε := by
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn
    (-1) 1 f' hf' (ε / 4) (by positivity)
  obtain ⟨Q, hQ⟩ := exists_polynomial_primitive q
  let p : ℝ[X] := C (f (-1) - Q.eval (-1)) + Q
  have hpder : p.derivative = q := by simp [p, hQ]
  have hpbase : p.eval (-1) = f (-1) := by simp [p]
  refine ⟨p, hpbase, ?_⟩
  intro x hx
  have hdiff : ∀ y ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun t => p.eval t - f t)
        (q.eval y - f' y) (Icc (-1) 1) y := by
    intro y hy
    convert! (p.hasDerivWithinAt y (Icc (-1) 1)).sub (hf y hy) using 1
    simp [hpder]
  have hbound : |p.eval x - f x| ≤ (ε / 4) * |x - (-1)| := by
    have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      hdiff (fun y hy => by simpa only [Real.norm_eq_abs] using (hq y hy).le)
      (left_mem_Icc.mpr (by norm_num)) hx
    simpa only [Real.norm_eq_abs, hpbase, sub_self, sub_zero] using h
  have hlength : |x - (-1 : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hlength (show 0 ≤ ε / 4 by positivity)
    linarith
  · rw [hpder]
    exact (hq x hx).trans (by linarith)

/-- Positive C¹ functions have strictly positive polynomial approximants,
with simultaneous control of the function and its derivative. -/
theorem exists_positive_polynomial_C1_approximation {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (-1) 1) x)
    (hf' : ContinuousOn f' (Icc (-1 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Icc (-1 : ℝ) 1,
      0 < p.eval x ∧ |p.eval x - f x| < ε ∧
        |p.derivative.eval x - f' x| < ε := by
  have hc : ContinuousOn f (Icc (-1 : ℝ) 1) :=
    fun x hx => (hf x hx).continuousWithinAt
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (show (-1 : ℝ) ≤ 1 by norm_num)) hc
  have hδ : 0 < min ε (f z / 2) := lt_min hε (by positivity [hpos z hz])
  obtain ⟨p, _, hp⟩ := exists_polynomial_C1_approximation hf hf' hδ
  refine ⟨p, ?_⟩
  intro x hx
  obtain ⟨hval, hder⟩ := hp x hx
  refine ⟨?_, hval.trans_le (min_le_left _ _), hder.trans_le (min_le_left _ _)⟩
  have hlow := (abs_lt.mp (hval.trans_le (min_le_right _ _))).1
  have hzmin : f z ≤ f x := hmin hx
  linarith [hpos z hz]

/-- A positive C¹ function can be approximated by a positive polynomial while
also approximating its logarithmic-operator quotient uniformly. This proves
the C¹ stability step in Section 7.4; it does not claim spectral factorization. -/
theorem exists_positive_polynomial_C1_ratio_approximation {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ interval, HasDerivWithinAt f (f' x) interval x)
    (hf' : ContinuousOn f' interval)
    (hpos : ∀ x ∈ interval, 0 < f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ interval,
      0 < p.eval x ∧ |p.eval x - f x| < ε ∧
        |p.derivative.eval x - f' x| < ε ∧
        |logarithmicOperator (fun t => p.eval t) x / p.eval x -
          logarithmicOperator f x / f x| < ε := by
  have hc : ContinuousOn f interval := fun x hx => (hf x hx).continuousWithinAt
  have hI : interval.Nonempty := nonempty_Icc.mpr (by norm_num)
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn hI hc
  obtain ⟨w, hw, hmax⟩ := isCompact_Icc.exists_isMaxOn hI hf'.abs
  let m := f z / 2
  let K := |f' w|
  have hm : 0 < m := by dsimp [m]; positivity [hpos z hz]
  have hK : 0 ≤ K := abs_nonneg _
  have hbf : ∀ x ∈ interval, |f' x| ≤ K := fun x hx => hmax hx
  have hminf : ∀ x ∈ interval, 2 * m ≤ f x := by
    intro x hx
    have hzmin : f z ≤ f x := hmin hx
    dsimp [m]
    linarith
  let D := 2 / m + 2 * K / (m * m)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let δ := min (ε / 2) (min (m / 2) (ε / (2 * (D + 1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδm : δ ≤ m / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδD : δ ≤ ε / (2 * (D + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : D * δ < ε := by
    have hmul := (le_div_iff₀ (show 0 < 2 * (D + 1) by positivity)).mp hδD
    nlinarith
  obtain ⟨p, _, hp⟩ := exists_polynomial_C1_approximation hf hf' hδ
  have hpder : ∀ x ∈ interval,
      HasDerivWithinAt (fun t => p.eval t) (p.derivative.eval x) interval x := by
    intro x _
    exact p.hasDerivWithinAt x interval
  have hbp : ∀ x ∈ interval, |p.derivative.eval x| ≤ K + δ := by
    intro x hx
    have h := abs_add_le (p.derivative.eval x - f' x) (f' x)
    rw [sub_add_cancel] at h
    linarith [(hp x hx).2, hbf x hx]
  have hpf : ∀ x ∈ interval, m ≤ p.eval x := by
    intro x hx
    have h := (abs_lt.mp (hp x hx).1).1
    linarith [hminf x hx]
  have hff : ∀ x ∈ interval, m ≤ f x := by
    intro x hx
    linarith [hminf x hx]
  refine ⟨p, ?_⟩
  intro x hx
  refine ⟨hm.trans_le (hpf x hx),
    (hp x hx).1.trans (by linarith), (hp x hx).2.trans (by linarith), ?_⟩
  have hratio := logarithmicRatio_sub_bound (by positivity : 0 ≤ K + δ) hK
    hδ.le hδ.le hm hpder hf hbp hbf
    (fun y hy => (hp y hy).2.le) (fun y hy => (hp y hy).1.le) hpf hff hx
  have heq : 2 * δ / m + 2 * K * δ / (m * m) = D * δ := by dsimp [D]; ring
  rw [heq] at hratio
  exact hratio.trans_lt hsmall

end Erdos1132.Counterexample
