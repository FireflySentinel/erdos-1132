import Erdos1132.Counterexample.CoordinateBounds
import Erdos1132.Counterexample.AmplitudeInterpolation

/-!
# Amplitude nodes at the inverse images of phase midpoints

These rows use the same globally bounded phase as the quadrature estimates.
Their Lebesgue function is the exact inverse-coordinate sum in (7.28).
-/

noncomputable section

open Set Polynomial Finset
open scoped Topology ContDiff BigOperators

namespace Erdos1132.Counterexample

def phaseMidpoint (n : ℕ) (i : Fin n) : ℝ := ((i : ℝ) + 1/2)*(Real.pi/n)

theorem phaseMidpoint_mem_Ioo {n : ℕ} (i : Fin n) :
    phaseMidpoint n i ∈ Set.Ioo 0 Real.pi := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  constructor
  · dsimp [phaseMidpoint]; positivity
  · unfold phaseMidpoint
    rw [← mul_div_assoc, div_lt_iff₀ hnR]
    nlinarith [Real.pi_pos]

theorem phaseMidpoint_injective (n : ℕ) : Function.Injective (phaseMidpoint n) := by
  intro i j hij
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hp : Real.pi / n ≠ 0 := div_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hn.ne')
  have he : (i : ℝ) = j := by
    have := mul_right_cancel₀ hp hij
    linarith
  exact Fin.ext (by exact_mod_cast he)

theorem phaseInverse_scaled_identity {ψ : ℝ → ℝ} {B : ℝ} {n : ℕ}
    (hψ : Continuous ψ) (hval : ∀ t, |ψ t| ≤ B) (hn : 0 < n) (s : ℝ) :
    n * phaseInverse ψ (n : ℝ)⁻¹ s - ψ (phaseInverse ψ (n : ℝ)⁻¹ s) = n*s := by
  have he := phaseInverse_right (ε := (n : ℝ)⁻¹) hψ hval s
  dsimp only [phaseMap] at he
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn0] at he
  simpa only [one_div] using he

/-- A fixed admissible phase determines an actual interior node row and its
exact coordinate formula for the Lagrange Lebesgue function. -/
theorem exists_phaseCoordinate_row (h : ℝ[X]) {ψ v : ℝ → ℝ} {B : ℝ} {n : ℕ}
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) (hn : h.natDegree < n)
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |(n : ℝ)⁻¹| * B < 1)
    (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0)
    (hid : ∀ t, (amplitudePolynomial h n).eval (Real.cos t) =
      ‖(complexPolynomial h).eval (circlePoint t)‖ * Real.cos (n*t - ψ t))
    (hv : ∀ t, v (Real.cos t) = ‖(complexPolynomial h).eval (circlePoint t)‖⁻¹) :
    ∃ Y : Nodes n,
      (∀ i, Y.point i = phaseCoordinate ψ ((n : ℝ)⁻¹, phaseMidpoint n i) ∧
        Y.point i ∈ Set.Ioo (-1) 1) ∧
      (∀ i, (amplitudePolynomial h n).eval (Y.point i) = 0 ∧
        (amplitudePolynomial h n).derivative.eval (Y.point i) ≠ 0) ∧
      ∀ s : ℝ, (∀ i, phaseCoordinate ψ ((n : ℝ)⁻¹, s) ≠ Y.point i) →
        let X := fun t => phaseCoordinate ψ ((n : ℝ)⁻¹, t)
        Y.lebesgue (X s) = |Real.cos (n*s)| / (n*v (X s)) *
          ∑ i : Fin n, v (X (phaseMidpoint n i)) * |deriv X (phaseMidpoint n i)| /
            |X s - X (phaseMidpoint n i)| := by
  have hn0 : 0 < n := (Nat.zero_le h.natDegree).trans_lt hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  let X := fun t => phaseCoordinate ψ ((n : ℝ)⁻¹, t)
  let θ := fun t => phaseInverse ψ (n : ℝ)⁻¹ t
  let w := fun t => ‖(complexPolynomial h).eval (circlePoint t)‖
  have hwpos (t : ℝ) : 0 < w t := norm_pos_iff.mpr (hzero _ (by simp))
  have hθ (t : ℝ) (ht : t ∈ Set.Ioo 0 Real.pi) : θ t ∈ Set.Ioo 0 Real.pi := by
    have hm := phaseInverse_strictMono hψ hval hder hε
    constructor
    · simpa only [phaseInverse_endpoint hψ hder hε h0] using hm ht.1
    · simpa only [phaseInverse_endpoint hψ hder hε hπ] using hm ht.2
  have hp (t : ℝ) : 0 < (n : ℝ) - deriv ψ (θ t) := by
    have hh := (le_abs_self ((n : ℝ)⁻¹ * deriv ψ (θ t))).trans
      ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hder _) (abs_nonneg _)))
    have hq : 0 < 1 - (n : ℝ)⁻¹ * deriv ψ (θ t) := by linarith
    have hidq : 1 - (n : ℝ)⁻¹ * deriv ψ (θ t) =
        ((n : ℝ) - deriv ψ (θ t))/n := by field_simp
    rw [hidq] at hq
    exact (div_pos_iff_of_pos_right hnR).mp hq
  have hphase (t : ℝ) : (n : ℝ)*θ t - ψ (θ t) = n*t :=
    phaseInverse_scaled_identity hψ.continuous hval hn0 t
  have hmphase (i : Fin n) : (n : ℝ)*θ (phaseMidpoint n i) - ψ (θ (phaseMidpoint n i)) =
      ((i : ℝ) + 1/2)*Real.pi := by
    rw [hphase]
    dsimp [phaseMidpoint]
    field_simp
  have hc (i : Fin n) : Real.cos (n*θ (phaseMidpoint n i) - ψ (θ (phaseMidpoint n i))) = 0 := by
    rw [hmphase]
    rw [show ((i : ℝ) + 1/2)*Real.pi = Real.pi/2 + i.val*Real.pi by ring,
      Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero]
  have hroot (i : Fin n) : (amplitudePolynomial h n).eval (X (phaseMidpoint n i)) = 0 := by
    change (amplitudePolynomial h n).eval (Real.cos (θ (phaseMidpoint n i))) = 0
    rw [hid, hc, mul_zero]
  have hinj : Function.Injective (fun i : Fin n => X (phaseMidpoint n i)) := by
    intro i j hij
    have he := Real.strictAntiOn_cos.injOn
      (show θ (phaseMidpoint n i) ∈ Set.Icc 0 Real.pi from
        ⟨(hθ _ (phaseMidpoint_mem_Ioo i)).1.le, (hθ _ (phaseMidpoint_mem_Ioo i)).2.le⟩)
      (show θ (phaseMidpoint n j) ∈ Set.Icc 0 Real.pi from
        ⟨(hθ _ (phaseMidpoint_mem_Ioo j)).1.le, (hθ _ (phaseMidpoint_mem_Ioo j)).2.le⟩) hij
    exact phaseMidpoint_injective n ((phaseInverse_strictMono hψ hval hder hε).injective he)
  let Y : Nodes n := ⟨fun i => X (phaseMidpoint n i), hinj,
    fun i => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩⟩
  have hweight (i : Fin n) : |(amplitudePolynomial h n).derivative.eval (Y.point i)| =
      w (θ (phaseMidpoint n i))* (n - deriv ψ (θ (phaseMidpoint n i))) /
        Real.sin (θ (phaseMidpoint n i)) := by
    exact oscillatory_root_derivative
      ((((complexPolynomial h).hasDerivAt _).comp _
        (hasDerivAt_circlePoint _)).differentiableAt.norm ℝ (hzero _ (by simp)))
      ((hψ.differentiable (by simp)) _) hid (hc i) (hwpos _).le (hp _)
      (Real.sin_pos_of_mem_Ioo (hθ _ (phaseMidpoint_mem_Ioo i)))
  have hP : amplitudePolynomial h n ≠ 0 := by
    intro hz
    have hh := amplitudePolynomial_degree h hn hpos.ne'
    rw [hz, Polynomial.degree_zero] at hh
    exact WithBot.bot_ne_coe hh
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro i
    exact ⟨rfl, phaseCoordinate_mem_Ioo hψ hval hder hε h0 hπ (phaseMidpoint_mem_Ioo i)⟩
  · intro i
    refine ⟨hroot i, abs_pos.mp ?_⟩
    rw [hweight]
    exact div_pos (mul_pos (hwpos _) (hp _))
      (Real.sin_pos_of_mem_Ioo (hθ _ (phaseMidpoint_mem_Ioo i)))
  · intro s hs
    dsimp only
    rw [lebesgue_eq_polynomial_derivative_sum Y hP
      (amplitudePolynomial_natDegree h hn hpos.ne').le hroot hs]
    have hPs : (amplitudePolynomial h n).eval (X s) = w (θ s)*Real.cos (n*s) := by
      change (amplitudePolynomial h n).eval (Real.cos (θ s)) = _
      rw [hid, hphase]
    have hvs (t : ℝ) : v (X t) = (w (θ t))⁻¹ := hv (θ t)
    rw [hPs, abs_mul, abs_of_pos (hwpos _)]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [hweight, hvs, hvs]
    have hd : |deriv X (phaseMidpoint n i)| =
        Real.sin (θ (phaseMidpoint n i))*n/(n - deriv ψ (θ (phaseMidpoint n i))) := by
      rw [(phaseCoordinate_hasDerivAt hψ hval hder hε _).deriv]
      have hsin := Real.sin_pos_of_mem_Ioo (hθ _ (phaseMidpoint_mem_Ioo i))
      have hq : 0 < 1 - (n : ℝ)⁻¹ * deriv ψ (θ (phaseMidpoint n i)) := by
        have he : 1 - (n : ℝ)⁻¹ * deriv ψ (θ (phaseMidpoint n i)) =
            ((n : ℝ) - deriv ψ (θ (phaseMidpoint n i)))/n := by field_simp
        rw [he]
        exact div_pos (hp _) hnR
      rw [abs_div, abs_neg, abs_of_pos hsin, abs_of_pos hq]
      field_simp
    rw [hd]
    dsimp only [Y, X]
    field_simp [(hwpos (θ s)).ne', (hwpos (θ (phaseMidpoint n i))).ne',
      (Real.sin_pos_of_mem_Ioo (hθ _ (phaseMidpoint_mem_Ioo i))).ne', hnR.ne']

end Erdos1132.Counterexample
