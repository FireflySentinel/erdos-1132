import Erdos1132.Additive.ComplexPotentialEstimate
import Erdos1132.Additive.PotentialScales
import Erdos1132.Additive.PotentialDrop

/-! # Local potential estimates under a linear Lebesgue bound

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace Erdos1132

/-- A point in the inset interval remains in the original interpolation interval. -/
theorem mem_interval_of_inset {a b d x : ℝ} (hd : 0 ≤ d) (hx : x ∈ Icc (a+d) (b-d)) :
    x ∈ Icc a b := by constructor <;> linarith [hx.1, hx.2]

/-- A direct proof of [Tao, Theorem 4.1(ii)] in the form needed here, with
his hypothesis (4.1) specialized to `λ ≤ n` on the fixed interval.
The normalization and exterior density are defined from the node array. -/
theorem uniform_complex_potential_expansion {a b d : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      ∀ x ∈ Icc (a+d) (b-d), ∀ h : ℝ, 1/(n : ℝ) ≤ h →
        |X.complexLogPotential x h-X.potentialNormalization +
          Real.pi*h*X.exteriorDensity a b X.potentialNormalization x 0| ≤
          C*(potentialErrorSize n+h^3) := by
  let A := normalizationBound a b
  let C₀ := 5+Real.log 2+(Real.sqrt (2*logSquareBound)+2*A)/Real.pi
  let C₃ := exteriorKernelBound d*(weightedLogBound+A)/(Real.pi*d^2)
  have hA : 0 < A := normalizationBound_pos hab
  have hC₀ : 0 < C₀ := by
    have hB := logSquareBound_nonneg
    dsimp [C₀]
    positivity
  have hC₃ : 0 < C₃ := by
    dsimp [C₃]
    exact div_pos (mul_pos (exteriorKernelBound_pos hd)
      (add_pos_of_nonneg_of_pos weightedLogBound_nonneg hA)) (by positivity)
  refine ⟨C₀+C₃+1, by positivity, ?_⟩
  intro n X hn hΛ x hx h hh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh0 : 0 < h := (one_div_pos.mpr hnR).trans_le hh
  have hxI := hI (mem_interval_of_inset hd.le hx)
  have hx1 : |x| ≤ 1 := abs_le.mpr hxI
  have hα := X.abs_potentialNormalization_le hn hab hI hΛ
  change |X.potentialNormalization| ≤ A at hα
  let δ : ℝ := 1/(n : ℝ)^5
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ)^5)).mpr
    exact one_le_pow₀ hn1
  have he := X.complex_potential_expansion hn hd hx hx1 hI hh0 hδ hδ1 hΛ hn1
  have hlog := local_log_error_scale hn1
  have hsmall := small_set_error_scale hn1 (abs_nonneg X.potentialNormalization) logSquareBound_nonneg hh
  have hsmall' : (Real.sqrt (2*n*δ*logSquareBound)+|X.potentialNormalization| *(2*n*δ))/(Real.pi*h) ≤
      ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)*potentialErrorSize n := by
    have hAmono : ((Real.sqrt (2*logSquareBound)+2*|X.potentialNormalization|)/Real.pi)/(n : ℝ) ≤
        ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)/(n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      linarith
    have hmult := mul_le_mul_of_nonneg_left (by linarith [Real.log_nonneg hn1] : (1 : ℝ) ≤ 1+Real.log n)
      (by positivity : 0 ≤ (Real.sqrt (2*logSquareBound)+2*A)/Real.pi)
    have hfinal := div_le_div_of_nonneg_right hmult hnR.le
    calc
      _ ≤ ((Real.sqrt (2*logSquareBound)+2*|X.potentialNormalization|)/Real.pi)/(n : ℝ) := hsmall
      _ ≤ ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)/(n : ℝ) := hAmono
      _ ≤ _ := by simpa only [mul_one, potentialErrorSize, mul_div_assoc] using hfinal
  have hcubic : (exteriorKernelBound d*(weightedLogBound+|X.potentialNormalization|)/(Real.pi*d^2))*h^3 ≤ C₃*h^3 := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh0.le _)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith : weightedLogBound+|X.potentialNormalization| ≤ weightedLogBound+A)
      (exteriorKernelBound_pos hd).le
  have hsum := add_le_add (add_le_add hlog hsmall') hcubic
  have hE := potentialErrorSize_nonneg hn
  calc
    _ ≤ (5+Real.log 2)*potentialErrorSize n +
        ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)*potentialErrorSize n+C₃*h^3 := he.trans hsum
    _ = C₀*potentialErrorSize n+C₃*h^3 := by dsimp [C₀]; ring
    _ ≤ (C₀+C₃+1)*(potentialErrorSize n+h^3) := by
      nlinarith [mul_nonneg hC₀.le (pow_nonneg hh0.le 3), mul_nonneg hC₃.le hE]

/-- The actual exterior density has uniform size and Lipschitz bounds. -/
theorem uniform_exterior_density_bounds {a b d : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      (∀ x ∈ Icc (a+d) (b-d), |X.exteriorDensity a b X.potentialNormalization x 0| ≤ C) ∧
      (∀ x ∈ Icc (a+d) (b-d), ∀ z ∈ Icc (a+d) (b-d),
        |X.exteriorDensity a b X.potentialNormalization x 0-
          X.exteriorDensity a b X.potentialNormalization z 0| ≤ C*|x-z|) := by
  let A := normalizationBound a b
  let B := (exteriorKernelBound d/Real.pi^2)*(weightedLogBound+A)
  let L := 2*B/d
  have hA := (normalizationBound_pos hab).le
  have hB : 0 ≤ B := mul_nonneg (div_nonneg (exteriorKernelBound_pos hd).le (sq_nonneg _))
    (add_nonneg weightedLogBound_nonneg hA)
  have hL : 0 ≤ L := div_nonneg (mul_nonneg (by norm_num) hB) hd.le
  refine ⟨B+L+1, by positivity, ?_⟩
  intro n X hn hΛ
  have hα := X.abs_potentialNormalization_le hn hab hI hΛ
  change |X.potentialNormalization| ≤ A at hα
  have hx1 (x : ℝ) (hx : x ∈ Icc (a+d) (b-d)) : |x| ≤ 1 :=
    abs_le.mpr (hI (mem_interval_of_inset hd.le hx))
  constructor
  · intro x hx
    have hb := (X.exterior_density_integrable_and_bound hn hd hx (hx1 x hx) X.potentialNormalization 0).2
    have hm := mul_le_mul_of_nonneg_left (by linarith : weightedLogBound+|X.potentialNormalization| ≤ weightedLogBound+A)
      (div_nonneg (exteriorKernelBound_pos hd).le (sq_nonneg Real.pi))
    exact (hb.trans hm).trans (by dsimp [B] at *; linarith)
  · intro x hx z hz
    have hb := X.exteriorDensity_lipschitz_bound hn hd hx hz (hx1 x hx) (hx1 z hz) X.potentialNormalization
    have hc : 2*exteriorKernelBound d/Real.pi^2*(weightedLogBound+|X.potentialNormalization|)/d ≤ L := by
      have hD := exteriorKernelBound_pos hd
      have hm := mul_le_mul_of_nonneg_left (by linarith : weightedLogBound+|X.potentialNormalization| ≤ weightedLogBound+A)
        (by positivity : 0 ≤ 2*exteriorKernelBound d/Real.pi^2/d)
      convert! hm using 1 <;> ring
    exact hb.trans ((mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith : L ≤ B+L+1) (abs_nonneg _)))

end Erdos1132
