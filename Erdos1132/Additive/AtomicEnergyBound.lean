import Erdos1132.Additive.AtomicRieszEnergy

/-! # Quantitative lower bound for atomic Riesz energy

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Real Finset
open scoped BigOperators
namespace Erdos1132

theorem atomic_riesz_lower_bound {n : ℕ} (hn : 0 < n) (x a : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) {A M C E : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (ha0 : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (hfM : ∀ t, f t ≤ M) (hsupp : ∀ t, t ∉ Icc (-1:ℝ) 1 → f t = 0)
    (hconv : ∀ t, |rieszConvolution (1/(n:ℝ)) f t-2*Real.log n*f t| ≤ C)
    (hquad : |(∑ i, a i*f (x i))/(n:ℝ)-(∫ t, (f t)^2)| ≤ E) :
    2*Real.log n*(∫ t, (f t)^2)-4*Real.log n*E-2*C*A-C*(∫ t, f t) ≤
      (∑ i, ∑ j, a i*a j*rieszKernel (1/(n:ℝ)) (x i-x j))/(n:ℝ)^2 := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hε : 0 < 1/(n:ℝ) := by positivity
  let w (i : Fin n) := a i/(n:ℝ)
  have hw0 (i : Fin n) : 0 ≤ w i := div_nonneg (ha0 i) hnR.le
  have hwA (i : Fin n) : w i ≤ A := by
    apply (div_le_iff₀ hnR).mpr
    exact (haA i).trans (by nlinarith)
  have hwtotal : (∑ i, w i) ≤ A := by
    dsimp only [w]
    rw [← sum_div]
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ ∑ _i : Fin n, A := sum_le_sum (fun i _ => haA i)
      _ = _ := by simp; ring
  have hwquad : (∫ t, (f t)^2)-E ≤ ∑ i, w i*f (x i) := by
    have hq := (abs_le.mp hquad).1
    have he : (∑ i, w i*f (x i)) = (∑ i, a i*f (x i))/(n:ℝ) := by
      rw [sum_div]; apply sum_congr rfl; intro i hi; dsimp [w]; ring
    rw [he]
    linarith
  have hmixed : 2*Real.log n*((∫ t, (f t)^2)-E)-C*A ≤
      ∑ i, w i*rieszConvolution (1/(n:ℝ)) f (x i) := by
    have hl (i : Fin n) := mul_le_mul_of_nonneg_left
      (show 2*Real.log n*f (x i)-C ≤ rieszConvolution (1/(n:ℝ)) f (x i) by
        have hh := (abs_le.mp (hconv (x i))).1; linarith) (hw0 i)
    have hs := sum_le_sum (s := univ) (fun i _ => hl i)
    have he : (∑ i, w i*(2*Real.log n*f (x i)-C)) =
        2*Real.log n*(∑ i, w i*f (x i))-C*(∑ i, w i) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl; intro i hi; ring
    rw [he] at hs
    have hq := mul_le_mul_of_nonneg_left hwquad (by positivity : 0 ≤ 2*Real.log (n:ℝ))
    have hm := mul_le_mul_of_nonneg_left hwtotal hC
    linarith
  have hfsq : Integrable (fun t => (f t)^2) := by
    simpa only [pow_two] using hf.mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]; exact hfM t))
  have hself : (∫ t, f t*rieszConvolution (1/(n:ℝ)) f t) ≤
      2*Real.log n*(∫ t, (f t)^2)+C*(∫ t, f t) := by
    calc
      _ ≤ ∫ t, (2*Real.log n)*(f t)^2+C*f t := integral_mono
        (integrable_riesz_self_energy hε hf hfm) ((hfsq.const_mul _).add (hf.const_mul _)) (fun t => by
          have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hconv t)).2 (hf0 t)
          nlinarith)
      _ = _ := by rw [integral_add (hfsq.const_mul _) (hf.const_mul _), integral_const_mul, integral_const_mul]
  have hp := atomic_riesz_energy_comparison x w hx hε (by positivity : 0 ≤ A+M)
    (fun i => by rw [abs_of_nonneg (hw0 i)]; exact (hwA i).trans (by linarith))
    hfm (fun t => by rw [abs_of_nonneg (hf0 t)]; exact (hfM t).trans (by linarith)) hsupp
  change 2*(∑ i, w i*rieszConvolution (1/(n:ℝ)) f (x i))-
    (∫ t, f t*rieszConvolution (1/(n:ℝ)) f t) ≤ _ at hp
  have he : (∑ i, ∑ j, w i*w j*rieszKernel (1/(n:ℝ)) (x i-x j)) =
      (∑ i, ∑ j, a i*a j*rieszKernel (1/(n:ℝ)) (x i-x j))/(n:ℝ)^2 := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    rw [sum_div]
    apply sum_congr rfl
    intro j hj
    dsimp only [w]
    ring
  rw [he] at hp
  nlinarith

theorem regularized_energy_le_reciprocal_add_diag {n : ℕ} (x a : Fin n → ℝ)
    (hx : Function.Injective x) (ha : ∀ i, 0 ≤ a i) {ε : ℝ} (hε : 0 < ε) :
    (∑ i, ∑ j, a i*a j*rieszKernel ε (x i-x j)) ≤
      (∑ i, ∑ j, a i*a j/|x i-x j|)+(∑ i, (a i)^2/ε) := by
  classical
  have hp (i j : Fin n) : a i*a j*rieszKernel ε (x i-x j) ≤
      a i*a j/|x i-x j|+if i = j then (a i)^2/ε else 0 := by
    by_cases hij : i = j
    · subst j
      simp [rieszKernel_diagonal hε.le, pow_two, div_eq_mul_inv]
    · have hd : x i-x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hx h))
      rw [if_neg hij, add_zero]
      simpa only [div_eq_mul_inv, one_div, mul_assoc, one_mul] using
        mul_le_mul_of_nonneg_left (rieszKernel_le_inverse_distance (ε := ε) hd) (mul_nonneg (ha i) (ha j))
  have hh := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun j _ => hp i j))
  simpa only [sum_add_distrib, sum_ite_eq, Finset.mem_univ, if_true] using hh

end Erdos1132
