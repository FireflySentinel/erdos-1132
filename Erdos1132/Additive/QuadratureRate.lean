import Erdos1132.Additive.LocalQuadrature
import Mathlib.Analysis.Real.Sqrt

/-! # A uniform algebraic rate for the local quadrature estimate

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace Erdos1132

/-- A fourth root records the two nested square-root scales without rounding. -/
def quarterRoot (N : ℝ) : ℝ := Real.sqrt (Real.sqrt N)

theorem quarterRoot_pos {N : ℝ} (hN : 0 < N) : 0 < quarterRoot N := by
  unfold quarterRoot
  positivity

theorem quarterRoot_pow_four {N : ℝ} (hN : 0 ≤ N) : (quarterRoot N)^4 = N := by
  unfold quarterRoot
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg N)
  have h2 := Real.sq_sqrt hN
  nlinarith

theorem one_le_quarterRoot {N : ℝ} (hN : 1 ≤ N) : 1 ≤ quarterRoot N := by
  have h0 : 0 ≤ N := zero_le_one.trans hN
  have hq := quarterRoot_pos (zero_lt_one.trans_le hN)
  have he := quarterRoot_pow_four h0
  by_contra he'
  have hlt : quarterRoot N < 1 := lt_of_not_ge he'
  have h1 : (quarterRoot N)^2 < 1 := by nlinarith
  nlinarith [sq_nonneg ((quarterRoot N)^2)]

theorem tendsto_quarterRoot : Tendsto quarterRoot atTop atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop

theorem tendsto_inv_quarterRoot_nat :
    Tendsto (fun n : ℕ => 1/quarterRoot n) atTop (𝓝 0) :=
  (tendsto_quarterRoot.comp tendsto_natCast_atTop_atTop).const_div_atTop 1

theorem log_div_quarterRoot_le {N : ℝ} (hN : 0 < N) : Real.log N/quarterRoot N ≤ 4 := by
  have hq := quarterRoot_pos hN
  have he := quarterRoot_pow_four hN.le
  have hl := Real.log_le_sub_one_of_pos hq
  apply (div_le_iff₀ hq).mpr
  calc
    Real.log N = Real.log ((quarterRoot N)^4) := congrArg Real.log he.symm
    _ = 4*Real.log (quarterRoot N) := by rw [Real.log_pow]; norm_num
    _ ≤ 4*quarterRoot N := by linarith

theorem quadrature_scale_rate {N C M L : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    L*(1/quarterRoot N)+8*M*(1/(quarterRoot N)^2)/(Real.pi*(1/quarterRoot N)) +
      C*M*(((1+Real.log N)/N)/(1/(quarterRoot N)^2)+(1/(quarterRoot N)^2)^2) ≤
      (L+8*M/Real.pi+5*C*M)/quarterRoot N := by
  let q := quarterRoot N
  have hq : 0 < q := quarterRoot_pos (zero_lt_one.trans_le hN)
  have hq1 : 1 ≤ q := one_le_quarterRoot hN
  have he : q^4 = N := quarterRoot_pow_four (zero_le_one.trans hN)
  have hlog : 1+Real.log N ≤ 4*q := by
    rw [← he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hl := Real.log_le_sub_one_of_pos hq
    linarith
  have hterm : ((1+Real.log N)/N)/(1/q^2) ≤ 4/q := by
    rw [← he]
    have heq : ((1+Real.log (q^4))/q^4)/(1/q^2) = (1+Real.log (q^4))/q^2 := by field_simp
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    have heq2 : 4/q*q^2 = 4*q := by field_simp
    rw [heq2]
    simpa only [he] using hlog
  have hpow : (1/q^2)^2 ≤ 1/q := by
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le hq
    nlinarith [sq_nonneg (q^2-1)]
  have hsum : ((1+Real.log N)/N)/(1/q^2)+(1/q^2)^2 ≤ 5/q := by
    have hh := add_le_add hterm hpow
    convert! hh using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC hM)
  have heq : 8*M*(1/q^2)/(Real.pi*(1/q)) = (8*M/Real.pi)/q := by field_simp
  change L*(1/q)+8*M*(1/q^2)/(Real.pi*(1/q))+_ ≤ _
  rw [heq]
  calc
    _ ≤ L*(1/q)+(8*M/Real.pi)/q+C*M*(5/q) := by linarith
    _ = _ := by ring

theorem uniform_local_quadrature_rate {a b d l r M L : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) (hlr : l ≤ r)
    (hJ : Icc l r ⊆ Icc (a+d) (b-d)) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, |f x| ≤ M) →
      (∀ x y, |f x-f y| ≤ L*|x-y|) → (∀ x, x ∉ Icc l r → f x = 0) →
      |(∑ i, f (X.point i))/(n : ℝ)-
        ∫ x, X.exteriorDensity a b X.potentialNormalization x 0*f x| ≤ C/quarterRoot n := by
  obtain ⟨C, hC, hquad⟩ := uniform_local_quadrature hab hI hd hlr hJ
  refine ⟨L+8*M/Real.pi+5*C*M+1, by positivity, ?_⟩
  intro n X hn hΛ f hf hMf hlip hsupp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < quarterRoot n := quarterRoot_pos hnR
  have hq1 := one_le_quarterRoot hn1
  have hscale : 1/(n : ℝ) ≤ 1/(quarterRoot n)^2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq)
    calc
      (quarterRoot n)^2 ≤ (quarterRoot n)^4 := by nlinarith [sq_nonneg ((quarterRoot n)^2-1)]
      _ = _ := quarterRoot_pow_four hnR.le
  have he := hquad n X hn hΛ f M L (1/(quarterRoot n)^2) (1/quarterRoot n)
    hf hMf hL hlip hsupp (by positivity) hscale
  have hb := quadrature_scale_rate (L := L) hn1 hC.le hM
  exact (he.trans hb).trans (div_le_div_of_nonneg_right (by linarith) hq.le)

end Erdos1132
