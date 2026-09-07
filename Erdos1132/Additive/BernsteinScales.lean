import Erdos1132.Additive.QuadratureRate
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Explicit scales for the local interpolation estimates

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace Erdos1132

def eighthRoot (N : ℝ) : ℝ := Real.sqrt (quarterRoot N)

theorem eighthRoot_nonneg (N : ℝ) : 0 ≤ eighthRoot N := Real.sqrt_nonneg _

theorem eighthRoot_pos {N : ℝ} (hN : 0 < N) : 0 < eighthRoot N :=
  Real.sqrt_pos.mpr (quarterRoot_pos hN)

theorem eighthRoot_pow_eight {N : ℝ} (hN : 0 ≤ N) : eighthRoot N^8 = N := by
  have h := Real.sq_sqrt (Real.sqrt_nonneg (Real.sqrt N))
  have he := quarterRoot_pow_four hN
  calc
    eighthRoot N^8 = (eighthRoot N^2)^4 := by ring
    _ = quarterRoot N^4 := by rw [show eighthRoot N^2 = quarterRoot N from h]
    _ = N := he

theorem eighthRoot_ge_one {N : ℝ} (hN : 1 ≤ N) : 1 ≤ eighthRoot N := by
  simpa only [eighthRoot, Real.sqrt_one] using Real.sqrt_le_sqrt (one_le_quarterRoot hN)

theorem tendsto_eighthRoot : Tendsto (fun n : ℕ => eighthRoot n) atTop atTop :=
  (Real.tendsto_sqrt_atTop.comp tendsto_quarterRoot).comp tendsto_natCast_atTop_atTop

theorem top_edge_scale_inequality {t C D : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlarge : D+10*C+4 ≤ t) :
    Real.pi*t^8*(1/t^4)*D*(1/t^2)+C*(1+Real.log (t^8)+t^8*(1/t^4)^3)-
      Real.log (1/t^4) ≤ Real.pi*t^8*(1/t^4)*(1/t) := by
  have ht0 : 0 < t := by linarith
  have he1 : Real.pi*t^8*(1/t^4)*D*(1/t^2) = Real.pi*D*t^2 := by field_simp
  have he2 : t^8*(1/t^4)^3 = 1/t^4 := by field_simp
  have he3 : Real.pi*t^8*(1/t^4)*(1/t) = Real.pi*t^3 := by field_simp
  rw [he1, he2, he3, Real.log_pow, one_div, Real.log_inv, Real.log_pow]
  have hlog : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hinv : 1/t^4 ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ ht)
  have ht2 : t ≤ t^2 := by nlinarith
  have hA : π*D*t^2+C*(1+8*Real.log t+1/t^4)+4*Real.log t ≤
      (π*D+10*C+4)*t^2 := by
    have hc1 := mul_le_mul_of_nonneg_left hinv hC
    have hc2 := mul_le_mul_of_nonneg_left hlog hC
    have hc3 := mul_le_mul_of_nonneg_left ht2 hC
    have hc4 := mul_le_mul_of_nonneg_left (show 1 ≤ t^2 by nlinarith) hC
    nlinarith
  have hB : π*D+10*C+4 ≤ π*t := by
    have hp : 1 ≤ π := by linarith [Real.pi_gt_three]
    have hm := mul_le_mul_of_nonneg_left hlarge Real.pi_pos.le
    have hc := mul_le_mul_of_nonneg_left hp (show 0 ≤ 10*C+4 by positivity)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hB (sq_nonneg t)
  norm_num at *
  nlinarith

/-- For the scales `L = n⁻¹ᐟ⁴`, `H = n⁻¹ᐟ²`, `ε = n⁻¹ᐟ⁸`, the
upper-edge surplus eventually absorbs the potential error and density variation. -/
theorem eventually_top_edge_scales {C D d : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hd : 0 < d) :
    ∀ᶠ (n : ℕ) in atTop, let t := eighthRoot n;
      0 < n ∧ 0 < t ∧ 1/t^2 ≤ d ∧ 0 < 1/t^4 ∧ 1/t^4 ≤ 1 ∧
      1/(n : ℝ) ≤ 1/t^4 ∧
      π*n*(1/t^4)*D*(1/t^2)+C*(1+Real.log n+n*(1/t^4)^3)-Real.log (1/t^4) ≤
        π*n*(1/t^4)*(1/t) := by
  have ht1 := tendsto_eighthRoot.eventually (eventually_ge_atTop (1 : ℝ))
  have hlarge := tendsto_eighthRoot.eventually (eventually_ge_atTop (D+10*C+4))
  have htd := tendsto_eighthRoot.eventually (eventually_ge_atTop (1/d+1))
  filter_upwards [eventually_ge_atTop 1, ht1, hlarge, htd] with n hn ht hlarge htd
  dsimp only
  let t := eighthRoot (n : ℝ)
  have hn0 : 0 < n := by omega
  have ht0 : 0 < t := eighthRoot_pos (by exact_mod_cast hn0)
  have he : t^8 = (n : ℝ) := eighthRoot_pow_eight (Nat.cast_nonneg n)
  have htd' : 1/t^2 ≤ d := by
    apply (div_le_iff₀ (pow_pos ht0 _)).mpr
    have hh : 1 ≤ d*t := by
      have hh := mul_le_mul_of_nonneg_left htd hd.le
      rw [mul_add, mul_one, mul_one_div_cancel hd.ne'] at hh
      linarith
    have hs : t ≤ t^2 := by change 1 ≤ t at ht; nlinarith
    nlinarith
  have hh1 : 1/t^4 ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ ht)
  refine ⟨hn0, ht0, htd', by positivity, hh1, ?_, ?_⟩
  · change 1/(n : ℝ) ≤ 1/t^4
    rw [← he]
    apply one_div_le_one_div_of_le (pow_pos ht0 _)
    exact pow_le_pow_right₀ ht (by norm_num)
  · have hg := top_edge_scale_inequality (t := t) ht hC hD hlarge
    rw [he] at hg
    exact hg

end Erdos1132
