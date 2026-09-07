import Erdos1132.Counterexample.HarmonicCorrection
import Erdos1132.Counterexample.LogarithmicOperator
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The quantitative upper estimate after singularity subtraction

The phase factor cancels both nearest-node poles. The remaining error is
explicit in the mesh width, the phase derivative bound, and quadrature error.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set Finset
open scoped BigOperators

namespace Erdos1132.Counterexample

theorem amplitude_sum_upper_bound {n m : ℕ} {s t a B v L Q E q Λ : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n)
    (ha : 0 < a) (hs : a ≤ s) (hπs : a ≤ Real.pi-s)
    (ht : t ∈ Set.Ioo 0 1) (heq : (n : ℝ)*s/Real.pi + 1/2 = m+t)
    (hv : 0 < v) (hq : 0 < q) (hqbound : q ≤ 1 + B/n)
    (hQ : |Q - (-L + v*(2*Real.log q - Real.log (s*(Real.pi-s))))| ≤ E)
    (hΛ : Λ = |Real.cos (n*s)|/Real.pi *
      ((∑ i : Fin n, 1 / |(n : ℝ)*s/Real.pi + 1/2 - ((i : ℝ)+1)|) + Q/v)) :
    Λ ≤ |Real.cos (n*s)| * (2/Real.pi*Real.log n - L/(Real.pi*v) + 2/Real.pi) +
      2 + |Real.cos (n*s)| * (1/(n*a) + 2*B/(Real.pi*n) + E/(Real.pi*v)) := by
  let b := |Real.cos (n*s)|
  have hb : 0 ≤ b := abs_nonneg _
  have hbsin : b = Real.sin (Real.pi*t) := phase_abs_cos_eq_sin ht heq
  have hH : b*(∑ i : Fin n, 1 / |(n : ℝ)*s/Real.pi + 1/2 - ((i : ℝ)+1)|) ≤
      b*(Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2) + 2*Real.pi := by
    rw [hbsin, heq, Fin.sum_univ_eq_sum_range
      (fun k : ℕ => 1 / |(m : ℝ) + t - ((k : ℝ)+1)|)]
    exact weighted_shifted_harmonic_bound hmn.le ht
  have hlogs := harmonic_log_correction hn hm hmn ha hs hπs ht heq
  have hqlog : Real.log q ≤ B/n := (Real.log_le_sub_one_of_pos hq).trans (by linarith)
  have hlogπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hQup : Q ≤ -L + v*(2*Real.log q - Real.log (s*(Real.pi-s))) + E := by
    linarith [(abs_le.mp hQ).2]
  have hQdiv : Q/v ≤ -L/v + 2*Real.log q - Real.log (s*(Real.pi-s)) + E/v := by
    apply (div_le_iff₀ hv).mpr
    field_simp
    nlinarith [hQup]
  have hlogs0 : Real.log m + Real.log ((n-m : ℕ) : ℝ) - Real.log (s*(Real.pi-s)) ≤
      2*Real.log n + Real.pi/(n*a) := by linarith
  have hcombine : Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2 - L/v +
      2*Real.log q - Real.log (s*(Real.pi-s)) + E/v ≤
      2*Real.log n + Real.pi/(n*a) + 2 - L/v + 2*B/n + E/v := by
    have hh := mul_le_mul_of_nonneg_left hqlog (by norm_num : (0 : ℝ) ≤ 2)
    rw [← mul_div_assoc] at hh
    linarith
  rw [hΛ]
  change b/Real.pi * _ ≤ b*_ + 2 + b*_
  calc
    _ = (b*(∑ i : Fin n, 1 / |(n : ℝ)*s/Real.pi + 1/2 - ((i : ℝ)+1)|))/Real.pi +
        b/Real.pi*(Q/v) := by ring
    _ ≤ (b*(Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2) + 2*Real.pi)/Real.pi +
        b/Real.pi*(-L/v + 2*Real.log q - Real.log (s*(Real.pi-s)) + E/v) :=
      add_le_add (div_le_div_of_nonneg_right hH Real.pi_pos.le)
        (mul_le_mul_of_nonneg_left hQdiv (div_nonneg hb Real.pi_pos.le))
    _ = 2 + b/Real.pi*(Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2 - L/v +
        2*Real.log q - Real.log (s*(Real.pi-s)) + E/v) := by field_simp; ring
    _ ≤ 2 + b/Real.pi*(2*Real.log n + Real.pi/(n*a) + 2 - L/v + 2*B/n + E/v) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcombine (div_nonneg hb Real.pi_pos.le))
    _ = _ := by field_simp; ring

end Erdos1132.Counterexample
