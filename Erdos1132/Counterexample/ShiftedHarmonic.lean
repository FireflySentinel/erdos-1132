import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# The shifted harmonic sum in the amplitude estimate

The two singular terms are controlled after multiplication by the phase
factor. All remaining terms are bounded by ordinary harmonic numbers.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Erdos1132.Counterexample

theorem shifted_reciprocal_sum_bound {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ j ∈ range N, 1 / ((j : ℝ) + t)) ≤ 1/t + 1 + Real.log N := by
  cases N with
  | zero => simp; positivity
  | succ N =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_add]
    have htail : (∑ j ∈ range N, 1 / ((↑(j + 1) : ℝ) + t)) ≤ (harmonic N : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply sum_le_sum
      intro j _
      rw [← one_div]
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    have hstep : (harmonic N : ℝ) ≤ (harmonic (N + 1) : ℝ) := by
      rw [harmonic_succ]
      push_cast
      exact le_add_of_nonneg_right (by positivity)
    have hlog := harmonic_le_one_add_log (N + 1)
    push_cast at hlog htail ⊢
    linarith

theorem shifted_harmonic_split {n m : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    (∑ k ∈ range n, 1 / |(m : ℝ) + t - ((k : ℝ) + 1)|) =
      (∑ j ∈ range m, 1 / ((j : ℝ) + t)) +
      ∑ j ∈ range (n-m), 1 / ((j : ℝ) + (1-t)) := by
  have hn : n = m + (n-m) := (Nat.add_sub_of_le hmn).symm
  conv_lhs => rw [hn, sum_range_add]
  congr 1
  · rw [← sum_range_reflect (fun k => 1 / |(m : ℝ) + t - ((k : ℝ) + 1)|) m]
    apply sum_congr rfl
    intro j hj
    have hjm := mem_range.mp hj
    have hm1 : 1 ≤ m := by omega
    have hj1 : j ≤ m-1 := by omega
    rw [Nat.cast_sub hj1, Nat.cast_sub hm1, Nat.cast_one]
    have hid : (m : ℝ) + t - ((m - 1 - j) + 1) = j + t := by ring
    rw [hid, abs_of_pos (by have := ht.1; positivity : 0 < (j : ℝ) + t)]
  · apply sum_congr rfl
    intro j _
    push_cast
    have hid : (m : ℝ) + t - (m + j + 1) = -((j : ℝ) + (1-t)) := by ring
    rw [hid, abs_neg, abs_of_pos (by have := ht.2; positivity)]

theorem shifted_harmonic_bound {n m : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    (∑ k ∈ range n, 1 / |(m : ℝ) + t - ((k : ℝ) + 1)|) ≤
      Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2 + 1/t + 1/(1-t) := by
  rw [shifted_harmonic_split hmn ht]
  have hleft := shifted_reciprocal_sum_bound ht.1 m
  have hright := shifted_reciprocal_sum_bound (sub_pos.mpr ht.2) (n-m)
  linarith

theorem weighted_shifted_harmonic_bound {n m : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    Real.sin (Real.pi*t) *
        (∑ k ∈ range n, 1 / |(m : ℝ) + t - ((k : ℝ) + 1)|) ≤
      Real.sin (Real.pi*t) * (Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2) + 2*Real.pi := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hb : 0 ≤ Real.sin (Real.pi*t) := Real.sin_nonneg_of_mem_Icc
    ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have hl : Real.sin (Real.pi*t)/t ≤ Real.pi := by
    apply (div_le_iff₀ ht.1).mpr
    exact Real.sin_le (by positivity)
  have hr : Real.sin (Real.pi*t)/(1-t) ≤ Real.pi := by
    apply (div_le_iff₀ (sub_pos.mpr ht.2)).mpr
    have hh := Real.sin_le (show 0 ≤ Real.pi*(1-t) by positivity)
    rw [mul_sub, mul_one, Real.sin_pi_sub] at hh
    nlinarith [hh]
  have hh := mul_le_mul_of_nonneg_left (shifted_harmonic_bound hmn ht) hb
  calc
    _ ≤ Real.sin (Real.pi*t) * (Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2) +
        Real.sin (Real.pi*t)/t + Real.sin (Real.pi*t)/(1-t) := by
      calc
        _ ≤ Real.sin (Real.pi*t) *
          (Real.log m + Real.log ((n-m : ℕ) : ℝ) + 2 + 1/t + 1/(1-t)) := hh
        _ = _ := by ring
    _ ≤ _ := by linarith

end Erdos1132.Counterexample
