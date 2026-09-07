import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Midpoint quadrature with a variation bound

The error is bounded by the mesh width times the total variation. The
estimate includes functions with jumps, uniformly in the location of a jump.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1132.Counterexample

theorem midpoint_quadrature_error_bound {f : ℝ → ℝ} {L : ℝ} {n : ℕ}
    (hL : 0 ≤ L) (hn : 0 < n)
    (hBV : BoundedVariationOn f (Icc 0 L)) (hfi : IntervalIntegrable f volume 0 L) :
    |(L / n) * (∑ k ∈ Finset.range n, f (((k : ℝ) + 1 / 2) * (L / n))) -
      ∫ t in (0 : ℝ)..L, f t| ≤
        (L / n) * (eVariationOn f (Icc 0 L)).toReal := by
  let d : ℝ := L / n
  let a : ℕ → ℝ := fun k => k * d
  let m : ℕ → ℝ := fun k => ((k : ℝ) + 1 / 2) * d
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hd : 0 ≤ d := div_nonneg hL (Nat.cast_nonneg _)
  have ha : Monotone a := fun i j hij => mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hd
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = L := by dsimp [a, d]; field_simp
  have hlen (k : ℕ) : a (k + 1) - a k = d := by dsimp [a]; push_cast; ring
  have hsub {k : ℕ} (hk : k < n) : Icc (a k) (a (k + 1)) ⊆ Icc 0 L := by
    rw [← ha0, ← han]
    exact Icc_subset_Icc (ha (Nat.zero_le _)) (ha (by omega))
  have hmid (k : ℕ) : m k ∈ Icc (a k) (a (k + 1)) := by
    dsimp [m, a]
    push_cast
    constructor <;> nlinarith
  have hb {k : ℕ} (hk : k < n) : BoundedVariationOn f (Icc (a k) (a (k + 1))) :=
    hBV.mono (hsub hk)
  have hi {k : ℕ} (hk : k < n) : IntervalIntegrable f volume (a k) (a (k + 1)) := by
    apply hfi.mono_set
    rw [uIcc_of_le (ha (Nat.le_succ _)), uIcc_of_le hL]
    exact hsub hk
  have hcell {k : ℕ} (hk : k < n) :
      |d * f (m k) - ∫ t in a k..a (k + 1), f t| ≤
        d * (eVariationOn f (Icc (a k) (a (k + 1)))).toReal := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a k) (b := a (k + 1))
      (f := fun t => f (m k) - f t)
      (C := (eVariationOn f (Icc (a k) (a (k + 1)))).toReal) (fun t ht => by
        rw [uIoc_of_le (ha (Nat.le_succ _))] at ht
        simpa only [Real.norm_eq_abs, ← Real.dist_eq] using
          (hb hk).dist_le (hmid k) ⟨ht.1.le, ht.2⟩)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hi hk),
      intervalIntegral.integral_const, smul_eq_mul, hlen, abs_of_nonneg hd,
      Real.norm_eq_abs, mul_comm _ d] at h
    exact h
  have hsumvar : (∑ k ∈ Finset.range n,
      (eVariationOn f (Icc (a k) (a (k + 1)))).toReal) =
        (eVariationOn f (Icc 0 L)).toReal := by
    rw [← ENNReal.toReal_sum (fun k hk => hb (Finset.mem_range.mp hk))]
    rw [eVariationOn.sum' f ha, ha0, han]
  have hint := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := n)
    (fun k hk => hi hk)
  rw [ha0, han] at hint
  change |d * (∑ k ∈ Finset.range n, f (m k)) - ∫ t in (0 : ℝ)..L, f t| ≤ _
  rw [← hint, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n, |d * f (m k) - ∫ t in a k..a (k + 1), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, d * (eVariationOn f (Icc (a k) (a (k + 1)))).toReal :=
      Finset.sum_le_sum (fun k hk => hcell (Finset.mem_range.mp hk))
    _ = _ := by rw [← Finset.mul_sum, hsumvar]

/-- A common variation bound gives one `C/n` bound for every member of an
arbitrarily indexed family, including a moving singularity parameter. -/
theorem uniform_midpoint_quadrature_error {ι : Type*} {R : ι → ℝ → ℝ} {L V : ℝ}
    (hL : 0 ≤ L)
    (hBV : ∀ s, BoundedVariationOn (R s) (Icc 0 L))
    (hi : ∀ s, IntervalIntegrable (R s) volume 0 L)
    (hV : ∀ s, (eVariationOn (R s) (Icc 0 L)).toReal ≤ V)
    (s : ι) {n : ℕ} (hn : 0 < n) :
    |(L / n) * (∑ k ∈ Finset.range n, R s (((k : ℝ) + 1 / 2) * (L / n))) -
      ∫ t in (0 : ℝ)..L, R s t| ≤ L * V / n := by
  have h := (midpoint_quadrature_error_bound hL hn (hBV s) (hi s)).trans
    (mul_le_mul_of_nonneg_left (hV s) (div_nonneg hL (Nat.cast_nonneg n)))
  simpa only [div_mul_eq_mul_div] using h

end Erdos1132.Counterexample
