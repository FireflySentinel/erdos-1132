import Erdos1132.Additive.SecondMoment
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Intervals

/-! # Recurrence from the dyadic intersection estimates in Section 4

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators Topology
namespace Erdos1132

def harmonicWeight (j : ℕ) : ℝ := 1 / (j + 1 : ℝ)

def dyadicOverlapError (j k : ℕ) : ℝ :=
  if j < k then (2 : ℝ)^j / ((2 : ℝ)^k * (k + 1 : ℝ)) else 0

theorem harmonicWeight_pos (j : ℕ) : 0 < harmonicWeight j := by
  unfold harmonicWeight
  positivity

theorem sum_two_pow_le (k : ℕ) : (∑ j ∈ range k, (2 : ℝ)^j) ≤ 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [sum_range_succ, pow_succ]; linarith

theorem sum_dyadicOverlapError_le (s : Finset ℕ) (k : ℕ) :
    (∑ j ∈ s, dyadicOverlapError j k) ≤ harmonicWeight k := by
  unfold dyadicOverlapError harmonicWeight
  rw [← sum_filter, ← sum_div]
  have hsum : (∑ j ∈ s.filter (fun j => j < k), (2 : ℝ)^j) ≤ 2^k := by
    apply le_trans _ (sum_two_pow_le k)
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact mem_range.mpr (mem_filter.mp hj).2
    · intro j _ _
      positivity
  calc
    _ ≤ (2 : ℝ)^k / ((2 : ℝ)^k * (k+1 : ℝ)) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by field_simp

theorem dyadic_second_moment_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ j, μ.real (A j) ≤ C * harmonicWeight j)
    (hpair : ∀ j k : ℕ, j < k → μ.real (A j ∩ A k) ≤
      C * (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k))
    (s : Finset ℕ) :
    (∑ j ∈ s, ∑ k ∈ s, μ.real (A j ∩ A k)) ≤
      C * ((∑ j ∈ s, harmonicWeight j)^2 + 3 * ∑ j ∈ s, harmonicWeight j) := by
  have hfull (j k : ℕ) : μ.real (A j ∩ A k) ≤ C *
      (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k +
        dyadicOverlapError k j + if j = k then harmonicWeight j else 0) := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · have hh := hpair j k hjk
      simpa [dyadicOverlapError, hjk, not_lt_of_ge hjk.le, ne_of_lt hjk] using hh
    · simp only [Set.inter_self, dyadicOverlapError, lt_self_iff_false, ite_false,
        ite_true, add_zero]
      have hw := harmonicWeight_pos j
      nlinarith [hupper j]
    · have hh := hpair k j hkj
      rw [Set.inter_comm] at hh
      simpa [dyadicOverlapError, hkj, not_lt_of_ge hkj.le, ne_of_gt hkj,
        mul_comm, add_comm] using hh
  have hb := sum_le_sum (s := s) fun j _ => sum_le_sum (s := s) fun k _ => hfull j k
  simp only [sum_add_distrib, ← mul_sum] at hb
  have he1 : (∑ j ∈ s, ∑ k ∈ s, dyadicOverlapError j k) ≤
      ∑ j ∈ s, harmonicWeight j := by
    rw [sum_comm]
    exact sum_le_sum (fun k _ => sum_dyadicOverlapError_le s k)
  have he2 : (∑ j ∈ s, ∑ k ∈ s, dyadicOverlapError k j) ≤
      ∑ j ∈ s, harmonicWeight j :=
    sum_le_sum (fun j _ => sum_dyadicOverlapError_le s j)
  have hdiag : (∑ j ∈ s, ∑ k ∈ s, if j = k then harmonicWeight j else 0) =
      ∑ j ∈ s, harmonicWeight j := by
    apply sum_congr rfl
    intro j hj
    simp [hj]
  rw [hdiag] at hb
  have hprod : (∑ j ∈ s, harmonicWeight j * ∑ k ∈ s, harmonicWeight k) =
      (∑ j ∈ s, harmonicWeight j)^2 := by rw [← sum_mul]; ring
  rw [hprod] at hb
  nlinarith

/-- The reciprocal first moments and dyadic overlap bound force positive
measure recurrence, with no independence hypothesis. -/
theorem measure_frequently_pos_of_dyadic_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ j, MeasurableSet (A j)) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ j, c * harmonicWeight j ≤ μ.real (A j))
    (hupper : ∀ j, μ.real (A j) ≤ C * harmonicWeight j)
    (hpair : ∀ j k : ℕ, j < k → μ.real (A j ∩ A k) ≤
      C * (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k)) :
    0 < μ {x | ∃ᶠ j in atTop, x ∈ A j} := by
  apply measure_frequently_pos_of_second_moment μ A hA
    (C := 4*C/c^2) (by positivity)
  intro N
  have hdiverge : Tendsto (fun m => ∑ j ∈ range m, harmonicWeight j) atTop atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨m, hmN, hm⟩ := ((eventually_ge_atTop N).and
    (hdiverge.eventually_ge_atTop (1 + ∑ j ∈ range N, harmonicWeight j))).exists
  let s := Ico N m
  have hH : 1 ≤ ∑ j ∈ s, harmonicWeight j := by
    dsimp [s]
    rw [sum_Ico_eq_sub _ hmN]
    linarith
  have hS : c * (∑ j ∈ s, harmonicWeight j) ≤ ∑ j ∈ s, μ.real (A j) := by
    rw [mul_sum]
    exact sum_le_sum (fun j _ => hlower j)
  have hSpos : 0 < ∑ j ∈ s, μ.real (A j) :=
    (mul_pos hc (zero_lt_one.trans_le hH)).trans_le hS
  refine ⟨s, fun n hn => (mem_Ico.mp hn).1, hSpos, ?_⟩
  have hQ := dyadic_second_moment_bound μ A hC.le hupper hpair s
  have hSsq : (c * (∑ j ∈ s, harmonicWeight j))^2 ≤ (∑ j ∈ s, μ.real (A j))^2 :=
    pow_le_pow_left₀ (by positivity) hS 2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  have hc2 := sq_nonneg c
  have hHS : (∑ j ∈ s, harmonicWeight j) ≤ (∑ j ∈ s, harmonicWeight j)^2 := by nlinarith
  have hQ' : (∑ j ∈ s, ∑ k ∈ s, μ.real (A j ∩ A k)) ≤
      4*C*(∑ j ∈ s, harmonicWeight j)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hQ' hc2
  have hh' := mul_le_mul_of_nonneg_left hSsq (show 0 ≤ 4*C by positivity)
  nlinarith

theorem harmonicWeight_add_le (j N : ℕ) : harmonicWeight (j+N) ≤ harmonicWeight j := by
  unfold harmonicWeight
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem harmonicWeight_le_add_mul (j N : ℕ) :
    harmonicWeight j / (N+1 : ℝ) ≤ harmonicWeight (j+N) := by
  unfold harmonicWeight
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) j]

theorem dyadicOverlapError_add_le (j k N : ℕ) :
    dyadicOverlapError (j+N) (k+N) ≤ dyadicOverlapError j k := by
  by_cases hjk : j < k
  · have hjk' : j+N < k+N := Nat.add_lt_add_right hjk N
    unfold dyadicOverlapError
    rw [if_pos hjk, if_pos hjk']
    have heq : (2 : ℝ)^(j+N) / ((2 : ℝ)^(k+N) * (k+N+1 : ℝ)) =
        (2 : ℝ)^j / (2 : ℝ)^k * harmonicWeight (k+N) := by
      unfold harmonicWeight
      rw [pow_add, pow_add]
      push_cast
      field_simp
    push_cast
    rw [heq]
    calc
      _ ≤ (2 : ℝ)^j / (2 : ℝ)^k * harmonicWeight k :=
        mul_le_mul_of_nonneg_left (harmonicWeight_add_le k N) (by positivity)
      _ = _ := by unfold harmonicWeight; field_simp
  · simp [dyadicOverlapError, hjk]

/-- The same recurrence conclusion holds when the dyadic estimates start
only after an arbitrary finite index. -/
theorem measure_frequently_pos_of_eventual_dyadic_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ j, MeasurableSet (A j)) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) (N : ℕ)
    (hlower : ∀ j ≥ N, c * harmonicWeight j ≤ μ.real (A j))
    (hupper : ∀ j ≥ N, μ.real (A j) ≤ C * harmonicWeight j)
    (hpair : ∀ j k : ℕ, N ≤ j → j < k → μ.real (A j ∩ A k) ≤
      C * (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k)) :
    0 < μ {x | ∃ᶠ j in atTop, x ∈ A j} := by
  have hh := measure_frequently_pos_of_dyadic_bounds μ (fun j => A (j+N))
    (fun j => hA _) (c := c/(N+1)) (C := C) (by positivity) hC
    (fun j => ?_) (fun j => ?_) (fun j k hjk => ?_)
  · apply hh.trans_le
    apply measure_mono
    intro x hx
    exact (tendsto_add_atTop_nat N).frequently hx
  · calc
      _ = c * (harmonicWeight j / (N+1 : ℝ)) := by ring
      _ ≤ c * harmonicWeight (j+N) :=
        mul_le_mul_of_nonneg_left (harmonicWeight_le_add_mul j N) hc.le
      _ ≤ _ := hlower _ (Nat.le_add_left _ _)
  · exact (hupper _ (Nat.le_add_left _ _)).trans
      (mul_le_mul_of_nonneg_left (harmonicWeight_add_le j N) hC.le)
  · apply (hpair _ _ (Nat.le_add_left _ _) (Nat.add_lt_add_right hjk N)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add
      (mul_le_mul (harmonicWeight_add_le j N) (harmonicWeight_add_le k N)
        (harmonicWeight_pos _).le (harmonicWeight_pos _).le)
      (dyadicOverlapError_add_le j k N)

end Erdos1132
