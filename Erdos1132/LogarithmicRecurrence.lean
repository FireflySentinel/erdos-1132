import Erdos1132.DyadicRecurrence

/-! # Positive-measure recurrence from logarithmic row estimates -/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace Erdos1132

def dyadicRow (j : ℕ) : ℕ := 2^(j+1)

theorem lt_dyadicRow (j : ℕ) : j < dyadicRow j := by
  induction j with
  | zero => norm_num [dyadicRow]
  | succ j ih =>
    simp only [dyadicRow, pow_succ] at *
    omega

theorem dyadicRow_strictMono : StrictMono dyadicRow := by
  intro j k hjk
  exact Nat.pow_lt_pow_right (by norm_num : 1 < (2:ℕ)) (by omega : j+1 < k+1)

theorem tendsto_dyadicRow : Tendsto dyadicRow atTop atTop :=
  tendsto_atTop_mono (fun j => (lt_dyadicRow j).le) tendsto_id

theorem log_dyadicRow (j : ℕ) : Real.log (dyadicRow j : ℝ) = (j+1:ℝ)*Real.log 2 := by
  simp [dyadicRow, Nat.cast_pow, Real.log_pow]

theorem measure_frequently_pos_of_logarithmic_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) (N : ℕ)
    (hlower : ∀ n ≥ N, c/Real.log n ≤ μ.real (A n))
    (hupper : ∀ n ≥ N, μ.real (A n) ≤ C/Real.log n)
    (hpair : ∀ n m : ℕ, N ≤ n → N ≤ m → n < m → μ.real (A n ∩ A m) ≤
      C*(1/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m))) :
    0 < μ {x | ∃ᶠ n in atTop, x ∈ A n} := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C' := C/(Real.log 2)^2+C/Real.log 2+1
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hcoef1 : 0 ≤ C/(Real.log 2)^2 := by positivity
  have hcoef2 : 0 ≤ C/Real.log 2 := by positivity
  have hN (j : ℕ) (hj : N ≤ j) : N ≤ dyadicRow j := hj.trans (lt_dyadicRow j).le
  have hfreq := measure_frequently_pos_of_eventual_dyadic_bounds μ (fun j => A (dyadicRow j))
    (fun j => hA _) (c := c/Real.log 2) (C := C') (by positivity) hC' N
    (fun j hj => ?_) (fun j hj => ?_) (fun j k hj hjk => ?_)
  · apply hfreq.trans_le
    apply measure_mono
    intro x hx
    exact tendsto_dyadicRow.frequently hx
  · have hh := hlower _ (hN j hj)
    rw [log_dyadicRow] at hh
    convert! hh using 1 <;> dsimp [harmonicWeight] <;> field_simp
  · have hh := hupper _ (hN j hj)
    rw [log_dyadicRow] at hh
    have he : C/((j+1:ℝ)*Real.log 2) = (C/Real.log 2)*harmonicWeight j := by
      dsimp [harmonicWeight]; field_simp
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C']; linarith)
      (harmonicWeight_pos j).le)
  · have hh := hpair _ _ (hN j hj) (hN k (hj.trans hjk.le)) (dyadicRow_strictMono hjk)
    have he : C*(1/(Real.log (dyadicRow j)*Real.log (dyadicRow k))+
        (dyadicRow j:ℝ)/((dyadicRow k:ℝ)*Real.log (dyadicRow k))) =
        (C/(Real.log 2)^2)*(harmonicWeight j*harmonicWeight k)+
          (C/Real.log 2)*dyadicOverlapError j k := by
      rw [log_dyadicRow, log_dyadicRow]
      simp only [dyadicRow, Nat.cast_pow, Nat.cast_ofNat, pow_succ, Nat.cast_mul,
        harmonicWeight, dyadicOverlapError, if_pos hjk]
      field_simp
    rw [he] at hh
    have h1 := mul_le_mul_of_nonneg_right (show C/(Real.log 2)^2 ≤ C' by dsimp [C']; linarith)
      (mul_nonneg (harmonicWeight_pos j).le (harmonicWeight_pos k).le)
    have h2 := mul_le_mul_of_nonneg_right (show C/Real.log 2 ≤ C' by dsimp [C']; linarith)
      (show 0 ≤ dyadicOverlapError j k by simp only [dyadicOverlapError, if_pos hjk]; positivity)
    exact hh.trans (by nlinarith)

end Erdos1132
