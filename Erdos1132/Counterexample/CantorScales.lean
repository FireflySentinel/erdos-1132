import Erdos1132.Counterexample.Constants
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The scales of the Cantor construction

The removed proportions are summable, while the number of children forces
a fixed logarithmic contribution from the gaps at every stage.

Companion note: §2.1, the compact set and its gaps.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace Erdos1132.Counterexample

def cantorProportion (ρ : ℝ) (k : ℕ) : ℝ := ρ/2/(2:ℝ)^k

def cantorBranching (ρ : ℝ) (k : ℕ) : ℕ := ⌈Real.exp (1/cantorProportion ρ k)⌉₊

def cantorLength (ρ : ℝ) : ℕ → ℝ
  | 0 => 2
  | k+1 => (1-cantorProportion ρ k)*cantorLength ρ k/cantorBranching ρ k

def cantorGapLength (ρ : ℝ) (k : ℕ) : ℝ :=
  cantorProportion ρ k*cantorLength ρ k/(cantorBranching ρ k-1 : ℕ)

theorem gapScale_le_quarter {A : ℝ} (hA : 1 < A) : gapScale A ≤ 1/4 := by
  have he : (4 : ℝ) ≤ Real.exp 2 := by
    have hh := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hh ⊢
    linarith
  have hρ : gapScale A ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg] at hρ
  exact hρ.trans (by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he)

theorem cantorProportion_pos {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) : 0 < cantorProportion ρ k := by
  dsimp [cantorProportion]
  positivity

theorem cantorProportion_le {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) : cantorProportion ρ k ≤ ρ/2 := by
  unfold cantorProportion
  exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))

theorem cantorProportion_sum (ρ : ℝ) : HasSum (cantorProportion ρ) ρ := hasSum_geometric_two' ρ

theorem cantorProportion_le_eighth {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorProportion ρ k ≤ 1/8 := by linarith [cantorProportion_le hρ k]

theorem cantorBranching_ge {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    32 ≤ cantorBranching ρ k := by
  have hδ := cantorProportion_pos hρ k
  have hδ8 := cantorProportion_le_eighth hρ hρ4 k
  have hinv : (8 : ℝ) ≤ 1/cantorProportion ρ k := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have he : (32 : ℝ) ≤ Real.exp (1/cantorProportion ρ k) := by
    have hh := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 1/cantorProportion ρ k by positivity)
    nlinarith
  have hh := he.trans (Nat.le_ceil _)
  exact_mod_cast hh

theorem cantorProportion_log_branching {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    1 ≤ cantorProportion ρ k*Real.log (cantorBranching ρ k) := by
  have hδ := cantorProportion_pos hρ k
  have hh := Real.log_le_log (Real.exp_pos (1/cantorProportion ρ k)) (Nat.le_ceil _)
  rw [Real.log_exp] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hδ.le
  simpa only [cantorBranching, mul_one_div_cancel hδ.ne'] using hmul

theorem cantorLength_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    0 < cantorLength ρ k := by
  induction k with
  | zero => norm_num [cantorLength]
  | succ k hk =>
    rw [cantorLength]
    apply div_pos (mul_pos (by linarith [cantorProportion_le_eighth hρ hρ4 k]) hk)
    have hh := cantorBranching_ge hρ hρ4 k
    exact_mod_cast (show 0 < cantorBranching ρ k by omega)

theorem cantorGapLength_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    0 < cantorGapLength ρ k := by
  unfold cantorGapLength
  apply div_pos (mul_pos (cantorProportion_pos hρ k) (cantorLength_pos hρ hρ4 k))
  have hh := cantorBranching_ge hρ hρ4 k
  exact_mod_cast (show 0 < cantorBranching ρ k-1 by omega)

theorem cantor_subdivision_length {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    (cantorBranching ρ k : ℝ)*cantorLength ρ (k+1) +
      (cantorBranching ρ k-1 : ℕ)*cantorGapLength ρ k = cantorLength ρ k := by
  have hh := cantorBranching_ge hρ hρ4 k
  have hm : (cantorBranching ρ k : ℝ) ≠ 0 := by exact_mod_cast (show cantorBranching ρ k ≠ 0 by omega)
  have hm' : ((cantorBranching ρ k-1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show cantorBranching ρ k-1 ≠ 0 by omega)
  simp only [cantorLength, cantorGapLength]
  field_simp
  ring

theorem cantorLength_step_le_half {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorLength ρ (k+1) ≤ cantorLength ρ k/2 := by
  have hlen := cantorLength_pos hρ hρ4 k
  have hδ := cantorProportion_pos hρ k
  have hm : (2 : ℝ) ≤ cantorBranching ρ k := by
    have hh := cantorBranching_ge hρ hρ4 k
    exact_mod_cast (show 2 ≤ cantorBranching ρ k by omega)
  rw [cantorLength]
  apply (div_le_iff₀ (show 0 < (cantorBranching ρ k : ℝ) by linarith)).mpr
  nlinarith

theorem cantorLength_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorLength ρ k ≤ 2*(1/2 : ℝ)^k := by
  induction k with
  | zero => simp [cantorLength]
  | succ k hk =>
    have hh := cantorLength_step_le_half hρ hρ4 k
    rw [pow_succ]
    linarith

theorem cantorLength_tendsto_zero {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    Tendsto (cantorLength ρ) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => (cantorLength_pos hρ hρ4 k).le) (cantorLength_bound hρ hρ4)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_mul 2


theorem cantorGapLength_le_child {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorGapLength ρ k ≤ cantorLength ρ (k+1) := by
  have hδ := cantorProportion_pos hρ k
  have hδ8 := cantorProportion_le_eighth hρ hρ4 k
  have hlen := cantorLength_pos hρ hρ4 k
  have hm := cantorBranching_ge hρ hρ4 k
  have hmR : (2 : ℝ) ≤ cantorBranching ρ k := by exact_mod_cast (show 2 ≤ cantorBranching ρ k by omega)
  have hm1 : 1 ≤ cantorBranching ρ k := by omega
  have hden : 0 < ((cantorBranching ρ k-1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < cantorBranching ρ k-1 by omega)
  unfold cantorGapLength
  rw [cantorLength]
  apply (div_le_div_iff₀ hden (show 0 < (cantorBranching ρ k : ℝ) by linarith)).mpr
  rw [Nat.cast_sub hm1, Nat.cast_one]
  have hcoeff : cantorProportion ρ k*(cantorBranching ρ k : ℝ) ≤
      (1-cantorProportion ρ k)*((cantorBranching ρ k : ℝ)-1) := by
    have hh := mul_nonneg (show 0 ≤ 1/8-cantorProportion ρ k by linarith)
      (show 0 ≤ 2*(cantorBranching ρ k : ℝ)-1 by linarith)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoeff hlen.le
  nlinarith

theorem cantorGapLength_lower {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (k : ℕ) :
    cantorProportion ρ k*cantorLength ρ k/cantorBranching ρ k ≤ cantorGapLength ρ k := by
  have hm := cantorBranching_ge hρ hρ4 k
  have hden : 0 < ((cantorBranching ρ k-1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < cantorBranching ρ k-1 by omega)
  apply div_le_div_of_nonneg_left
    (mul_nonneg (cantorProportion_pos hρ k).le (cantorLength_pos hρ hρ4 k).le) hden
  exact_mod_cast Nat.sub_le (cantorBranching ρ k) 1

end Erdos1132.Counterexample
