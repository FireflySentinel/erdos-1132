import Erdos1132.Interpolation
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Degree blocks and the quantifiers in Section 7.5

Given the stated row estimates, pointwise eventual estimates in the amplitude
index pass to every sufficiently large row, not merely to a subsequence.
An eventual upper bound on an open interval implies relative non-density of
the corresponding good-point set in `(-1,1)`.

Companion note: §4, assembly of the array in Theorem 1.
-/

noncomputable section

open Set Filter

namespace Erdos1132.Counterexample

/-- Increasing thresholds can majorize any prescribed sequence of bounds. -/
theorem exists_strict_thresholds (T : ℕ → ℕ) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ j, T j ≤ N j := by
  let N : ℕ → ℕ := Nat.rec (T 0) (fun j n => max (n + 1) (T (j + 1)))
  have hsucc (j : ℕ) : N (j + 1) = max (N j + 1) (T (j + 1)) := rfl
  refine ⟨N, strictMono_nat_of_lt_succ (fun j => ?_), ?_⟩
  · rw [hsucc]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  · intro j
    cases j with
    | zero => exact le_rfl
    | succ j => rw [hsucc]; exact le_max_right _ _

/-- The index of the block containing row `n`, after the initial finite prefix. -/
def blockIndex (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun j => N j ≤ n) n

theorem threshold_le_at_blockIndex (N : ℕ → ℕ) {n : ℕ} (hn : N 0 ≤ n) :
    N (blockIndex N n) ≤ n := by
  exact Nat.findGreatest_spec (P := fun j => N j ≤ n) (Nat.zero_le n) hn

theorem blockIndex_tendsto {N : ℕ → ℕ} (hN : StrictMono N) :
    Tendsto (blockIndex N) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro j
  refine ⟨N j, ?_⟩
  intro n hn
  exact Nat.le_findGreatest ((hN.id_le j).trans hn) hn

def assembledRows (B : ℕ → ∀ n : ℕ, Nodes (n + 2)) (N : ℕ → ℕ)
    (n : ℕ) : Nodes (n + 2) := B (blockIndex N n) n

/-- The all-rows diagonal argument. The analytic upper estimates and the
pointwise eventual lower estimates for `q` are explicit hypotheses. -/
theorem assembled_eventually_upper
    (B : ℕ → ∀ n : ℕ, Nodes (n + 2))
    (N : ℕ → ℕ) (hN : StrictMono N) (K : ℕ → Set ℝ)
    (q : ℕ → ℝ → ℝ) (M : ℝ)
    (hrow : ∀ j n, N j ≤ n → ∀ x ∈ K j,
      (B j n).lebesgue x ≤ (2 / Real.pi) * Real.log (n + 2 : ℝ) + 3 - q j x / Real.pi)
    (hK : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ j in atTop, x ∈ K j)
    (hq : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ j in atTop, Real.pi * (M + 4) ≤ q j x) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ n in atTop,
      (assembledRows B N n).lebesgue x < (2 / Real.pi) * Real.log (n + 2 : ℝ) - M := by
  intro x hx
  filter_upwards [(blockIndex_tendsto hN).eventually (hK x hx),
    (blockIndex_tendsto hN).eventually (hq x hx), eventually_ge_atTop (N 0)]
    with n hnK hnq hn
  have h := hrow (blockIndex N n) n (threshold_le_at_blockIndex N hn) x hnK
  have hdiv : M + 4 ≤ q (blockIndex N n) x / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    simpa only [mul_comm] using hnq
  change (B (blockIndex N n) n).lebesgue x < _
  linarith

/-- The good-point set from (1.4), in the existing shifted-row convention. -/
def goodPoints (X : ∀ n : ℕ, Nodes (n + 2)) (C : ℝ) : Set ℝ :=
  {x | x ∈ Ioo (-1 : ℝ) 1 ∧ ∃ᶠ (n : ℕ) in atTop,
    (2 / Real.pi) * Real.log (n + 2 : ℝ) - C < (X n).lebesgue x}

theorem not_mem_goodPoints_of_eventually_le
    (X : ∀ n : ℕ, Nodes (n + 2)) {C x : ℝ}
    (h : ∀ᶠ n in atTop,
      (X n).lebesgue x ≤ (2 / Real.pi) * Real.log (n + 2 : ℝ) - C) :
    x ∉ goodPoints X C := by
  intro hx
  have hfrequent := hx.2.and_eventually h
  obtain ⟨n, hlt, hle⟩ := hfrequent.exists
  exact (not_lt_of_ge hle) hlt

/-- An eventual upper bound on a nonempty open subinterval implies non-density
of the good-point set relative to `(-1,1)`. -/
theorem not_dense_goodPoints_of_open_interval
    (X : ∀ n : ℕ, Nodes (n + 2)) {C b c : ℝ}
    (hbc : b < c) (hb : -1 ≤ b) (hc : c ≤ 1)
    (h : ∀ x ∈ Ioo b c, ∀ᶠ n in atTop,
      (X n).lebesgue x ≤ (2 / Real.pi) * Real.log (n + 2 : ℝ) - C) :
    ¬Dense {x : Ioo (-1 : ℝ) 1 | (x : ℝ) ∈ goodPoints X C} := by
  intro hdense
  let V : Set (Ioo (-1 : ℝ) 1) := {x | (x : ℝ) ∈ Ioo b c}
  have hopen : IsOpen V := isOpen_Ioo.preimage continuous_subtype_val
  have hne : V.Nonempty := by
    refine ⟨⟨(b + c) / 2, ⟨by linarith, by linarith⟩⟩, ?_⟩
    exact ⟨by linarith, by linarith⟩
  obtain ⟨x, hxV, hxG⟩ := hdense.inter_open_nonempty V hopen hne
  exact not_mem_goodPoints_of_eventually_le X (h x hxV) hxG

end Erdos1132.Counterexample
