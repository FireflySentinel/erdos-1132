import Erdos1132.Shared.BaireBounds
import Erdos1132.Counterexample.Theorem2

/-! # Quantifier consequences of Theorem 1 of the companion note

Companion note: §1 (the two uniform statements) and §5 (interval constants).
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Erdos1132.Counterexample

/-- A common eventual lower bound for the suprema on all compact interior
intervals makes the good-point set with constant `C + 1` dense. -/
theorem dense_goodPoints_of_uniform_interval_constant
    (X : ∀ n : ℕ, Nodes n) (C : ℝ)
    (h : ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 →
      ∀ᶠ (n : ℕ) in atTop, (2 / Real.pi) * Real.log (n : ℝ) - C ≤
        sSup ((X n).lebesgue '' Icc l r)) :
    Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
      (2 / Real.pi) * Real.log (n : ℝ) - (C + 1) < (X n).lebesgue x} := by
  simpa only [sub_sub] using dense_frequently_of_interval_sup
    (fun n => (X n).lebesgue) (fun n => (X n).continuous_lebesgue)
    (fun n => (2 / Real.pi) * Real.log (n : ℝ) - C) (ε := 1) (by norm_num) h

/-- The interval-constant corollary in companion §5: for any array whose every finite-constant
good-point set is non-dense, an eventual interval-supremum bound cannot use one
constant for all intervals. -/
theorem no_uniform_interval_constant
    (X : ∀ n : ℕ, Nodes n)
    (hX : ∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
      (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x}) :
    ¬∃ C : ℝ, ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 →
      ∀ᶠ (n : ℕ) in atTop, (2 / Real.pi) * Real.log (n : ℝ) - C ≤
        sSup ((X n).lebesgue '' Icc l r) := by
  rintro ⟨C, hC⟩
  exact hX (C + 1) (dense_goodPoints_of_uniform_interval_constant X C hC)

/-- For every proposed constant there is a compact interior interval on which
the supremum falls strictly below that bound in arbitrarily large rows. -/
theorem frequently_interval_sup_lt
    (X : ∀ n : ℕ, Nodes n)
    (hX : ∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
      (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x}) (C : ℝ) :
    ∃ l r : ℝ, l < r ∧ Icc l r ⊆ Ioo (-1 : ℝ) 1 ∧
      ∃ᶠ n in atTop, sSup ((X n).lebesgue '' Icc l r) <
        (2 / Real.pi) * Real.log (n : ℝ) - C := by
  have h := no_uniform_interval_constant X hX
  push Not at h
  simpa only [not_eventually, not_le] using h C

/-- Theorem 1 of the companion note and its interval-constant corollary for the same constructed array. -/
theorem theorem2_with_interval_corollary (M : ℝ) (hM : 0 < M) :
    ∃ X : ∀ n : ℕ, Nodes n,
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ n in atTop,
        (X n).lebesgue x ≤ (2 / Real.pi) * Real.log (n : ℝ) - M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x}) ∧
      (∀ C : ℝ, ∃ l r : ℝ, l < r ∧ Icc l r ⊆ Ioo (-1 : ℝ) 1 ∧
        ∃ᶠ n in atTop, sSup ((X n).lebesgue '' Icc l r) <
          (2 / Real.pi) * Real.log (n : ℝ) - C) := by
  obtain ⟨X, hI, hupper, hnd⟩ := theorem2 M hM
  exact ⟨X, hI, hupper, hnd, frequently_interval_sup_lt X hnd⟩

/-- No absolute additive constant works for all arrays, even with interior nodes. -/
theorem no_absolute_additive_constant :
    ¬∃ C : ℝ, ∀ X : ∀ n : ℕ, Nodes n,
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) →
      ∃ x ∈ Ioo (-1 : ℝ) 1, ∃ᶠ (n : ℕ) in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x := by
  rintro ⟨C, hC⟩
  obtain ⟨X, hI, hupper, _⟩ := theorem2 (max C 0 + 1) (by positivity)
  obtain ⟨x, hx, hfreq⟩ := hC X hI
  obtain ⟨n, hn, hle⟩ := (hfreq.and_eventually (hupper x hx)).exists
  linarith [le_max_left C 0]

/-- An array-dependent constant need not give a dense good-point set. -/
theorem no_arraywise_dense_constant :
    ¬∀ X : ∀ n : ℕ, Nodes n,
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) →
      ∃ C : ℝ, Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ (n : ℕ) in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < (X n).lebesgue x} := by
  intro h
  obtain ⟨X, hI, _, hnd⟩ := theorem2 1 (by norm_num)
  obtain ⟨C, hd⟩ := h X hI
  exact hnd C hd

end Erdos1132.Counterexample
