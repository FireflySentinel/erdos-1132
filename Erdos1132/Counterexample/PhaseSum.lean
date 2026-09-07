import Erdos1132.Counterexample.CoordinateRows
import Erdos1132.Counterexample.AmplitudeRemainder
import Erdos1132.Counterexample.HarmonicCorrection

/-!
# Exact decomposition of the coordinate sum

The interpolation sum splits into a shifted harmonic sum and the midpoint
sum of the regular remainder. The fractional phase is interior whenever
the evaluation point is not a node.
-/

noncomputable section

open Set Finset
open scoped Topology ContDiff BigOperators

namespace Erdos1132.Counterexample

theorem exists_interior_phase_split {n : ℕ} {s : ℝ}
    (hleft : 1 ≤ (n : ℝ)*s/Real.pi) (hright : (n : ℝ)*s/Real.pi ≤ n-1)
    (hmid : ∀ i : Fin n, s ≠ phaseMidpoint n i) :
    ∃ m : ℕ, 0 < m ∧ m < n ∧ ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      (n : ℝ)*s/Real.pi + 1/2 = m+t := by
  let u : ℝ := n*s/Real.pi + 1/2
  let m := Nat.floor u
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hm : 0 < m := Nat.floor_pos.mpr (by dsimp [u]; linarith)
  have hmn : m < n := (Nat.floor_lt hu).mpr (by dsimp [u]; linarith)
  have hfloor : (m : ℝ) ≤ u := Nat.floor_le hu
  have hupper : u < m+1 := Nat.lt_floor_add_one u
  have hne : u ≠ m := by
    intro heq
    let i : Fin n := ⟨m-1, by omega⟩
    apply hmid i
    have hn : 0 < n := hm.trans hmn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hm1 : 1 ≤ m := hm
    change s = ((↑(m-1) : ℝ) + 1/2)*(Real.pi/n)
    rw [Nat.cast_sub hm1, Nat.cast_one]
    dsimp [u] at heq
    have hh := (div_eq_iff Real.pi_ne_zero).mp
      (show (n : ℝ)*s/Real.pi = m-1/2 by linarith)
    field_simp
    nlinarith [hh]
  refine ⟨m, hm, hmn, u-m, ⟨sub_pos.mpr (lt_of_le_of_ne hfloor hne.symm), by linarith⟩, ?_⟩
  dsimp [u]
  ring

theorem phase_distance_identity {n : ℕ} (hn : 0 < n) (s : ℝ) (i : Fin n) :
    s - phaseMidpoint n i = (Real.pi/n) *
      ((n : ℝ)*s/Real.pi + 1/2 - ((i : ℝ)+1)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold phaseMidpoint
  field_simp
  ring

theorem coordinate_sum_decomposition {v X : ℝ → ℝ} {n : ℕ}
    (hn : 0 < n) (s : ℝ) :
    (Real.pi/n) * (∑ i : Fin n,
      v (X (phaseMidpoint n i)) * |deriv X (phaseMidpoint n i)| /
        |X s - X (phaseMidpoint n i)|) =
      v (X s) * (∑ i : Fin n, 1 / |(n : ℝ)*s/Real.pi + 1/2 - ((i : ℝ)+1)|) +
      (Real.pi/n) * ∑ i : Fin n, amplitudeRemainder v X s (phaseMidpoint n i) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmesh : 0 < Real.pi/n := div_pos Real.pi_pos hnR
  unfold amplitudeRemainder
  rw [phase_distance_identity hn s i, abs_mul, abs_of_pos hmesh]
  field_simp
  ring

theorem lebesgue_coordinate_sum_decomposition {v X : ℝ → ℝ} {n : ℕ} {s Λ : ℝ}
    (hn : 0 < n) (hv : 0 < v (X s))
    (hΛ : Λ = |Real.cos (n*s)| / (n*v (X s)) *
      ∑ i : Fin n, v (X (phaseMidpoint n i)) * |deriv X (phaseMidpoint n i)| /
        |X s - X (phaseMidpoint n i)|) :
    Λ = |Real.cos (n*s)|/Real.pi *
      ((∑ i : Fin n, 1 / |(n : ℝ)*s/Real.pi + 1/2 - ((i : ℝ)+1)|) +
        ((Real.pi/n) * ∑ i : Fin n, amplitudeRemainder v X s (phaseMidpoint n i))/v (X s)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hh := coordinate_sum_decomposition (v := v) (X := X) hn s
  rw [hΛ]
  field_simp [hv.ne'] at hh ⊢
  nlinarith [congrArg (fun x : ℝ => |Real.cos (n*s)| * x) hh]

end Erdos1132.Counterexample
