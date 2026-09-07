import Erdos1132.Counterexample.CantorSmoothSequence
import Erdos1132.Counterexample.CantorEndpoint
import Erdos1132.Counterexample.AmplitudeApproximation
import Erdos1132.Counterexample.InteriorRows
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Theorem 2 with rows indexed by `n + 2`

For each positive M, a single array of distinct interior nodes has the
eventual pointwise deficit M and, for every finite C, a non-dense set of
points attaining the corresponding lower bound infinitely often.

Paper: §7.5, assembly of the array in Theorem 2.
-/
noncomputable section
open Set Filter Polynomial
open scoped Topology ContDiff
namespace Erdos1132.Counterexample

/-- The complete counterexample theorem with `n + 2` nodes in row `n`. -/
theorem theorem2_shifted (M : ℝ) (hM : 0 < M) :
    ∃ X : ∀ n : ℕ, Nodes (n+2),
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1:ℝ) 1, ∀ᶠ n in atTop,
        (X n).lebesgue x ≤ (2/Real.pi)*Real.log (n+2:ℝ)-M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1:ℝ) 1 | (x:ℝ) ∈ goodPoints X C}) := by
  classical
  let A := Real.pi*(M+4)
  have hA : 1 < A := by dsimp [A]; nlinarith [Real.pi_gt_three]
  obtain ⟨v,hvs,hvb,hvlower,hvlimit⟩ := exists_cantor_smooth_sequence hA
  have hamp : ∀ j, ∃ h : ℝ[X], 0 < h.coeff 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0) ∧
      ∀ x ∈ interval, |logarithmicOperator (amplitudeWeight h) x/amplitudeWeight h x-
        logarithmicOperator (v j) x/v j x| < (1/2:ℝ) := by
    intro j
    exact exists_amplitude_logarithmicRatio_approximation
      (fun x _ => ((hvs j).differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
      ((hvs j).continuous_deriv (by simp)).continuousOn (fun x _ => (hvb j x).1) (by norm_num)
  choose h hh0 hhzero hhclose using hamp
  let q : ℕ → ℝ → ℝ := fun j x => logarithmicOperator (amplitudeWeight (h j)) x/amplitudeWeight (h j) x
  have hqall : ∀ x ∈ Ioo (-1:ℝ) 1, ∀ᶠ j in atTop, Real.pi*(M+4) ≤ q j x := by
    intro x hx
    filter_upwards [hvlower x ⟨hx.1.le,hx.2.le⟩] with j hj
    have herr := (abs_lt.mp (hhclose j x ⟨hx.1.le,hx.2.le⟩)).1
    change A ≤ q j x
    change -(1/2:ℝ) < q j x-logarithmicOperator (v j) x/v j x at herr
    linarith
  have hqinterval : ∀ C : ℝ, ∃ b c : ℝ, b < c ∧ -1 ≤ b ∧ c ≤ 1 ∧
      ∀ x ∈ Ioo b c, ∀ᶠ j in atTop, Real.pi*(C+4) ≤ q j x := by
    intro C
    obtain ⟨b,c,hbc,hb,hc,hsub,hgt⟩ := exists_interval_cantor_ratio_gt hA (Real.pi*(C+4)+1)
    refine ⟨b,c,hbc,hb,hc,?_⟩
    intro x hx
    have hlim := hvlimit x (hsub hx)
    filter_upwards [hlim.eventually (Ioi_mem_nhds (hgt x hx))] with j hj
    have hxI : x ∈ interval := ⟨(hb.trans hx.1.le),(hx.2.le.trans hc)⟩
    have herr := (abs_lt.mp (hhclose j x hxI)).1
    change -(1/2:ℝ) < q j x-logarithmicOperator (v j) x/v j x at herr
    have hj' : Real.pi*(C+4)+1 < logarithmicOperator (v j) x/v j x := hj
    linarith
  choose B hB T hT using fun j => exists_amplitude_row_family (h j) (hhzero j) (hh0 j) j
  obtain ⟨N,hN,hNT⟩ := exists_strict_thresholds T
  have hrow : ∀ j n, N j ≤ n → ∀ x ∈ compactInterior j,
      (B j n).lebesgue x ≤ (2/Real.pi)*Real.log (n+2:ℝ)+3-q j x/Real.pi := by
    intro j n hn x hx
    exact hT j n ((hNT j).trans hn) x hx
  let X := assembledRows B N
  have hupper := assembled_eventually_upper B N hN compactInterior q M hrow
    (fun x hx => eventually_mem_compactInterior hx) hqall
  refine ⟨X,fun n i => hB (blockIndex N n) n i,?_,?_⟩
  · intro x hx
    filter_upwards [hupper x hx] with n hn
    exact hn.le
  · intro C
    obtain ⟨b,c,hbc,hb,hc,hq⟩ := hqinterval C
    apply not_dense_goodPoints_of_open_interval X hbc hb hc
    intro x hx
    have hxI : x ∈ Ioo (-1:ℝ) 1 := ⟨hb.trans_lt hx.1,hx.2.trans_le hc⟩
    filter_upwards [(blockIndex_tendsto hN).eventually (eventually_mem_compactInterior hxI),
      (blockIndex_tendsto hN).eventually (hq x hx), eventually_ge_atTop (N 0)] with n hnK hnq hn
    have hh := hrow (blockIndex N n) n (threshold_le_at_blockIndex N hn) x hnK
    have hd : C+4 ≤ q (blockIndex N n) x/Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      simpa only [mul_comm] using hnq
    change (B (blockIndex N n) n).lebesgue x ≤ _
    linarith

end Erdos1132.Counterexample
