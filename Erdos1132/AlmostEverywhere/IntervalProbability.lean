import Erdos1132.Shared.BoundaryMeasure

/-! # Stability of the centered interval probability

Paper: §6, Theorem 1(ii) and the positive-measure argument used in §8.
-/

noncomputable section

open MeasureTheory Filter Complex Metric
open scoped Topology

namespace Erdos1132

theorem intervalHarmonic_affine (a b u : ℝ) {γ : ℝ} (hγ : γ ≠ 0) (z : ℂ) :
    intervalHarmonic (u + γ * a) (u + γ * b) z =
      intervalHarmonic a b ((z - u) / γ) := by
  unfold intervalHarmonic
  congr 2
  have hc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have he (v : ℝ) : (z - u) / γ - v = (z - (u + γ * v : ℝ)) / γ := by
    push_cast
    field_simp
    ring
  rw [he a, he b, div_div_div_cancel_right₀ hc]

theorem intervalHarmonic_centered {K : ℝ} (hK : 0 < K) :
    intervalHarmonic (-K) K (-I) = 2 / Real.pi * Real.arctan K := by
  have he : inverseCayley K = -exp ((2 * Real.arctan K : ℝ) * I) := by
    have h := circleMap_cayleyAngle K
    simpa [circleMap, cayleyAngle, Complex.ofReal_add, add_mul, exp_add,
      Complex.exp_pi_mul_I] using h.symm
  have hq : (-I - ((-K : ℝ) : ℂ)) / (-I - (K : ℂ)) = -inverseCayley K := by
    unfold inverseCayley
    push_cast
    rw [show -I - (K : ℂ) = -((K : ℂ) + I) by ring, div_neg_eq_neg_div]
    congr 1
    ring
  rw [intervalHarmonic, hq, he, neg_neg, arg_exp_mul_I,
    (toIocMod_eq_self Real.two_pi_pos).mpr]
  · ring
  · constructor
    · linarith [Real.arctan_pos.mpr hK, Real.pi_pos]
    · linarith [Real.arctan_lt_pi_div_two K]

theorem centered_probability_gt_half {K : ℝ} (hK : 1 < K) :
    1 / 2 < intervalHarmonic (-K) K (-I) := by
  rw [intervalHarmonic_centered (lt_trans zero_lt_one hK)]
  have h := Real.arctan_strictMono hK
  rw [Real.arctan_one] at h
  have hp := Real.pi_pos
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ hp).mpr
  nlinarith

theorem centered_probability_stable {K : ℝ} (hK : 1 < K) :
    ∃ q > 0, ∃ δ > 0, ∀ z : ℂ, ‖z + I‖ < δ →
      (1 + q) / 2 < intervalHarmonic (-K) K z := by
  have hp := centered_probability_gt_half hK
  let q := intervalHarmonic (-K) K (-I) - 1 / 2
  have hq : 0 < q := sub_pos.mpr hp
  have hab : -K < K := by linarith
  have hc : ContinuousAt (intervalHarmonic (-K) K) (-I) := by
    exact (harmonicAt_intervalHarmonic_comp (z := -I) hab analyticAt_id (by simp)).1.continuousAt
  have he : ∀ᶠ z in 𝓝 (-I), (1 + q) / 2 < intervalHarmonic (-K) K z :=
    hc.eventually (lt_mem_nhds (show (1 + q) / 2 < intervalHarmonic (-K) K (-I) by
      dsimp only [q]
      linarith))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨q, hq, δ, hδ, fun z hz => hd ?_⟩
  simpa [dist_eq_norm, sub_neg_eq_add] using hz

end Erdos1132
