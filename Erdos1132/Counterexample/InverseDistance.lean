import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Exact logarithmic integrals of the inverse-distance kernel

Paper: §7.2, the logarithmic integral estimate.
-/

open MeasureTheory Set

namespace Erdos1132.Counterexample

def radialAnnulus (x a R : ℝ) : Set ℝ := {y | a ≤ |x - y| ∧ |x - y| ≤ R}

theorem radialAnnulus_eq {x a R : ℝ} (ha : 0 < a) :
    radialAnnulus x a R = Icc (x - R) (x - a) ∪ Icc (x + a) (x + R) := by
  ext y
  simp only [radialAnnulus, mem_ofPred_eq, mem_union, mem_Icc, abs_le, le_abs]
  constructor
  · rintro ⟨h | h, hl, hu⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨hl, hu⟩ | ⟨hl, hu⟩)
    · exact ⟨Or.inl (by linarith), by linarith, by linarith⟩
    · exact ⟨Or.inr (by linarith), by linarith, by linarith⟩

theorem integrableOn_inverseDistance_left {x a R : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y => 1 / |x - y|) (Icc (x - R) (x - a)) := by
  apply ContinuousOn.integrableOn_Icc
  apply continuousOn_const.div (continuous_const.sub continuous_id).abs.continuousOn
  intro y hy
  change |x - y| ≠ 0
  exact ne_of_gt (lt_of_lt_of_le ha (by rw [abs_of_pos (by linarith [hy.2])]; linarith [hy.2]))

theorem integrableOn_inverseDistance_right {x a R : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y => 1 / |x - y|) (Icc (x + a) (x + R)) := by
  apply ContinuousOn.integrableOn_Icc
  apply continuousOn_const.div (continuous_const.sub continuous_id).abs.continuousOn
  intro y hy
  change |x - y| ≠ 0
  exact ne_of_gt (lt_of_lt_of_le ha (by rw [abs_of_neg (by linarith [hy.1])]; linarith [hy.1]))

theorem integrableOn_inverseDistance_annulus {x a R : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y => 1 / |x - y|) (radialAnnulus x a R) := by
  rw [radialAnnulus_eq ha]
  exact (integrableOn_inverseDistance_left ha).union (integrableOn_inverseDistance_right ha)

theorem integral_inverseDistance_left {x a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    (∫ y in Icc (x - R) (x - a), 1 / |x - y|) = Real.log (R / a) := by
  calc
    _ = ∫ y in Icc (x - R) (x - a), 1 / (x - y) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp
      rw [abs_of_pos (by linarith [hy.2])]
    _ = ∫ y in (x - R)..(x - a), 1 / (x - y) := by
      rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
    _ = ∫ t in a..R, 1 / t := by
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => 1 / t) x]
      simp
    _ = _ := integral_one_div_of_pos ha (ha.trans_le haR)

theorem integral_inverseDistance_right {x a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    (∫ y in Icc (x + a) (x + R), 1 / |x - y|) = Real.log (R / a) := by
  calc
    _ = ∫ y in Icc (x + a) (x + R), 1 / (y - x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp
      rw [abs_of_neg (by linarith [hy.1])]
      congr 1
      ring
    _ = ∫ y in (x + a)..(x + R), 1 / (y - x) := by
      rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
    _ = ∫ t in a..R, 1 / t := by
      rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => 1 / t) x]
      simp
    _ = _ := integral_one_div_of_pos ha (ha.trans_le haR)

/-- Both sides of the annulus contribute `log (R/a)`. -/
theorem integral_inverseDistance_annulus {x a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    (∫ y in radialAnnulus x a R, 1 / |x - y|) = 2 * Real.log (R / a) := by
  rw [radialAnnulus_eq ha]
  have hd : Disjoint (Icc (x - R) (x - a)) (Icc (x + a) (x + R)) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    linarith [hy.2, hz.1]
  rw [setIntegral_union hd measurableSet_Icc
    (integrableOn_inverseDistance_left ha) (integrableOn_inverseDistance_right ha),
    integral_inverseDistance_left ha haR, integral_inverseDistance_right ha haR]
  ring

/-- A subset of the annulus has no larger inverse-distance integral. -/
theorem integral_inverseDistance_le {S : Set ℝ} {x a R : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hS : S ⊆ radialAnnulus x a R) :
    (∫ y in S, 1 / |x - y|) ≤ 2 * Real.log (R / a) := by
  rw [← integral_inverseDistance_annulus (x := x) ha haR]
  exact setIntegral_mono_set (integrableOn_inverseDistance_annulus ha)
    (Filter.Eventually.of_forall (fun y => by positivity)) (Filter.Eventually.of_forall hS)

end Erdos1132.Counterexample
