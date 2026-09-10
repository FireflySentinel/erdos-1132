import Erdos1132.Counterexample.DividedDifferences
import Erdos1132.Counterexample.MidpointQuadrature
import Mathlib.Analysis.BoundedVariation

/-!
# Uniform variation estimates with a moving jump

Multiplying a Lipschitz function by a sign jump adds at most twice its
supremum norm to its variation, independently of the jump's position.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Erdos1132.Counterexample

def jumpSign (s t : ℝ) : ℝ := if t < s then -1 else if s < t then 1 else 0

theorem jumpSign_monotone (s : ℝ) : Monotone (jumpSign s) := by
  intro t u htu
  unfold jumpSign
  split_ifs <;> norm_num at * <;> linarith

theorem abs_jumpSign_le (s t : ℝ) : |jumpSign s t| ≤ 1 := by
  unfold jumpSign
  split_ifs <;> norm_num

theorem jumpSign_eq_div_abs (s t : ℝ) : jumpSign s t = (t - s) / |t - s| := by
  unfold jumpSign
  split_ifs with hlt hgt
  · rw [abs_of_neg (sub_neg.mpr hlt)]
    apply (eq_div_iff (neg_ne_zero.mpr (sub_ne_zero.mpr hlt.ne))).mpr
    ring
  · rw [abs_of_pos (sub_pos.mpr hgt)]
    exact (div_self (sub_ne_zero.mpr hgt.ne')).symm
  · have he : t = s := by linarith
    simp [he]

theorem variation_jumpSign {s l r : ℝ} (hs : s ∈ Ioo l r) :
    eVariationOn (jumpSign s) (Icc l r) = 2 := by
  have h := (jumpSign_monotone s).monotoneOn univ |>.eVariationOn_eq
    (a := l) (b := r) (by simp) (by simp)
  norm_num [jumpSign, hs.1, hs.2, not_lt_of_ge hs.2.le] at h ⊢
  exact h

theorem variation_le_of_derivative_bound {g : ℝ → ℝ} {l r D : ℝ}
    (hD : 0 ≤ D) (hg : ∀ t ∈ Icc l r, DifferentiableAt ℝ g t)
    (hd : ∀ t ∈ Icc l r, |deriv g t| ≤ D) :
    eVariationOn g (Icc l r) ≤ ENNReal.ofReal (D * (r - l)) := by
  have hlip : LipschitzOnWith ⟨D, hD⟩ g (Icc l r) :=
    (convex_Icc l r).lipschitzOnWith_of_nnnorm_deriv_le hg
      (fun t ht => by change ‖deriv g t‖ ≤ D; simpa only [Real.norm_eq_abs] using hd t ht)
  have h := hlip.comp_eVariationOn_le (g := id) (mapsTo_id (Icc l r))
  rw [Function.comp_id, eVariationOn_id_Icc] at h
  simpa only [ENNReal.ofReal_mul hD, ENNReal.ofReal_eq_coe_nnreal hD] using! h

theorem variation_jump_mul_le {g : ℝ → ℝ} {s l r A D : ℝ}
    (hs : s ∈ Ioo l r) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hg : ∀ t ∈ Icc l r, DifferentiableAt ℝ g t)
    (ha : ∀ t ∈ Icc l r, |g t| ≤ A)
    (hd : ∀ t ∈ Icc l r, |deriv g t| ≤ D) :
    eVariationOn (fun t => jumpSign s t * g t) (Icc l r) ≤
      ENNReal.ofReal (D * (r - l) + 2 * A) := by
  have h := eVariationOn_fun_mul_le
    (f := jumpSign s) (g := g) (C := 1) (D := ENNReal.ofReal A)
    (fun t _ => by simpa [Real.enorm_eq_ofReal_abs] using
      ENNReal.ofReal_le_ofReal (abs_jumpSign_le s t))
    (fun t ht => by simpa [Real.enorm_eq_ofReal_abs] using
      ENNReal.ofReal_le_ofReal (ha t ht))
  rw [one_mul, variation_jumpSign hs] at h
  apply h.trans
  calc
    eVariationOn g (Icc l r) + ENNReal.ofReal A * 2
      ≤ ENNReal.ofReal (D * (r - l)) + ENNReal.ofReal A * 2 :=
        add_le_add (variation_le_of_derivative_bound hD hg hd) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_add (mul_nonneg hD (sub_nonneg.mpr (hs.1.trans hs.2).le))
        (mul_nonneg (by norm_num) hA)]
      congr 1
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [mul_comm]

theorem jumpSign_measurable (s : ℝ) : Measurable (jumpSign s) :=
  (jumpSign_monotone s).measurable

theorem jump_mul_intervalIntegrable {g : ℝ → ℝ} {s l r : ℝ}
    (hlr : l ≤ r) (hg : ContinuousOn g (Icc l r)) :
    IntervalIntegrable (fun t => jumpSign s t * g t) volume l r := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mpr
  have hgi : IntegrableOn g (Icc l r) volume := hg.integrableOn_Icc
  apply hgi.norm.mono'
    (((jumpSign_measurable s).aemeasurable.mul
      (hg.aemeasurable measurableSet_Icc)).aestronglyMeasurable)
  filter_upwards [] with t
  simpa only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_mul] using
    mul_le_of_le_one_left (abs_nonneg (g t)) (abs_jumpSign_le s t)

end Erdos1132.Counterexample
