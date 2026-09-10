import Erdos1132.Additive.PotentialL2
import Erdos1132.Additive.SecondMoment

/-! # Bounds on the normalization and on small-set logarithmic integrals

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped BigOperators
namespace Erdos1132

/-- The common square-integral bound for probability averages of logarithms
with poles in the interpolation interval. -/
def logSquareBound : ℝ := ∫ x in Set.Icc (-3 : ℝ) 3, (Real.log x)^2

theorem logSquareBound_nonneg : 0 ≤ logSquareBound :=
  integral_nonneg (fun _x => sq_nonneg _)

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem inv_two_pow_le_abs_weight (i : Fin n) : (2 : ℝ)⁻¹^n ≤ |X.weight i| := by
  have hd (j : Fin n) : |X.point i-X.point j| ≤ 2 := by
    have hi := X.mem_interval i
    have hj := X.mem_interval j
    apply abs_le.mpr
    constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]
  have hp : (∏ j ∈ Finset.univ.erase i, |X.point i-X.point j|) ≤ (2 : ℝ)^n := by
    calc
      _ ≤ ∏ _j ∈ Finset.univ.erase i, (2 : ℝ) :=
        Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hd j)
      _ = (2 : ℝ)^(n-1) := by simp
      _ ≤ (2 : ℝ)^n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
  have hpos : 0 < ∏ j ∈ Finset.univ.erase i, |X.point i-X.point j| := by
    apply Finset.prod_pos
    intro j hj
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (X.injective he).symm)
  have he : |X.weight i| = (∏ j ∈ Finset.univ.erase i, |X.point i-X.point j|)⁻¹ := by
    simp only [weight, Lagrange.nodalWeight, abs_prod, abs_inv, Finset.prod_inv_distrib]
  rw [he, inv_pow]
  exact inv_anti₀ hpos hp

theorem potentialNormalization_lower (hn : 0 < n) :
    -Real.log 2 ≤ X.potentialNormalization := by
  let i : Fin n := ⟨0, hn⟩
  have hlow : (2 : ℝ)⁻¹^n ≤ X.totalWeight :=
    (X.inv_two_pow_le_abs_weight i).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (X.weight j)) (Finset.mem_univ i))
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ)⁻¹^n) hlow
  rw [Real.log_pow, Real.log_inv] at hl
  unfold potentialNormalization
  apply (le_div_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr
  nlinarith

theorem integral_abs_empiricalLogPotential_le (hn : 0 < n) :
    (∫ x in Set.Icc (-2 : ℝ) 2, |X.empiricalLogPotential x|) ≤
      (4+logSquareBound)/2 := by
  have hf := X.integrableOn_empiricalLogPotential (-2) 2
  have hf2 := X.integrableOn_empiricalLogPotential_sq hn (-2) 2
  have hi : (∫ x in Set.Icc (-2 : ℝ) 2, 2*|X.empiricalLogPotential x|) ≤
      ∫ x in Set.Icc (-2 : ℝ) 2, 1+(X.empiricalLogPotential x)^2 := by
    apply integral_mono (hf.abs.const_mul 2) ((integrable_const 1).add hf2)
    intro x
    change 2*|X.empiricalLogPotential x| ≤ 1+(X.empiricalLogPotential x)^2
    nlinarith [sq_nonneg (|X.empiricalLogPotential x|-1), sq_abs (X.empiricalLogPotential x)]
  rw [integral_const_mul, integral_add (integrable_const 1) hf2, integral_const] at hi
  norm_num [Measure.real, Real.volume_Icc] at hi
  have hsq := X.integral_empiricalLogPotential_sq_le hn
  change _ ≤ logSquareBound at hsq
  linarith

theorem integral_abs_potential_small_set (hn : 0 < n) {s : Set ℝ}
    (hs : s ⊆ Set.Icc (-2) 2) :
    (∫ x in s, |X.empiricalLogPotential x|) ≤
      Real.sqrt (volume.real s * logSquareBound) := by
  have hsfin : volume s ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hs)
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin
  have hi := (X.integrableOn_empiricalLogPotential (-2) 2).mono_set hs
  have hi2 := (X.integrableOn_empiricalLogPotential_sq hn (-2) 2).mono_set hs
  have hcs := integral_sq_le_mass_mul_integral_sq (volume.restrict s) hi.abs
    (by simpa only [sq_abs] using! hi2)
  simp only [Measure.real, Measure.restrict_apply_univ, sq_abs] at hcs
  have hb : (∫ x in s, (X.empiricalLogPotential x)^2) ≤ logSquareBound := by
    apply le_trans _ (X.integral_empiricalLogPotential_sq_le hn)
    exact setIntegral_mono_set (X.integrableOn_empiricalLogPotential_sq hn _ _)
      (ae_of_all _ (fun x => sq_nonneg _)) (ae_of_all _ hs)
  apply (Real.le_sqrt (integral_nonneg (fun x => abs_nonneg _))
    (mul_nonneg ENNReal.toReal_nonneg logSquareBound_nonneg)).mpr
  exact hcs.trans (mul_le_mul_of_nonneg_left hb ENNReal.toReal_nonneg)

/-- An intervalwise Lebesgue bound controls the potential normalization with
constants depending only on the interval and its stated upper bound. -/
theorem potentialNormalization_upper (hn : 0 < n) {a b Λ : ℝ}
    (hab : a < b) (hI : Set.Icc a b ⊆ Set.Icc (-1) 1)
    (hΛ : ∀ x ∈ Set.Icc a b, X.lebesgue x ≤ Λ) :
    X.potentialNormalization ≤ Real.log (2*Λ)/n +
      (4+logSquareBound)/(2*(b-a)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hI2 : Set.Icc a b ⊆ Set.Icc (-2) 2 := by
    intro x hx
    have hx' := hI hx
    constructor <;> linarith [hx'.1, hx'.2]
  have hi := X.integrableOn_empiricalLogPotential a b
  have hlow : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      X.potentialNormalization - Real.log (2*Λ)/n ≤ X.empiricalLogPotential x := by
    have havoid : ∀ᵐ x : ℝ, x ∉ Set.range X.point := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
        (Set.finite_range X.point).measure_zero volume
    filter_upwards [ae_restrict_of_ae havoid, ae_restrict_mem measurableSet_Icc] with x hx hxI
    have hdist : ∀ i, 0 < |x-X.point i| := fun i => abs_pos.mpr
      (sub_ne_zero.mpr (fun he => hx ⟨i, he.symm⟩))
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let δ := Finset.univ.inf' Finset.univ_nonempty (fun i => |x-X.point i|)
    have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun i _ => hdist i)
    have hbound := (X.local_potential_bounds hn (hI hxI) hδ
      (fun i => Finset.inf'_le _ (Finset.mem_univ i)) (hΛ x hxI)).1
    rw [X.empiricalLogPotential_eq_realLogPotential (fun i he => hx ⟨i, he.symm⟩)]
    exact hbound
  have hle := integral_mono_ae (integrable_const
    (X.potentialNormalization-Real.log (2*Λ)/n)) hi hlow
  rw [integral_const] at hle
  have hvol : (volume.restrict (Set.Icc a b)).real Set.univ = b-a := by
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  change (volume.restrict (Set.Icc a b)).real Set.univ *
    (X.potentialNormalization-Real.log (2*Λ)/n) ≤ _ at hle
  rw [hvol] at hle
  have hupper : (∫ x in Set.Icc a b, X.empiricalLogPotential x) ≤ (4+logSquareBound)/2 := by
    calc
      _ ≤ ∫ x in Set.Icc a b, |X.empiricalLogPotential x| :=
        integral_mono hi hi.abs (fun x => le_abs_self _)
      _ ≤ ∫ x in Set.Icc (-2 : ℝ) 2, |X.empiricalLogPotential x| :=
        setIntegral_mono_set (X.integrableOn_empiricalLogPotential (-2) 2).abs
          (ae_of_all _ (fun x => abs_nonneg _)) (ae_of_all _ hI2)
      _ ≤ _ := X.integral_abs_empiricalLogPotential_le hn
  have hfinal : X.potentialNormalization-Real.log (2*Λ)/n ≤
      ((4+logSquareBound)/2)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by nlinarith)
  rw [div_div] at hfinal
  linarith

end Nodes
end Erdos1132
