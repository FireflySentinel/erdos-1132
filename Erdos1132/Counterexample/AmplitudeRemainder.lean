import Erdos1132.Counterexample.JumpVariation

/-!
# Removing the diagonal singularity in the amplitude sum

The remainder is a sign jump times a regular function built from divided
differences. Its variation and integral can therefore be estimated on the
whole interval.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

def amplitudeRemainder (v X : ℝ → ℝ) (s t : ℝ) : ℝ :=
  v (X t) * |deriv X t| / |X s - X t| - v (X s) / |s - t|

def regularRemainder (v X : ℝ → ℝ) (s t : ℝ) : ℝ :=
  dslope v (X s) (X t) * deriv X t +
    v (X s) * deriv (dslope X s) t / dslope X s t

theorem amplitudeRemainder_eq_jump_mul {v X : ℝ → ℝ} {s t : ℝ}
    (hXt : DifferentiableAt ℝ X t) (hd : deriv X t ≤ 0)
    (hD : dslope X s t < 0) :
    amplitudeRemainder v X s t = jumpSign s t * regularRemainder v X s t := by
  by_cases hts : t = s
  · subst t
    simp [amplitudeRemainder, jumpSign]
  · have hX : X t - X s = (t - s) * dslope X s t := by
      simpa only [smul_eq_mul] using (sub_smul_dslope X s t).symm
    have hV : v (X t) = v (X s) +
        (t - s) * dslope X s t * dslope v (X s) (X t) := by
      have hh := sub_smul_dslope v (X s) (X t)
      simp only [smul_eq_mul, hX] at hh
      linarith
    unfold amplitudeRemainder regularRemainder
    rw [abs_of_nonpos hd, abs_sub_comm (X s) (X t), hX, abs_mul, abs_of_neg hD,
      abs_sub_comm s t, jumpSign_eq_div_abs, (dslope_hasDerivAt hXt hts).deriv, hX, hV]
    field_simp [hD.ne, sub_ne_zero.mpr hts]
    ring

theorem regularRemainder_hasDerivAt {v X : ℝ → ℝ} {s t : ℝ}
    (hv : ContDiffAt ℝ ⊤ v (X t)) (hX : ContDiffAt ℝ ⊤ X t)
    (hD : dslope X s t ≠ 0) :
    HasDerivAt (regularRemainder v X s)
      ((deriv (dslope v (X s)) (X t) * deriv X t) * deriv X t +
        dslope v (X s) (X t) * deriv (deriv X) t +
        v (X s) * (deriv (deriv (dslope X s)) t * dslope X s t -
          deriv (dslope X s) t * deriv (dslope X s) t) / (dslope X s t)^2) t := by
  have hx := hX.differentiableAt (by simp)
  have hx' := (hX.derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  have hds := (contDiffAt_dslope hX s).differentiableAt (by simp)
  have hds' := ((contDiffAt_dslope hX s).derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  have hvds := (contDiffAt_dslope hv (X s)).differentiableAt (by simp)
  have hh := ((hvds.hasDerivAt.comp t hx.hasDerivAt).mul hx'.hasDerivAt).add
    ((hds'.hasDerivAt.div hds.hasDerivAt hD).const_mul (v (X s)))
  simp only [Function.comp_apply] at hh
  convert! hh using 1
  · ext u
    simp only [regularRemainder, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply]
    ring
  · ring

theorem regularRemainder_bounds {v X : ℝ → ℝ} {s t M d : ℝ}
    (hv : ContDiffAt ℝ ⊤ v (X t)) (hX : ContDiffAt ℝ ⊤ X t)
    (hM : 0 ≤ M) (hd : 0 < d) (hden : d ≤ |dslope X s t|)
    (hv0 : |v (X s)| ≤ M) (hSv : |dslope v (X s) (X t)| ≤ M)
    (hSv' : |deriv (dslope v (X s)) (X t)| ≤ M)
    (hx1 : |deriv X t| ≤ M) (hx2 : |deriv (deriv X) t| ≤ M)
    (hD0 : |dslope X s t| ≤ M) (hD1 : |deriv (dslope X s) t| ≤ M)
    (hD2 : |deriv (deriv (dslope X s)) t| ≤ M) :
    |regularRemainder v X s t| ≤ M^2 + M^2 / d ∧
    |deriv (regularRemainder v X s) t| ≤ M^3 + M^2 + 2*M^3 / d^2 := by
  have hne : dslope X s t ≠ 0 := abs_pos.mp (hd.trans_le hden)
  constructor
  · unfold regularRemainder
    calc
      _ ≤ |dslope v (X s) (X t)| * |deriv X t| +
          |v (X s)| * |deriv (dslope X s) t| / |dslope X s t| := by
        simpa only [abs_mul, abs_div] using abs_add_le
          (dslope v (X s) (X t) * deriv X t)
          (v (X s) * deriv (dslope X s) t / dslope X s t)
      _ ≤ M*M + (M*M)/d := add_le_add
        (mul_le_mul hSv hx1 (abs_nonneg _) hM)
        (div_le_div₀ (by positivity) (mul_le_mul hv0 hD1 (abs_nonneg _) hM) hd hden)
      _ = _ := by ring
  · rw [(regularRemainder_hasDerivAt hv hX hne).deriv]
    have h₁ : |(deriv (dslope v (X s)) (X t) * deriv X t) * deriv X t| ≤ M^3 := by
      rw [abs_mul, abs_mul]
      calc
        _ ≤ (M*M)*M := mul_le_mul
          (mul_le_mul hSv' hx1 (abs_nonneg _) hM) hx1 (abs_nonneg _) (mul_nonneg hM hM)
        _ = _ := by ring
    have h₂ : |dslope v (X s) (X t) * deriv (deriv X) t| ≤ M^2 := by
      rw [abs_mul]
      simpa only [pow_two] using mul_le_mul hSv hx2 (abs_nonneg _) hM
    have h₃ : |v (X s) * (deriv (deriv (dslope X s)) t * dslope X s t -
        deriv (dslope X s) t * deriv (dslope X s) t)| ≤ 2*M^3 := by
      rw [abs_mul]
      calc
        _ ≤ |v (X s)| *
            (|deriv (deriv (dslope X s)) t| * |dslope X s t| +
              |deriv (dslope X s) t| * |deriv (dslope X s) t|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using abs_sub_le
            (deriv (deriv (dslope X s)) t * dslope X s t) 0
            (deriv (dslope X s) t * deriv (dslope X s) t)
        _ ≤ M * (M*M + M*M) := mul_le_mul hv0
          (add_le_add (mul_le_mul hD2 hD0 (abs_nonneg _) hM)
            (mul_le_mul hD1 hD1 (abs_nonneg _) hM)) (by positivity) hM
        _ = _ := by ring
    have h₄ : |v (X s) * (deriv (deriv (dslope X s)) t * dslope X s t -
        deriv (dslope X s) t * deriv (dslope X s) t) / (dslope X s t)^2| ≤
        2*M^3/d^2 := by
      rw [abs_div, abs_pow]
      exact div_le_div₀ (by positivity) h₃ (sq_pos_of_pos hd)
        (pow_le_pow_left₀ hd.le hden 2)
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₄)

/-- A uniform bound for the concrete remainder from ordinary derivative
bounds and a lower bound for the divided difference of the coordinate map. -/
theorem amplitudeRemainder_variation {v X : ℝ → ℝ} {s M d : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hs : s ∈ Ioo 0 Real.pi) (hxs : X s ∈ Ioo (-1) 1)
    (hv : ∀ y ∈ Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ v y)
    (hX : ∀ t ∈ Icc 0 Real.pi, ContDiffAt ℝ ⊤ X t)
    (hmap : MapsTo X (Icc 0 Real.pi) (Icc (-1) 1))
    (hneg : ∀ t ∈ Icc 0 Real.pi, deriv X t ≤ 0)
    (hden : ∀ t ∈ Icc 0 Real.pi, dslope X s t ≤ -d)
    (hv0 : ∀ y ∈ Icc (-1 : ℝ) 1, |v y| ≤ M)
    (hv1 : ∀ y ∈ Icc (-1 : ℝ) 1, |deriv v y| ≤ M)
    (hv2 : ∀ y ∈ Icc (-1 : ℝ) 1, |iteratedDeriv 2 v y| ≤ M)
    (hX1 : ∀ t ∈ Icc 0 Real.pi, |deriv X t| ≤ M)
    (hX2 : ∀ t ∈ Icc 0 Real.pi, |iteratedDeriv 2 X t| ≤ M)
    (hX3 : ∀ t ∈ Icc 0 Real.pi, |iteratedDeriv 3 X t| ≤ M) :
    BoundedVariationOn (amplitudeRemainder v X s) (Icc 0 Real.pi) ∧
    IntervalIntegrable (amplitudeRemainder v X s) volume 0 Real.pi ∧
    (eVariationOn (amplitudeRemainder v X s) (Icc 0 Real.pi)).toReal ≤
      Real.pi * (M^3 + M^2 + 2*M^3/d^2) + 2*(M^2 + M^2/d) := by
  have hs' : s ∈ Icc 0 Real.pi := ⟨hs.1.le, hs.2.le⟩
  have hxs' : X s ∈ Icc (-1 : ℝ) 1 := ⟨hxs.1.le, hxs.2.le⟩
  have hDneg (t : ℝ) (ht : t ∈ Icc 0 Real.pi) : dslope X s t < 0 :=
    (hden t ht).trans_lt (neg_neg_of_pos hd)
  have hjet (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
      |regularRemainder v X s t| ≤ M^2 + M^2/d ∧
      |deriv (regularRemainder v X s) t| ≤ M^3 + M^2 + 2*M^3/d^2 := by
    apply regularRemainder_bounds (hv _ (hmap ht)) (hX t ht) hM hd
    · rw [abs_of_neg (hDneg t ht)]
      linarith [hden t ht]
    · exact hv0 _ hxs'
    · exact abs_dslope_le (fun y hy => (hv y hy).differentiableAt (by simp))
        hxs' (hmap ht) hv1
    · have hh := abs_deriv_dslope_le hv hxs (hmap ht) hv2
      linarith
    · exact hX1 t ht
    · simpa only [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
        iteratedDeriv_zero] using hX2 t ht
    · exact abs_dslope_le (fun t ht => (hX t ht).differentiableAt (by simp)) hs' ht hX1
    · have hh := abs_deriv_dslope_le hX hs ht hX2
      linarith
    · have hh := abs_second_deriv_dslope_le hX hs ht hX3
      linarith
  have hdiff (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
      DifferentiableAt ℝ (regularRemainder v X s) t :=
    (regularRemainder_hasDerivAt (hv _ (hmap ht)) (hX t ht) (hDneg t ht).ne).differentiableAt
  have heq : EqOn (amplitudeRemainder v X s)
      (fun t => jumpSign s t * regularRemainder v X s t) (Icc 0 Real.pi) := by
    intro t ht
    exact amplitudeRemainder_eq_jump_mul ((hX t ht).differentiableAt (by simp))
      (hneg t ht) (hDneg t ht)
  have hvar := variation_jump_mul_le hs (by positivity : 0 ≤ M^2 + M^2/d)
    (by positivity : 0 ≤ M^3 + M^2 + 2*M^3/d^2) hdiff
    (fun t ht => (hjet t ht).1) (fun t ht => (hjet t ht).2)
  rw [← eVariationOn.congr heq] at hvar
  have hfinite : eVariationOn (amplitudeRemainder v X s) (Icc 0 Real.pi) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  refine ⟨hfinite, ?_, ?_⟩
  · apply (jump_mul_intervalIntegrable (s := s) Real.pi_pos.le
      (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt)).congr
    intro t ht
    rw [uIoc_of_le Real.pi_pos.le] at ht
    exact (heq ⟨ht.1.le, ht.2⟩).symm
  · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
    have hbound0 : 0 ≤ (M^3 + M^2 + 2*M^3/d^2) * (Real.pi - 0) +
        2*(M^2 + M^2/d) := by simp only [sub_zero]; positivity
    rw [ENNReal.toReal_ofReal hbound0] at hh
    simpa only [sub_zero, mul_comm] using hh

end Erdos1132.Counterexample
