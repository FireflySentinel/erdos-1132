import Erdos1132.Additive.PoissonPotential
import Erdos1132.Additive.PotentialNormalization

/-! # Explicit control of the interior contribution to the Poisson integral

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Finset Real
open scoped BigOperators
namespace Erdos1132

theorem poissonKernel_le_inv_height {h : ℝ} (hh : 0 < h) (t : ℝ) :
    poissonKernel h t ≤ 1/(Real.pi*h) := by
  unfold poissonKernel
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg t, Real.pi_pos]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

def nodeNeighborhood (δ : ℝ) : Set ℝ :=
  ⋃ i, Set.Ioo (X.point i-δ) (X.point i+δ)

theorem measurableSet_nodeNeighborhood (δ : ℝ) : MeasurableSet (X.nodeNeighborhood δ) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioo)

theorem mem_nodeNeighborhood {δ y : ℝ} :
    y ∈ X.nodeNeighborhood δ ↔ ∃ i, |y-X.point i| < δ := by
  simp only [nodeNeighborhood, Set.mem_iUnion, Set.mem_Ioo, abs_lt]
  constructor <;> rintro ⟨i, h1, h2⟩ <;> refine ⟨i, ?_, ?_⟩ <;> linarith

theorem nodeNeighborhood_subset {δ : ℝ} (hδ : δ ≤ 1) :
    X.nodeNeighborhood δ ⊆ Set.Icc (-2) 2 := by
  intro y hy
  obtain ⟨i, hi⟩ := X.mem_nodeNeighborhood.mp hy
  have ha := abs_lt.mp hi
  have hx := X.mem_interval i
  constructor <;> linarith [ha.1, ha.2, hx.1, hx.2]

theorem measureReal_nodeNeighborhood_le {δ : ℝ} (hδ : 0 ≤ δ) :
    volume.real (X.nodeNeighborhood δ) ≤ 2*n*δ := by
  have he (i : Fin n) : volume.real (Set.Ioo (X.point i-δ) (X.point i+δ)) = 2*δ := by
    simp [Measure.real, Real.volume_Ioo, show X.point i+δ-(X.point i-δ) = 2*δ by ring,
      hδ]
  have hb := measureReal_iUnion_fintype_le (μ := volume)
    (fun i => Set.Ioo (X.point i-δ) (X.point i+δ))
  simp_rw [he] at hb
  simpa [nodeNeighborhood, mul_comm, mul_left_comm, mul_assoc] using hb

theorem abs_potential_sub_le_away (hn : 0 < n) {y δ Λ : ℝ}
    (hy : y ∈ Set.Icc (-1) 1) (hδ : 0 < δ)
    (haway : y ∉ X.nodeNeighborhood δ) (hΛ : X.lebesgue y ≤ Λ) :
    |X.empiricalLogPotential y-X.potentialNormalization| ≤
      max (Real.log (2*Λ)) (-Real.log δ)/n := by
  have hdist : ∀ i, δ ≤ |y-X.point i| := by
    intro i
    by_contra he
    exact haway (X.mem_nodeNeighborhood.mpr ⟨i, lt_of_not_ge he⟩)
  have hneq : ∀ i, y ≠ X.point i := by
    intro i he
    have hd := hdist i
    rw [he, sub_self, abs_zero] at hd
    exact hδ.not_ge hd
  rw [X.empiricalLogPotential_eq_realLogPotential hneq]
  have hb := X.local_potential_bounds hn hy hδ hdist hΛ
  have hm1 := div_le_div_of_nonneg_right
    (le_max_left (Real.log (2*Λ)) (-Real.log δ)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hm2 := div_le_div_of_nonneg_right
    (le_max_right (Real.log (2*Λ)) (-Real.log δ)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [neg_div] at hm2
  apply abs_le.mpr
  constructor <;> linarith

/-- The contribution from the interpolation interval has an explicit error
bound. The exceptional set is the stated union of node neighborhoods. -/
theorem local_poisson_potential_bound (hn : 0 < n) {a b Λ δ h : ℝ}
    (hI : Set.Icc a b ⊆ Set.Icc (-1) 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : 0 < h) (hΛ : ∀ y ∈ Set.Icc a b, X.lebesgue y ≤ Λ) (x : ℝ)
    (hΛ1 : 1 ≤ Λ) :
    |∫ y in Set.Icc a b,
      poissonKernel h (y-x) * (X.empiricalLogPotential y-X.potentialNormalization)| ≤
      max (Real.log (2*Λ)) (-Real.log δ)/n +
        (Real.sqrt (2*n*δ*logSquareBound) + |X.potentialNormalization| *(2*n*δ)) /
          (Real.pi*h) := by
  let B := X.nodeNeighborhood δ
  let E := max (Real.log (2*Λ)) (-Real.log δ)/n
  let K := 1/(Real.pi*h)
  let f := fun y => |X.empiricalLogPotential y|+|X.potentialNormalization|
  have hE : 0 ≤ E := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact (Real.log_nonneg (by linarith : 1 ≤ 2*Λ)).trans (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB := X.measurableSet_nodeNeighborhood δ
  have hBs := X.nodeNeighborhood_subset hδ1
  have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hBs)
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have hf : IntegrableOn f B :=
    ((X.integrableOn_empiricalLogPotential (-2) 2).mono_set hBs).abs.add (integrable_const _)
  have hfi : Integrable (B.indicator f) := (integrable_indicator_iff hB).mpr hf
  have hw := (integrable_poissonKernel hh.le).comp_sub_right x
  have hpoint : ∀ y ∈ Set.Icc a b,
      |poissonKernel h (y-x) * (X.empiricalLogPotential y-X.potentialNormalization)| ≤
        E*poissonKernel h (y-x)+K*B.indicator f y := by
    intro y hy
    have hw0 := (poissonKernel_pos hh (y-x)).le
    rw [abs_mul, abs_of_nonneg hw0]
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB]
      have hab : |X.empiricalLogPotential y-X.potentialNormalization| ≤ f y :=
        abs_sub _ _
      have hf0 : 0 ≤ f y := add_nonneg (abs_nonneg _) (abs_nonneg _)
      have hb := mul_le_mul (poissonKernel_le_inv_height hh (y-x)) hab
        (abs_nonneg _) hK
      exact hb.trans (le_add_of_nonneg_left (mul_nonneg hE hw0))
    · rw [Set.indicator_of_notMem hyB, mul_zero, add_zero]
      simpa only [E, mul_comm] using mul_le_mul_of_nonneg_left
        (X.abs_potential_sub_le_away hn (hI hy) hδ hyB (hΛ y hy)) hw0
  have hweighted := X.integrable_poisson_potential_sub hh x X.potentialNormalization
  have hbound := setIntegral_mono_on hweighted.abs.integrableOn
    ((hw.const_mul E).add (hfi.const_mul K)).integrableOn measurableSet_Icc hpoint
  have hintw : (∫ y in Set.Icc a b, poissonKernel h (y-x)) ≤ 1 := by
    apply le_trans (setIntegral_le_integral hw (ae_of_all _ (fun y => (poissonKernel_pos hh _).le)))
    rw [integral_sub_right_eq_self, integral_poissonKernel hh]
  have hintf : (∫ y in Set.Icc a b, B.indicator f y) ≤ ∫ y in B, f y := by
    apply le_trans (setIntegral_le_integral hfi (ae_of_all _
      (fun y => Set.indicator_nonneg (fun y _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) y)))
    rw [integral_indicator hB]
  have hintB : (∫ y in B, f y) ≤
      Real.sqrt (2*n*δ*logSquareBound)+|X.potentialNormalization| *(2*n*δ) := by
    have hv := X.measureReal_nodeNeighborhood_le hδ.le
    have hs := (X.integral_abs_potential_small_set hn hBs).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hv logSquareBound_nonneg))
    dsimp [f]
    rw [integral_add (((X.integrableOn_empiricalLogPotential (-2) 2).mono_set hBs).abs)
      (integrable_const _), integral_const]
    simp only [measureReal_restrict_apply_univ, smul_eq_mul]
    change _ + volume.real B * |X.potentialNormalization| ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg X.potentialNormalization)]
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hw.const_mul E).integrableOn (hfi.const_mul K).integrableOn,
    integral_const_mul, integral_const_mul] at hbound
  have hfinal := (abs_integral_le_integral_abs (f := fun y =>
    poissonKernel h (y-x)*(X.empiricalLogPotential y-X.potentialNormalization))).trans hbound
  have h1 := mul_le_mul_of_nonneg_left hintw hE
  have h2 := mul_le_mul_of_nonneg_left (hintf.trans hintB) hK
  calc
    _ ≤ E*1 + K*(Real.sqrt (2*n*δ*logSquareBound) +
        |X.potentialNormalization| * (2*n*δ)) := hfinal.trans (add_le_add h1 h2)
    _ = _ := by dsimp [E, K]; ring

end Nodes
end Erdos1132
