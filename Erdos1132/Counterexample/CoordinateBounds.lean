import Erdos1132.Counterexample.SmoothCoordinates
import Erdos1132.Counterexample.DividedDifferences
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform nonvanishing of coordinate divided differences

Cosine has negative extended slopes on compact interior angle sets. Uniform
convergence of first derivatives transfers this bound to the perturbed coordinates.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

theorem dslope_cos_eq (s t : ℝ) :
    dslope Real.cos s t = -Real.sin ((s + t)/2) * Real.sinc ((t - s)/2) := by
  by_cases hts : t = s
  · subst t
    simp [dslope_same, Real.deriv_cos]
  · rw [dslope_of_ne _ hts, slope_def_field, Real.cos_sub_cos,
      Real.sinc_of_ne_zero (div_ne_zero (sub_ne_zero.mpr hts) (by norm_num))]
    rw [add_comm s t]
    field_simp

theorem continuous_dslope_cos : Continuous (fun p : ℝ × ℝ => dslope Real.cos p.1 p.2) := by
  simp_rw [dslope_cos_eq]
  fun_prop

theorem dslope_cos_neg {s t : ℝ} (hs : s ∈ Ioo 0 Real.pi) (ht : t ∈ Icc 0 Real.pi) :
    dslope Real.cos s t < 0 := by
  rcases lt_trichotomy t s with hts | rfl | hst
  · rw [dslope_of_ne _ hts.ne, slope_def_field]
    exact div_neg_of_pos_of_neg
      (sub_pos.mpr (Real.strictAntiOn_cos ht ⟨hs.1.le, hs.2.le⟩ hts)) (sub_neg.mpr hts)
  · simpa [dslope_same, Real.deriv_cos] using neg_neg_of_pos (Real.sin_pos_of_mem_Ioo hs)
  · rw [dslope_of_ne _ hst.ne', slope_def_field]
    exact div_neg_of_neg_of_pos
      (sub_neg.mpr (Real.strictAntiOn_cos ⟨hs.1.le, hs.2.le⟩ ht hst)) (sub_pos.mpr hst)

theorem exists_uniform_cos_slope_bound {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi) :
    ∃ d : ℝ, 0 < d ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc 0 Real.pi,
      dslope Real.cos s t ≤ -2*d := by
  have hne : ((Icc a b) ×ˢ (Icc 0 Real.pi)).Nonempty :=
    ⟨(a, 0), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, Real.pi_pos.le⟩⟩⟩
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn hne
    continuous_dslope_cos.continuousOn
  have hpneg := dslope_cos_neg ⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb⟩ hp.2
  refine ⟨-dslope Real.cos p.1 p.2 / 2, div_pos (neg_pos.mpr hpneg) (by norm_num), ?_⟩
  intro s hs t ht
  have hh := hmax (show (s, t) ∈ (Icc a b) ×ˢ (Icc 0 Real.pi) from ⟨hs, ht⟩)
  dsimp at hh ⊢
  linarith

theorem abs_dslope_sub_le {X : ℝ → ℝ} {s t ε : ℝ}
    (hX : ∀ u ∈ Icc 0 Real.pi, DifferentiableAt ℝ X u)
    (hs : s ∈ Icc 0 Real.pi) (ht : t ∈ Icc 0 Real.pi)
    (hε : ∀ u ∈ Icc 0 Real.pi, |deriv X u - deriv Real.cos u| ≤ ε) :
    |dslope X s t - dslope Real.cos s t| ≤ ε := by
  have hh : dslope (fun u => X u - Real.cos u) s t =
      dslope X s t - dslope Real.cos s t := by
    by_cases hts : t = s
    · subst t
      rw [dslope_same, dslope_same, dslope_same]
      exact ((hX s hs).hasDerivAt.sub Real.differentiable_cos.differentiableAt.hasDerivAt).deriv
    · rw [dslope_of_ne _ hts, dslope_of_ne _ hts, dslope_of_ne _ hts]
      simp only [slope_def_field]
      ring
  rw [← hh]
  apply abs_dslope_le (fun u hu => (hX u hu).sub Real.differentiable_cos.differentiableAt) hs ht
  intro u hu
  rw [((hX u hu).hasDerivAt.sub Real.differentiable_cos.differentiableAt.hasDerivAt).deriv]
  exact hε u hu

theorem eventually_uniform_coordinate_slope_bound {ψ : ℝ → ℝ} {B a b : ℝ}
    (hB : 0 < B) (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ s ∈ Icc a b, ∀ t ∈ Icc 0 Real.pi,
        dslope (fun u => phaseCoordinate ψ (ε, u)) s t ≤ -d := by
  obtain ⟨d, hd, hcos⟩ := exists_uniform_cos_slope_bound ha hab hb
  refine ⟨d, hd, ?_⟩
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    (phaseCoordinate_derivatives_tendstoUniformlyOn hB hψ hval hder 1) d hd
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, |ε| * B < 1 :=
    (continuous_abs.mul continuous_const).continuousAt.eventually_lt_const (by simp)
  filter_upwards [hclose, hsmall] with ε hε hεB
  intro s hs t ht
  have hX : ∀ u ∈ Icc 0 Real.pi,
      DifferentiableAt ℝ (fun u => phaseCoordinate ψ (ε, u)) u := by
    intro u _
    exact (phaseCoordinate_hasDerivAt hψ hval hder hεB u).differentiableAt
  have hc : ∀ u ∈ Icc 0 Real.pi,
      |deriv (fun u => phaseCoordinate ψ (ε, u)) u - deriv Real.cos u| ≤ d := by
    intro u hu
    simpa only [iteratedDeriv_one, Real.dist_eq, abs_sub_comm] using (hε u hu).le
  have hds := abs_dslope_sub_le hX
    ⟨(ha.trans_le hs.1).le, (hs.2.trans_lt hb).le⟩ ht hc
  have hh := (abs_le.mp hds).2
  linarith [hcos s hs t ht]


theorem eventually_uniform_coordinate_derivative_bound {ψ : ℝ → ℝ} {B : ℝ}
    (hB : 0 < B) (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (k : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ t ∈ Icc 0 Real.pi,
      |iteratedDeriv k (fun u => phaseCoordinate ψ (ε, u)) t| ≤ 2 := by
  have hh := Metric.tendstoUniformlyOn_iff.mp
    (phaseCoordinate_derivatives_tendstoUniformlyOn hB hψ hval hder k) 1 zero_lt_one
  filter_upwards [hh] with ε hε t ht
  have hclose : |iteratedDeriv k (fun u => phaseCoordinate ψ (ε, u)) t -
      iteratedDeriv k Real.cos t| ≤ 1 := by
    simpa only [Real.dist_eq, abs_sub_comm] using (hε t ht).le
  have htri := abs_add_le
    (iteratedDeriv k (fun u => phaseCoordinate ψ (ε, u)) t - iteratedDeriv k Real.cos t)
    (iteratedDeriv k Real.cos t)
  rw [sub_add_cancel] at htri
  linarith [Real.abs_iteratedDeriv_cos_le_one k t]

theorem phaseCoordinate_mem_Ioo {ψ : ℝ → ℝ} {B ε s : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |ε| * B < 1)
    (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0) (hs : s ∈ Ioo 0 Real.pi) :
    phaseCoordinate ψ (ε, s) ∈ Ioo (-1) 1 := by
  have hm := phaseInverse_strictMono hψ hval hder hε
  have hz : 0 < phaseInverse ψ ε s := by
    simpa only [phaseInverse_endpoint hψ hder hε h0] using hm hs.1
  have hp : phaseInverse ψ ε s < Real.pi := by
    simpa only [phaseInverse_endpoint hψ hder hε hπ] using hm hs.2
  constructor
  · have hh := Real.strictAntiOn_cos ⟨hz.le, hp.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hp
    simpa only [Real.cos_pi, phaseCoordinate] using hh
  · have hh := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hz.le, hp.le⟩ hz
    simpa only [Real.cos_zero, phaseCoordinate] using hh

theorem phaseCoordinate_deriv_nonpos {ψ : ℝ → ℝ} {B ε t : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |ε| * B < 1)
    (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0) (ht : t ∈ Icc 0 Real.pi) :
    deriv (fun u => phaseCoordinate ψ (ε, u)) t ≤ 0 := by
  rw [(phaseCoordinate_hasDerivAt hψ hval hder hε t).deriv]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (Real.sin_nonneg_of_mem_Icc
      (phaseInverse_mem_Icc hψ hval hder hε h0 hπ ht))
  · have hh := (le_abs_self (ε * deriv ψ (phaseInverse ψ ε t))).trans
      ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hder _) (abs_nonneg _)))
    linarith

theorem contDiffAt_iteratedDeriv {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ ⊤ f x) (k : ℕ) : ContDiffAt ℝ ⊤ (iteratedDeriv k f) x := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k hk =>
    rw [iteratedDeriv_succ]
    exact hk.derivWithin (by simp)

theorem exists_uniform_analytic_jet_bound {v : ℝ → ℝ}
    (hv : ∀ y ∈ Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ v y) (k : ℕ) :
    ∃ M : ℝ, 2 ≤ M ∧ ∀ j ≤ k, ∀ y ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv j v y| ≤ M := by
  have hh (j : ℕ) : ∃ M : ℝ, ∀ y ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv j v y| ≤ M := by
    have hc : ContinuousOn (fun y => |iteratedDeriv j v y|) (Icc (-1 : ℝ) 1) := by
      intro y hy
      exact (contDiffAt_iteratedDeriv (hv y hy) j).continuousAt.abs.continuousWithinAt
    obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
    exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
  induction k with
  | zero =>
    obtain ⟨M, hM⟩ := hh 0
    refine ⟨max 2 M, le_max_left _ _, ?_⟩
    intro j hj y hy
    have : j = 0 := by omega
    subst j
    exact (hM y hy).trans (le_max_right _ _)
  | succ k hk =>
    obtain ⟨M, hM2, hM⟩ := hk
    obtain ⟨D, hD⟩ := hh (k + 1)
    refine ⟨max M D, hM2.trans (le_max_left _ _), ?_⟩
    intro j hj y hy
    rcases Nat.le_succ_iff.mp hj with hj | rfl
    · exact (hM j hj y hy).trans (le_max_left _ _)
    · exact (hD y hy).trans (le_max_right _ _)

end Erdos1132.Counterexample
