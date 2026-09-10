import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-! # Analytic cancellation of a simple pole

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Filter Complex Set
open scoped Topology
namespace Erdos1132

theorem analyticAt_dslope_same {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- Subtracting the principal part of a quotient at a simple zero leaves an
analytic divided difference. -/
theorem simple_pole_subtraction {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hg0 : g a = 0) (hg1 : deriv g a ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
      (fun z => f z/g z-(f a/deriv g a)/(z-a)) =ᶠ[𝓝[≠] a] H := by
  let q := fun z => f z/dslope g a z
  have hD := analyticAt_dslope_same hg
  have hD0 : dslope g a a ≠ 0 := by simpa only [dslope_same] using hg1
  have hq : AnalyticAt ℂ q a := hf.div hD hD0
  refine ⟨dslope q a, analyticAt_dslope_same hq, ?_⟩
  have hev : ∀ᶠ z in 𝓝 a, dslope g a z ≠ 0 := hD.continuousAt.eventually_ne hD0
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hza
  have hza' : z ≠ a := hza
  have hgz : g z = (z-a)*dslope g a z := by
    simpa only [smul_eq_mul] using (sub_smul_dslope_of_zero hg0 z).symm
  have hqa : q a = f a/deriv g a := by simp only [q, dslope_same]
  rw [dslope_of_ne _ hza', slope_def_field, hgz, ← hqa]
  dsimp only [q]
  field_simp

/-- A meromorphic function with a local analytic extension has an analytic
normal form there. -/
theorem analyticAt_normalForm_of_extension {g H : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hg : MeromorphicOn g U) (ha : a ∈ U) (hH : AnalyticAt ℂ H a)
    (heq : g =ᶠ[𝓝[≠] a] H) :
    AnalyticAt ℂ (toMeromorphicNFOn g U) a := by
  have hord : 0 ≤ meromorphicOrderAt g a :=
    (hg a ha).meromorphicOrderAt_nonneg_iff.mpr ⟨H, hH, heq⟩
  have hnf := (hg a ha).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hord
  exact hnf.congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hg ha).symm

theorem normalForm_eventuallyEq_of_analyticAt {g : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hg : MeromorphicOn g U) (ha : a ∈ U) (hga : AnalyticAt ℂ g a) :
    toMeromorphicNFOn g U =ᶠ[𝓝 a] g := by
  have he := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hg ha
  rw [toMeromorphicNFAt_eq_self.mpr hga.meromorphicNFAt] at he
  exact he

end Erdos1132
