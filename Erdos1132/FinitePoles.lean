import Erdos1132.SimplePole

/-! # Removal of finitely many simple poles from an analytic quotient -/

noncomputable section
open Filter Complex Set Finset Metric
open scoped Topology BigOperators
namespace Erdos1132

def principalParts (S : Finset ℂ) (r : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ a ∈ S, r a/(z-a)

def quotientRegularPart (f g : ℂ → ℂ) (S : Finset ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => f z/g z-principalParts S (fun a => f a/deriv g a) z) Set.univ

theorem analyticAt_principalParts {S : Finset ℂ} {r : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) :
    AnalyticAt ℂ (principalParts S r) z := by
  apply Finset.analyticAt_fun_sum
  intro a ha
  apply analyticAt_const.div (analyticAt_id.sub analyticAt_const)
  change z-a ≠ 0
  exact sub_ne_zero.mpr (fun he => hz (he.symm ▸ ha))

theorem meromorphic_principalParts (S : Finset ℂ) (r : ℂ → ℂ) (z : ℂ) :
    MeromorphicAt (principalParts S r) z := by
  apply MeromorphicAt.fun_sum
  intro a _
  exact MeromorphicAt.div (by fun_prop) (by fun_prop)

theorem meromorphic_quotient_sub_principalParts {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ) (S : Finset ℂ) :
    MeromorphicOn (fun z => f z/g z-principalParts S (fun a => f a/deriv g a) z) Set.univ := by
  intro z _
  exact ((hf z trivial).meromorphicAt.div (hg z trivial).meromorphicAt).sub
    (meromorphic_principalParts S _ z)

theorem quotientRegularPart_eventuallyEq {f g : ℂ → ℂ} {S : Finset ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hz : z ∉ S) (hgz : g z ≠ 0) :
    quotientRegularPart f g S =ᶠ[𝓝 z]
      (fun w => f w/g w-principalParts S (fun a => f a/deriv g a) w) := by
  apply normalForm_eventuallyEq_of_analyticAt
    (meromorphic_quotient_sub_principalParts hf hg S) (Set.mem_univ z)
  exact ((hf z trivial).div (hg z trivial) hgz).sub (analyticAt_principalParts hz)

/-- At a listed simple zero, the regular part is the analytic divided difference
of the local quotient, minus the other principal parts. -/
theorem analyticAt_quotientRegularPart_of_mem {f g : ℂ → ℂ} {S : Finset ℂ} {a : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ha : a ∈ S) (hga : g a = 0) (hg'a : deriv g a ≠ 0) :
    AnalyticAt ℂ (quotientRegularPart f g S) a := by
  obtain ⟨H, hH, heq⟩ := simple_pole_subtraction (hf a trivial) (hg a trivial) hga hg'a
  let r := fun a => f a/deriv g a
  have hother : AnalyticAt ℂ (principalParts (S.erase a) r) a :=
    analyticAt_principalParts (Finset.notMem_erase a S)
  apply analyticAt_normalForm_of_extension
    (meromorphic_quotient_sub_principalParts hf hg S) (Set.mem_univ a)
    (hH.sub hother)
  filter_upwards [heq] with z hz
  have hsum : principalParts S r z = r a/(z-a)+principalParts (S.erase a) r z := by
    unfold principalParts
    exact (Finset.add_sum_erase S (fun b => r b/(z-b)) ha).symm
  change f z/g z-principalParts S r z = H z-principalParts (S.erase a) r z
  rw [hsum]
  dsimp [r]
  rw [← hz]
  ring

theorem analyticOnNhd_quotientRegularPart {f g : ℂ → ℂ} {S : Finset ℂ} {V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hzero : ∀ z ∈ V, g z = 0 ↔ z ∈ S)
    (hsimple : ∀ a ∈ S, deriv g a ≠ 0) :
    AnalyticOnNhd ℂ (quotientRegularPart f g S) V := by
  intro z hz
  by_cases hS : z ∈ S
  · exact analyticAt_quotientRegularPart_of_mem hf hg hS ((hzero z hz).mpr hS) (hsimple z hS)
  · have hgz : g z ≠ 0 := fun he => hS ((hzero z hz).mp he)
    have ha := ((hf z trivial).div (hg z trivial) hgz).sub (analyticAt_principalParts (r := fun a => f a/deriv g a) hS)
    exact ha.congr (quotientRegularPart_eventuallyEq hf hg hS hgz).symm

theorem hasDerivAt_principalParts {S : Finset ℂ} {r : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) :
    HasDerivAt (principalParts S r) (∑ a ∈ S, -(r a/(z-a)^2)) z := by
  apply HasDerivAt.fun_sum
  intro a ha
  have hza : z-a ≠ 0 := sub_ne_zero.mpr (fun he => hz (he ▸ ha))
  convert! (hasDerivAt_const z (r a)).div ((hasDerivAt_id z).sub_const a) hza using 1
  simp only [id_eq, mul_one, zero_mul, zero_sub, neg_div]

theorem deriv_quotientRegularPart_zero {f g : ℂ → ℂ} {S : Finset ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hS : (0 : ℂ) ∉ S) (hg0 : g 0 = 1) (hg'0 : deriv g 0 = 0) :
    deriv (quotientRegularPart f g S) 0 = deriv f 0 +
      ∑ a ∈ S, (f a/deriv g a)/a^2 := by
  have hq := (hf 0 trivial).differentiableAt.hasDerivAt.div
    (hg 0 trivial).differentiableAt.hasDerivAt (by simp [hg0])
  have hp := hasDerivAt_principalParts (r := fun a => f a/deriv g a) hS
  have he := quotientRegularPart_eventuallyEq hf hg hS (by simp [hg0])
  have h := (hq.sub hp).congr_of_eventuallyEq he
  rw [h.deriv]
  simp [hg0, hg'0, Finset.sum_neg_distrib]

end Erdos1132
