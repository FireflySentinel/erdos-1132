import Erdos1132.Additive.FinitePoles

/-! # A finite residue formula for the differentiated Cauchy kernel

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Filter Complex Set Finset Metric
open scoped Topology BigOperators
namespace Erdos1132

theorem circleIntegrable_inv_sub {R : ℝ} {a : ℂ} (hR : 0 < R) (ha : ‖a‖ < R) :
    CircleIntegrable (fun z => (z-a)⁻¹) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply (continuousOn_id.sub continuousOn_const).inv₀
  intro z hz
  change z-a ≠ 0
  apply sub_ne_zero.mpr
  intro he
  have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
  rw [he] at hn
  exact ha.ne hn

theorem circleIntegrable_inv_sq {R : ℝ} (hR : 0 < R) :
    CircleIntegrable (fun z : ℂ => 1/z^2) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply continuousOn_const.div (continuousOn_id.pow 2)
  intro z hz
  have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
  change z^2 ≠ 0
  exact pow_ne_zero _ (by intro he; simp [he] at hn; linarith)

theorem circleIntegral_inv_sq (R : ℝ) : (∮ z in C(0, R), (1/z^2 : ℂ)) = 0 := by
  simpa only [sub_zero, zpow_neg, zpow_natCast, one_div] using!
    circleIntegral.integral_sub_zpow_of_ne (by norm_num : (-2 : ℤ) ≠ -1) 0 0 R

/-- The two residues of this rational kernel cancel. -/
theorem circleIntegral_simplePole_div_sq {R : ℝ} {a : ℂ} (hR : 0 < R)
    (ha : ‖a‖ < R) (ha0 : a ≠ 0) :
    (∮ z in C(0, R), 1/((z-a)*z^2)) = 0 := by
  have hi1 := circleIntegrable_inv_sub hR ha
  have hi0 := circleIntegrable_inv_sub hR (by simpa using hR : ‖(0 : ℂ)‖ < R)
  simp only [sub_zero] at hi0
  have hi2 := circleIntegrable_inv_sq hR
  have hid : ∀ z ∈ sphere (0 : ℂ) R,
      1/((z-a)*z^2) = (1/a^2)*((z-a)⁻¹-z⁻¹)-(1/a)*(1/z^2) := by
    intro z hz
    have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hn; linarith
    have hza : z-a ≠ 0 := sub_ne_zero.mpr (fun he => ha.ne (he ▸ hn))
    field_simp
    ring
  have hiA : CircleIntegrable (fun z => (1/a^2)*((z-a)⁻¹-z⁻¹)) 0 R := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using! (hi1.sub hi0).const_smul (a := (1/a^2))
  have hiB : CircleIntegrable (fun z => (1/a)*(1/z^2)) 0 R := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hi2.const_smul (a := (1/a))
  rw [circleIntegral.integral_congr hR.le hid,
    circleIntegral.integral_sub hiA hiB,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub hi1 hi0,
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa [mem_ball, dist_eq_norm] using ha)]
  have he0 := circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := 0)
    (R := R) (by simpa using hR)
  simp only [sub_zero] at he0
  rw [he0, circleIntegral_inv_sq]
  ring

/-- The finite residue identity used in the local differentiation formula. -/
theorem finite_residue_derivative_formula {f g : ℂ → ℂ} {S : Finset ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hR : 0 < R) (hS : (0 : ℂ) ∉ S)
    (hinside : ∀ a ∈ S, ‖a‖ < R)
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, g z = 0 ↔ z ∈ S)
    (hsimple : ∀ a ∈ S, deriv g a ≠ 0) (hg0 : g 0 = 1) (hg'0 : deriv g 0 = 0) :
    (∮ z in C(0, R), f z/(g z*z^2)) = (2*Real.pi*I)*
      (deriv f 0+∑ a ∈ S, (f a/deriv g a)/a^2) := by
  let H := quotientRegularPart f g S
  let r := fun a => f a/deriv g a
  have hH := analyticOnNhd_quotientRegularPart hf hg hzero hsimple
  have hHD : DifferentiableOn ℂ H (closedBall 0 R) := hH.differentiableOn
  have hC := hHD.deriv_eq_smul_circleIntegral hR
  have hzdata (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ∉ S ∧ g z ≠ 0 ∧ z ≠ 0 := by
    have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
    have hnS : z ∉ S := fun he => (hinside z he).ne hn
    refine ⟨hnS, fun he => hnS ((hzero z (sphere_subset_closedBall hz)).mp he), ?_⟩
    intro he
    simp [he] at hn
    linarith
  have hpoint : ∀ z ∈ sphere (0 : ℂ) R,
      f z/(g z*z^2) = (1/z^2)*H z + ∑ a ∈ S, r a*(1/((z-a)*z^2)) := by
    intro z hz
    have hd := hzdata z hz
    have he := (quotientRegularPart_eventuallyEq hf hg hd.1 hd.2.1).eq_of_nhds
    change H z = f z/g z-principalParts S r z at he
    rw [he, principalParts, mul_sub, Finset.mul_sum]
    have heq : (∑ a ∈ S, r a*(1/((z-a)*z^2))) = (∑ a ∈ S, (1/z^2)*(r a/(z-a))) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    field_simp
    ring
  have hiH : CircleIntegrable (fun z => (1/z^2)*H z) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply (continuousOn_const.div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero _ (hzdata z hz).2.2)).mul
      (hH.continuousOn.mono sphere_subset_closedBall)
  have hip (a : ℂ) (ha : a ∈ S) : CircleIntegrable (fun z => r a*(1/((z-a)*z^2))) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply continuousOn_const.mul
    apply continuousOn_const.div (by fun_prop)
    intro z hz
    apply mul_ne_zero _ (pow_ne_zero _ (hzdata z hz).2.2)
    exact sub_ne_zero.mpr (fun he => (hzdata z hz).1 (he ▸ ha))
  rw [circleIntegral.integral_congr hR.le hpoint,
    circleIntegral.integral_add hiH (CircleIntegrable.fun_sum S hip),
    circleIntegral.integral_fun_sum hip]
  have hs : (∑ a ∈ S, ∮ z in C(0, R), r a*(1/((z-a)*z^2))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [circleIntegral.integral_const_mul,
      circleIntegral_simplePole_div_sq hR (hinside a ha) (fun he => hS (he ▸ ha)), mul_zero]
  rw [hs, add_zero]
  simp only [sub_zero, smul_eq_mul] at hC
  rw [hC, deriv_quotientRegularPart_zero hf hg hS hg0 hg'0]

end Erdos1132
