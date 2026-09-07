import Erdos1132.Additive.InterpolantDerivative
import Erdos1132.Additive.PolynomialSecondDerivative

/-! # A uniform second derivative bound for bounded-data interpolants

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open Real Complex Set Filter
open scoped Topology
namespace Erdos1132

theorem eventually_interpolant_second_derivative (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ v : Fin n → ℝ,
      (∀ i, |v i| ≤ 1) →
      |((X n).interpolant v).derivative.derivative.eval x| ≤ C*(n : ℝ)^2*Real.log n := by
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hXn : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c, hc, hdensity⟩ := eventually_exterior_density_positive X hlr hI
    (by linarith : 0 < 2*d) hXn
  obtain ⟨D, hD, hDbound⟩ := uniform_exterior_density_bounds hlr hI (by linarith : 0 < 2*d)
  let K : ℝ := a+|b|+1
  let C : ℝ := 2*Real.exp 1*Real.exp 1*(Real.pi*(D+1))^2*K
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hloss := (tendsto_localRectangleLoss l r).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hupper, hlevels, hXn, hdensity, eventually_interpolant_local_growth hlr hI hd,
    eventually_riesz_radius (l := l) (r := r) hc, hloss, hlog,
    tendsto_eighthRoot.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hu hl hn hdens hgrow hrad hloss hlog ht
  change 1 ≤ Real.log (n : ℝ) at hlog
  intro x hx v hv
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  let A := logarithmicLevel a b n
  let E := Real.exp (localRectangleLoss l r n)
  let t := eighthRoot (n : ℝ)
  let ω := localFrequency (X n) l r x
  have hρ : c ≤ ρ := hdens x hx
  have hA : 0 < A := zero_lt_one.trans_le hl.2.1
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨hm, hω, hr, hh, herr⟩ := hrad (X n) x hρ
  have hR : 1 ≤ (localRieszIndex n : ℝ)*Real.pi := by
    have hmR : (1 : ℝ) ≤ localRieszIndex n := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three]
  have hr' : 1/ω ≤ (1/t^2)/2 := by apply (div_le_iff₀ hω).mpr; nlinarith
  have hh' : 1/ω ≤ 1/t^4 := by apply (div_le_iff₀ hω).mpr; nlinarith
  have hg := hgrow (X n) hn A hl.2.1 hu x hx (hc.le.trans hρ) v hv
  have hbound := polynomial_second_derivative_bound hω (mul_pos hA hE).le hr' hh' hg
  have hDb := (abs_le.mp ((hDbound n (X n) hl.1 hn).1 x hx)).2
  have hωD : ω ≤ (Real.pi*(D+1))*(n : ℝ) := by
    have hinv : 1/t ≤ 1 := (div_le_one (by linarith : 0 < t)).mpr ht
    have hp := mul_le_mul_of_nonneg_left (show ρ+1/t ≤ D+1 by linarith)
      (show 0 ≤ Real.pi*(n : ℝ) by positivity)
    exact hp.trans_eq (by ring)
  have hE1 : E ≤ Real.exp 1 := Real.exp_le_exp.mpr hloss.le
  have hAK : A ≤ K*Real.log n := by
    have hb := le_abs_self b
    have hm := mul_le_mul_of_nonneg_left hlog (abs_nonneg b)
    dsimp [A, K, logarithmicLevel]
    nlinarith
  have hstep : 2*(A*E)*Real.exp 1*ω^2 ≤
      2*((K*Real.log n)*Real.exp 1)*Real.exp 1*((Real.pi*(D+1))*(n : ℝ))^2 := by
    gcongr
  exact hbound.trans (hstep.trans_eq (by dsimp [C]; ring))

end Erdos1132
