import Erdos1132.InterpolantSecondDerivative
import Erdos1132.PeakArithmetic

/-! # A large interpolation derivative forces a nearby high Lebesgue value -/

noncomputable section
open Real Complex Set Filter
open scoped Topology
namespace Erdos1132

theorem eventually_interpolant_peak (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n)
    (D : ℝ) :
    ∃ K > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ v : Fin n → ℝ,
      (∀ i, |v i| ≤ 1) →
      a*Real.log n-D ≤ |((X n).interpolant v).derivative.eval x|/
        (Real.pi*n*(X n).exteriorDensity l r (X n).potentialNormalization x 0) →
      ∃ y ∈ Icc (l+d) (r-d), |y-x| ≤ K/n ∧ a*Real.log n-K ≤ (X n).lebesgue y := by
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hXn : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c, hc, hdensity⟩ := eventually_exterior_density_positive X hlr hI
    (by linarith : 0 < 2*d) hXn
  let K : ℝ := |b|+(Real.pi^2/4)*(|b+D|+3)+1/c+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hratio : Tendsto (fun n : ℕ => logarithmicLevel a b n/(c*eighthRoot n)) atTop (𝓝 0) := by
    have ht := (tendsto_log_affine_div_eighthRoot a b).div_const c
    simp only [zero_div] at ht
    convert ht using 1
    funext n
    dsimp [logarithmicLevel]
    ring
  have hrem := (tendsto_level_exp_loss_div_root_sq hlr a b).const_mul 32
  simp only [mul_zero] at hrem
  have hmove : Tendsto (fun n : ℕ => (1/c)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop (1/c)
  filter_upwards [hupper, hlevels, hXn, hdensity, eventually_interpolant_local_growth hlr hI hd,
    eventually_riesz_radius (l := l) (r := r) hc,
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (tendsto_level_mul_exp_loss_sub_one hlr a b).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hrem.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), hmove.eventually (gt_mem_nhds hd)]
    with n hu hl hn hdens hgrow hrad hratio hsmall hrem hmove
  intro x hx v hv hderiv
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  let A := logarithmicLevel a b n
  let E := Real.exp (localRectangleLoss l r n)
  let M := A*E
  let t := eighthRoot (n : ℝ)
  let ω := localFrequency (X n) l r x
  let Q := |((X n).interpolant v).derivative.eval x|
  have hρ : c ≤ ρ := hdens x hx
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hl.1
  have ht : 0 < t := eighthRoot_pos hnR
  have hA : 0 < A := zero_lt_one.trans_le hl.2.1
  have hE : 0 < E := Real.exp_pos _
  have hM : 0 < M := mul_pos hA hE
  obtain ⟨hm, hω, hr, hh, herr⟩ := hrad (X n) x hρ
  have hg := hgrow (X n) hn A hl.2.1 hu x hx hρ0.le v hv
  have hq : A-|b+D| ≤ Q/(Real.pi*n*ρ) := by
    dsimp [A, Q, ρ, logarithmicLevel]
    linarith [le_abs_self (b+D)]
  have hscale := frequency_ratio_lower hc hρ ht hA.le (abs_nonneg (b+D)) hq
  have hscaleid : Q/(Real.pi*n*ρ)*(ρ/(ρ+1/t)) = Q/ω := by
    have hden : ρ+1/t ≠ 0 := by positivity
    dsimp [ω, localFrequency]
    change Q/(Real.pi*n*ρ)*(ρ/(ρ+1/t)) = Q/(Real.pi*n*(ρ+1/t))
    field_simp
  rw [hscaleid] at hscale
  have hQ : A-|b+D|-1 ≤ Q/ω := by
    change A/(c*t) < 1 at hratio
    linarith
  have hMA : A ≤ M := by
    have he := Real.one_le_exp_iff.mpr (localRectangleLoss_nonneg hlr n)
    have hh := mul_le_mul_of_nonneg_left he hA.le
    simpa only [mul_one] using hh
  have hM1 : M ≤ A+1 := by
    change A*(E-1) < 1 at hsmall
    dsimp [M]
    nlinarith
  have heM : M*(16/((localRieszIndex n : ℝ)*Real.pi)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left herr hM.le
    change 32*(A*E/t^2) < 1 at hrem
    calc
      _ ≤ M*(32/t^2) := hh
      _ = 32*(A*E/t^2) := by dsimp [M]; ring
      _ ≤ 1 := hrem.le
  have hp := polynomial_local_peak_abs hm hω hM hr hh hg
    (δ := 1-Q/(ω*M)) (by change 1-(1-Q/(ω*M)) ≤ Q/(ω*M); linarith)
  have hpeak := (peak_deficit_bound hM hω hMA hM1 hQ heM).trans hp
  let y := x+Real.pi/(2*ω)
  have hωlow : Real.pi*c*n ≤ ω := by
    have ht' := mul_le_mul_of_nonneg_left
      (show c ≤ ρ+1/t by linarith [one_div_pos.mpr ht])
      (show 0 ≤ Real.pi*(n : ℝ) by positivity)
    dsimp [ω, localFrequency]
    nlinarith
  have hshift0 : 0 ≤ Real.pi/(2*ω) := by positivity
  have hshift : Real.pi/(2*ω) ≤ (1/c)/(n : ℝ) := by
    have hid : (1/c)/(n : ℝ) = 1/(c*n) := by ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*ω) (mul_pos hc hnR)).mpr
    nlinarith
  have hy : y ∈ Icc (l+d) (r-d) := by
    dsimp [y]
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨y, hy, ?_, ?_⟩
  · have he : |y-x| = Real.pi/(2*ω) := by dsimp [y]; rw [add_sub_cancel_left, abs_of_nonneg hshift0]
    rw [he]
    apply hshift.trans
    apply div_le_div_of_nonneg_right _ hnR.le
    dsimp [K]
    have hb : 0 ≤ (Real.pi^2/4)*(|b+D|+3) := by positivity
    linarith [abs_nonneg b]
  · have hh := (X n).interpolant_eval_le v hv y
    have hle : a*Real.log n-K ≤ A-(Real.pi^2/4)*(|b+D|+3) := by
      dsimp [A, K, logarithmicLevel]
      linarith [neg_le_abs b, one_div_pos.mpr hc]
    exact hle.trans (hpeak.trans hh)

end Erdos1132
