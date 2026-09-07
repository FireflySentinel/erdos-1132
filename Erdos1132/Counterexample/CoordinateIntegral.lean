import Erdos1132.Counterexample.CoordinateBounds
import Erdos1132.Counterexample.RemainderIntegral

/-!
# The explicit integral of the coordinate remainder

The endpoint terms give the logarithmic correction in the finite-part
integral identity of the amplitude lemma.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

theorem coordinate_endpoint_logs {X : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Ioo 0 Real.pi) (hxs : X s ∈ Ioo (-1) 1)
    (h0 : X 0 = 1) (hπ : X Real.pi = -1) :
    Real.log (dslope X s 0) + Real.log (dslope X s Real.pi) =
      Real.log (1 - (X s)^2) - Real.log (s*(Real.pi - s)) := by
  have hm : 0 < 1 - X s := sub_pos.mpr hxs.2
  have hp : 0 < 1 + X s := by linarith [hxs.1]
  have hps : 0 < Real.pi - s := sub_pos.mpr hs.2
  rw [dslope_of_ne _ hs.1.ne, dslope_of_ne _ hs.2.ne', slope_def_field,
    slope_def_field, h0, hπ]
  have hneg : -1 - X s = -(1 + X s) := by ring
  have hfac : 1 - (X s)^2 = (1 - X s)*(1 + X s) := by ring
  rw [zero_sub, hneg, Real.log_div hm.ne' (neg_ne_zero.mpr hs.1.ne'),
    Real.log_neg_eq_log, Real.log_div (neg_ne_zero.mpr hp.ne') hps.ne',
    Real.log_neg_eq_log, hfac, Real.log_mul hm.ne' hp.ne',
    Real.log_mul hs.1.ne' hps.ne']
  ring

theorem cosine_derivative_logs {θ q : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (hq : 0 < q) :
    Real.log (1 - (Real.cos θ)^2) - 2*Real.log (-Real.sin θ/q) = 2*Real.log q := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hid : 1 - (Real.cos θ)^2 = (Real.sin θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hid, Real.log_pow, Real.log_div (neg_ne_zero.mpr hs.ne') hq.ne', Real.log_neg_eq_log]
  norm_num
  ring

/-- The actual inverse-coordinate remainder has the finite-part integral
stated in the amplitude lemma. -/
theorem integral_phaseCoordinate_remainder {ψ v : ℝ → ℝ} {B ε s : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |ε| * B < 1)
    (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0)
    (hs : s ∈ Ioo 0 Real.pi)
    (hv : ∀ y ∈ Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ v y) :
    let X := fun t => phaseCoordinate ψ (ε, t)
    (∫ t in (0 : ℝ)..Real.pi, amplitudeRemainder v X s t) =
      -logarithmicOperator v (X s) + v (X s) *
        (2*Real.log (1 - ε*deriv ψ (phaseInverse ψ ε s)) - Real.log (s*(Real.pi - s))) := by
  dsimp only
  let X := fun t => phaseCoordinate ψ (ε, t)
  have hx0 : X 0 = 1 := by simp [X, phaseCoordinate, phaseInverse_endpoint hψ hder hε h0]
  have hxπ : X Real.pi = -1 := by simp [X, phaseCoordinate, phaseInverse_endpoint hψ hder hε hπ]
  have hXs : X s ∈ Ioo (-1) 1 := phaseCoordinate_mem_Ioo hψ hval hder hε h0 hπ hs
  have hXa : ∀ t : ℝ, ContDiffAt ℝ ⊤ X t := by
    intro t
    exact (phaseCoordinate_contDiffAt hψ hval hder hε).comp t
      (contDiffAt_const.prodMk contDiffAt_id)
  have hq (t : ℝ) : 0 < 1 - ε*deriv ψ (phaseInverse ψ ε t) := by
    have hh := (le_abs_self (ε * deriv ψ (phaseInverse ψ ε t))).trans
      ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hder _) (abs_nonneg _)))
    linarith
  have hθ : phaseInverse ψ ε s ∈ Ioo 0 Real.pi := by
    have hm := phaseInverse_strictMono hψ hval hder hε
    constructor
    · simpa only [phaseInverse_endpoint hψ hder hε h0] using hm hs.1
    · simpa only [phaseInverse_endpoint hψ hder hε hπ] using hm hs.2
  have hmono : StrictAntiOn X (Icc 0 Real.pi) := by
    intro t ht u hu htu
    exact Real.strictAntiOn_cos
      (phaseInverse_mem_Icc hψ hval hder hε h0 hπ ht)
      (phaseInverse_mem_Icc hψ hval hder hε h0 hπ hu)
      ((phaseInverse_strictMono hψ hval hder hε) htu)
  have hds (t : ℝ) (ht : t ∈ Icc 0 Real.pi) : dslope X s t < 0 := by
    rcases lt_trichotomy t s with hts | hts | hst
    · rw [dslope_of_ne _ hts.ne, slope_def_field]
      exact div_neg_of_pos_of_neg (sub_pos.mpr (hmono ht ⟨hs.1.le, hs.2.le⟩ hts))
        (sub_neg.mpr hts)
    · subst t
      rw [dslope_same, (phaseCoordinate_hasDerivAt hψ hval hder hε s).deriv]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (Real.sin_pos_of_mem_Ioo hθ)) (hq s)
    · rw [dslope_of_ne _ hst.ne', slope_def_field]
      exact div_neg_of_neg_of_pos (sub_neg.mpr (hmono ⟨hs.1.le, hs.2.le⟩ ht hst))
        (sub_pos.mpr hst)
  have hi := integral_amplitudeRemainder hs hv (fun t _ => hXa t)
    (fun t _ => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) hx0 hxπ
    (fun t ht => phaseCoordinate_deriv_nonpos hψ hval hder hε h0 hπ ht) hds
  change (∫ t in (0 : ℝ)..Real.pi, amplitudeRemainder v X s t) = _
  rw [hi, coordinate_endpoint_logs hs hXs hx0 hxπ]
  have hlog : Real.log (1 - (X s)^2) - 2*Real.log (deriv X s) =
      2*Real.log (1 - ε*deriv ψ (phaseInverse ψ ε s)) := by
    rw [(phaseCoordinate_hasDerivAt hψ hval hder hε s).deriv]
    exact cosine_derivative_logs hθ (hq s)
  change -logarithmicOperator v (X s) + v (X s) * _ =
    -logarithmicOperator v (X s) + v (X s) * _
  congr 1
  congr 1
  linarith

end Erdos1132.Counterexample
