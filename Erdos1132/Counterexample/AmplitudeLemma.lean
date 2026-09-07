import Erdos1132.Counterexample.AmplitudeUpperBound

/-!
# The amplitude lemma

A zero-free real polynomial supplies interior interpolation nodes in every
sufficiently large degree, with the stated Lebesgue-function upper bound on
any fixed compact interior interval.
-/

noncomputable section

open Set Filter Polynomial
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

/-- Lemma 9, with the amplitude defined by its positive polynomial square.
The node rows and all analytic estimates are constructed from `h`. -/
theorem eventually_exists_amplitude_upper_rows (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) {l r : ℝ} (hl : -1 < l) (_hlr : l ≤ r) (hr : r < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ Y : Nodes n,
      (∀ i, Y.point i ∈ Ioo (-1) 1) ∧
      ∀ x ∈ Icc l r, Y.lebesgue x ≤ 2/Real.pi*Real.log n + 3 -
        logarithmicOperator (amplitudeWeight h) x/(Real.pi*amplitudeWeight h x) := by
  obtain ⟨ψ, hψ, h0, hπ, _, hid, B, hB, hbound⟩ := exists_bounded_amplitude_phase h hzero hpos
  have hval : ∀ t, |ψ t| ≤ B := fun t => (hbound t).1
  have hder : ∀ t, |deriv ψ t| ≤ B := fun t => (hbound t).2
  let a := min (Real.arccos r) (Real.pi-Real.arccos l)/2
  have hrθ : 0 < Real.arccos r := Real.arccos_pos.mpr hr
  have hlθ : 0 < Real.pi-Real.arccos l := sub_pos.mpr (Real.arccos_lt_pi.mpr hl)
  have ha : 0 < a := div_pos (lt_min hrθ hlθ) (by norm_num)
  have ha₁ : 2*a ≤ Real.arccos r := by dsimp [a]; linarith [min_le_left (Real.arccos r) (Real.pi-Real.arccos l)]
  have ha₂ : 2*a ≤ Real.pi-Real.arccos l := by dsimp [a]; linarith [min_le_right (Real.arccos r) (Real.pi-Real.arccos l)]
  have haπ : a ≤ Real.pi-a := by linarith [Real.arccos_le_pi r]
  have hv : ∀ y ∈ Icc (-1 : ℝ) 1, ContDiffAt ℝ ⊤ (amplitudeWeight h) y :=
    fun _ hy => amplitudeWeight_contDiffAt h hzero hy
  have hvpos : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < amplitudeWeight h y :=
    fun _ hy => amplitudeWeight_pos h hzero hy
  have hupper := eventually_coordinate_row_upper hB hψ hval hder h0 hπ hv hvpos ha haπ
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, |(n : ℝ)⁻¹| * B < min 1 a := by
    have hh : ∀ᶠ ε : ℝ in 𝓝 0, |ε| * B < min 1 a :=
      (continuous_abs.mul continuous_const).continuousAt.eventually_lt_const
        (by simpa using lt_min zero_lt_one ha)
    exact hinv.eventually hh
  filter_upwards [hupper, hsmall, eventually_gt_atTop h.natDegree] with n hupper hsmall hn
  have hε : |(n : ℝ)⁻¹| * B < 1 := hsmall.trans_le (min_le_left _ _)
  have hεa : |(n : ℝ)⁻¹| * B ≤ a := (hsmall.trans_le (min_le_right _ _)).le
  obtain ⟨Y, hY, hformula⟩ := exists_phaseCoordinate_row h hzero hpos hn hψ hval hder hε h0 hπ
    (hid n hn) (amplitudeWeight_cos h)
  refine ⟨Y, fun i => (hY i).2, ?_⟩
  intro x hx
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨(hl.trans_le hx.1).le, (hx.2.trans_lt hr).le⟩
  let θ := Real.arccos x
  let s := phaseMap ψ (n : ℝ)⁻¹ θ
  have hθlo : Real.arccos r ≤ θ := Real.arccos_le_arccos hx.2
  have hθhi : θ ≤ Real.arccos l := Real.arccos_le_arccos hx.1
  have hψsmall : |(n : ℝ)⁻¹ * ψ θ| ≤ a := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hval θ) (abs_nonneg _)).trans hεa
  have hs : s ∈ Icc a (Real.pi-a) := by
    dsimp [s, phaseMap]
    have hh := abs_le.mp hψsmall
    constructor <;> linarith
  have hX : phaseCoordinate ψ ((n : ℝ)⁻¹, s) = x := by
    rw [phaseCoordinate, show s = phaseMap ψ (n : ℝ)⁻¹ θ from rfl,
      phaseInverse_left (hψ.differentiable (by simp)) hder hε]
    exact Real.cos_arccos hxI.1 hxI.2
  have hh := hupper Y (fun i => (hY i).1) hformula s hs
  dsimp only at hh
  simpa only [hX] using hh

end Erdos1132.Counterexample
