import Erdos1132.Counterexample.AmplitudeUpperBound

/-!
# The amplitude lemma

A zero-free real polynomial supplies interior interpolation nodes in every
sufficiently large degree, with the stated Lebesgue-function upper bound on
any fixed compact interior interval.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set Filter Polynomial
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

/-- the amplitude lemma (companion §3) on a compact interval: the same row consists of all the simple
roots of the specified amplitude polynomial and satisfies the upper estimate. -/
theorem eventually_exists_amplitude_polynomial_rows (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) {l r : ℝ} (hl : -1 < l) (_hlr : l ≤ r) (hr : r < 1) :
    ∀ᶠ n : ℕ in atTop, h.natDegree < n ∧
      (amplitudePolynomial h n).natDegree = n ∧ ∃ Y : Nodes n,
      (∀ i, Y.point i ∈ Ioo (-1) 1) ∧
      (∀ x : ℝ, (amplitudePolynomial h n).eval x = 0 ↔ ∃ i, x = Y.point i) ∧
      (∀ i, (amplitudePolynomial h n).derivative.eval (Y.point i) ≠ 0) ∧
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
  obtain ⟨Y, hY, hroots, hformula⟩ := exists_phaseCoordinate_row h hzero hpos hn hψ hval hder hε h0 hπ
    (hid n hn) (amplitudeWeight_cos h)
  have hdegree := amplitudePolynomial_natDegree h hn hpos.ne'
  have hP : amplitudePolynomial h n ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hdegree
    omega
  have hfac := polynomial_eq_leadingCoeff_mul_nodal Y hdegree.le (fun i => (hroots i).1)
  refine ⟨hn, hdegree, Y, fun i => (hY i).2, ?_, fun i => (hroots i).2, ?_⟩
  · intro x
    rw [hfac, Polynomial.eval_mul, Polynomial.eval_C, mul_eq_zero]
    simp only [Polynomial.leadingCoeff_ne_zero.mpr hP, false_or]
    simp [Nodes.nodePolynomial, Lagrange.nodal, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff, sub_eq_zero]
  · intro x hx
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

/-- The amplitude lemma's upper estimate, with all rows constructed from `h`. -/
theorem eventually_exists_amplitude_upper_rows (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) {l r : ℝ} (hl : -1 < l) (hlr : l ≤ r) (hr : r < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ Y : Nodes n,
      (∀ i, Y.point i ∈ Ioo (-1) 1) ∧
      ∀ x ∈ Icc l r, Y.lebesgue x ≤ 2/Real.pi*Real.log n + 3 -
        logarithmicOperator (amplitudeWeight h) x/(Real.pi*amplitudeWeight h x) := by
  filter_upwards [eventually_exists_amplitude_polynomial_rows h hzero hpos hl hlr hr]
    with n hn
  obtain ⟨_, _, Y, hI, _, _, hupper⟩ := hn
  exact ⟨Y, hI, hupper⟩

/-- the amplitude lemma (companion §3) for any compact subset of the open interval, with the polynomial,
its complete simple root set, and the upper bound in one statement. -/
theorem amplitude_lemma (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, h.natDegree < n ∧
      (amplitudePolynomial h n).natDegree = n ∧ ∃ Y : Nodes n,
      (∀ i, Y.point i ∈ Ioo (-1) 1) ∧
      (∀ x : ℝ, (amplitudePolynomial h n).eval x = 0 ↔ ∃ i, x = Y.point i) ∧
      (∀ i, (amplitudePolynomial h n).derivative.eval (Y.point i) ≠ 0) ∧
      ∀ x ∈ K, Y.lebesgue x ≤ 2/Real.pi*Real.log n + 3 -
        logarithmicOperator (amplitudeWeight h) x/(Real.pi*amplitudeWeight h x) := by
  have hinterval : ∃ l r : ℝ, -1 < l ∧ l ≤ r ∧ r < 1 ∧ K ⊆ Icc l r := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by norm_num, le_rfl, by norm_num, empty_subset _⟩
    · have hl := hK.sInf_mem hne
      have hr := hK.sSup_mem hne
      refine ⟨sInf K, sSup K, (hKI hl).1, csInf_le hK.bddBelow hr, (hKI hr).2, ?_⟩
      intro x hx
      exact ⟨csInf_le hK.bddBelow hx, le_csSup hK.bddAbove hx⟩
  obtain ⟨l, r, hl, hlr, hr, hsub⟩ := hinterval
  filter_upwards [eventually_exists_amplitude_polynomial_rows h hzero hpos hl hlr hr]
    with n hn
  obtain ⟨hd, hd', Y, hI, hroots, hsimple, hupper⟩ := hn
  exact ⟨hd, hd', Y, hI, hroots, hsimple, fun x hx => hupper x (hsub hx)⟩

end Erdos1132.Counterexample
