import Erdos1132.UniformLowSet
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos1132

def eventualLowSet (X : ∀ n, Nodes (n + 2)) (c : ℝ) (N : ℕ) : Set ℝ :=
  Icc (-1) 1 ∩ {x | ∀ n, N ≤ n → (X n).lebesgue x ≤ c * Real.log (rowSize n)}

theorem measurable_eventualLowSet (X : ∀ n, Nodes (n + 2)) (c : ℝ) (N : ℕ) :
    MeasurableSet (eventualLowSet X c N) := by
  apply measurableSet_Icc.inter
  rw [show {x | ∀ n, N ≤ n → (X n).lebesgue x ≤ c * Real.log (rowSize n)} =
      ⋂ n : ℕ, {x | N ≤ n → (X n).lebesgue x ≤ c * Real.log (rowSize n)} by ext; simp]
  apply MeasurableSet.iInter
  intro n
  by_cases hn : N ≤ n
  · simpa only [hn, true_implies] using measurableSet_le (X n).measurable_lebesgue measurable_const
  · simp only [hn, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

theorem eventualLowSet_null (X : ∀ n, Nodes (n + 2)) {c : ℝ}
    (hc : 0 < c) (hcπ : c < 2 / Real.pi) (N : ℕ) : volume (eventualLowSet X c N) = 0 := by
  apply uniform_low_set_null X hc hcπ (measurable_eventualLowSet X c N) inter_subset_left
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  exact hx.2 n hn

theorem ae_frequently_lower_bound_pos (X : ∀ n, Nodes (n + 2)) {c : ℝ}
    (hc : 0 < c) (hcπ : c < 2 / Real.pi) :
    ∀ᵐ x : ℝ, x ∈ Icc (-1) 1 → ∃ᶠ n in atTop, c * Real.log (rowSize n) < (X n).lebesgue x := by
  have he : ∀ᵐ x : ℝ, ∀ N, x ∉ eventualLowSet X c N := by
    apply ae_all_iff.mpr
    intro N
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using eventualLowSet_null X hc hcπ N
  filter_upwards [he] with x hx hxI
  by_contra hn
  rw [not_frequently] at hn
  have hn' : ∀ᶠ n in atTop, (X n).lebesgue x ≤ c * Real.log (rowSize n) := by
    simpa only [not_lt] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hn'
  exact hx N ⟨hxI, hN⟩

/-- Every coefficient below `2 / π` is exceeded infinitely often at almost every interior point. -/
theorem ae_frequently_lower_bound (X : ∀ n, Nodes (n + 2)) :
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1), ∀ c < 2 / Real.pi,
      ∃ᶠ n in atTop, c * Real.log (rowSize n) < (X n).lebesgue x := by
  have hr : ∀ r : ℚ, ∀ᵐ x : ℝ, x ∈ Icc (-1) 1 →
      0 < (r : ℝ) → (r : ℝ) < 2 / Real.pi →
        ∃ᶠ n in atTop, (r : ℝ) * Real.log (rowSize n) < (X n).lebesgue x := by
    intro r
    by_cases hr0 : 0 < (r : ℝ)
    · by_cases hrπ : (r : ℝ) < 2 / Real.pi
      · filter_upwards [ae_frequently_lower_bound_pos X hr0 hrπ] with x hx hxI _ _
        exact hx hxI
      · exact ae_of_all _ fun _ _ _ h => (hrπ h).elim
    · exact ae_of_all _ fun _ _ h _ => (hr0 h).elim
  have hr' := ae_all_iff.mpr hr
  filter_upwards [ae_restrict_of_ae hr', ae_restrict_mem measurableSet_Ioo] with x hx hxI
  intro c hc
  obtain ⟨r, hcr, hrπ⟩ := exists_rat_btwn (show max c 0 < 2 / Real.pi from
    max_lt hc (by positivity))
  have hr0 : 0 < (r : ℝ) := (le_max_right c 0).trans_lt hcr
  have hcr' : c < (r : ℝ) := (le_max_left c 0).trans_lt hcr
  apply (hx r ⟨hxI.1.le, hxI.2.le⟩ hr0 hrπ).mono
  intro n hn
  exact (mul_lt_mul_of_pos_right hcr' (log_rowSize_pos n)).trans hn

/-- The almost-everywhere assertion of Theorem 1(ii), with the limsup in the extended reals. -/
theorem ae_lebesgue_limsup_shifted (X : ∀ n, Nodes (n + 2)) :
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1),
      ((2 / Real.pi : ℝ) : EReal) ≤
        limsup (fun n => (((X n).lebesgue x / Real.log (rowSize n) : ℝ) : EReal)) atTop := by
  filter_upwards [ae_frequently_lower_bound X] with x hx
  apply (le_limsup_iff).mpr
  intro y hy
  obtain ⟨r, hyr, hr⟩ := EReal.exists_rat_btwn_of_lt hy
  apply (hx (r : ℝ) (EReal.coe_lt_coe_iff.mp hr)).mono
  intro n hn
  exact hyr.trans (EReal.coe_lt_coe_iff.mpr ((lt_div_iff₀ (log_rowSize_pos n)).mpr hn))

/-- Theorem 1(ii): the sharp almost-everywhere lower bound for an arbitrary triangular array. -/
theorem ae_lebesgue_limsup (X : ∀ n, Nodes n) :
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1),
      ((2 / Real.pi : ℝ) : EReal) ≤
        limsup (fun n => (((X n).lebesgue x / Real.log (n : ℝ) : ℝ) : EReal)) atTop := by
  filter_upwards [ae_lebesgue_limsup_shifted (fun n => X (n + 2))] with x hx
  rw [← limsup_nat_add (fun n => (((X n).lebesgue x / Real.log (n : ℝ) : ℝ) : EReal)) 2]
  simpa only [rowSize, Nat.cast_add, Nat.cast_ofNat] using hx

end Erdos1132
