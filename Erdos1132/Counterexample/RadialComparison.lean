import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Comparing decreasing radial integrals

Cumulative measure bounds on balls control integrals of decreasing radial
weights. The weight is held constant below the first controlled radius,
giving the boundary term used in the far-field estimate of Section 7.2.
-/

open MeasureTheory Set Filter

namespace Erdos1132.Counterexample

/-- Layer cake transfers a cumulative measure bound to a capped radial weight. -/
theorem integral_capped_radial_le
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (r : α → ℝ) {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hμ : ∀ᵐ y ∂μ, r y ≤ b) (hν : ∀ᵐ y ∂ν, r y ≤ b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hanti : StrictAntiOn f (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hiμ : Integrable (fun y => f (max a (r y))) μ)
    (hiν : Integrable (fun y => f (max a (r y))) ν)
    (hball : ∀ t ∈ Icc a b,
      μ {y | r y ≤ t} ≤ ENNReal.ofReal c * ν {y | r y ≤ t}) :
    (∫ y, f (max a (r y)) ∂μ) ≤ c * ∫ y, f (max a (r y)) ∂ν := by
  have hmax {y : α} (hy : r y ≤ b) : max a (r y) ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab hy⟩
  have hnμ : 0 ≤ᵐ[μ] fun y => f (max a (r y)) := hμ.mono fun y hy => hpos _ (hmax hy)
  have hnν : 0 ≤ᵐ[ν] fun y => f (max a (r y)) := hν.mono fun y hy => hpos _ (hmax hy)
  have hlevel (t : ℝ) :
      μ {y | t ≤ f (max a (r y))} ≤
        ENNReal.ofReal c * ν {y | t ≤ f (max a (r y))} := by
    by_cases hlow : t ≤ f b
    · have heq (σ : Measure α) (hσ : ∀ᵐ y ∂σ, r y ≤ b) :
          σ {y | t ≤ f (max a (r y))} = σ {y | r y ≤ b} := by
        apply measure_congr
        filter_upwards [hσ] with y hy
        have hval := hanti.antitoneOn (hmax hy) (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
          (max_le hab hy)
        change (t ≤ f (max a (r y))) = (r y ≤ b)
        exact propext (iff_of_true (hlow.trans hval) hy)
      rw [heq μ hμ, heq ν hν]
      exact hball b ⟨hab, le_rfl⟩
    · by_cases hhigh : f a < t
      · have hempty : μ {y | t ≤ f (max a (r y))} = 0 := by
          calc
            μ {y | t ≤ f (max a (r y))} = μ ∅ := by
              apply measure_congr
              filter_upwards [hμ] with y hy
              have hval := hanti.antitoneOn (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
                (hmax hy) (le_max_left _ _)
              change (t ≤ f (max a (r y))) = False
              exact propext (iff_false_intro (not_le.mpr (hval.trans_lt hhigh)))
            _ = 0 := measure_empty
        rw [hempty]
        exact bot_le
      · obtain ⟨z, hz, hzt⟩ := intermediate_value_Icc' hab hf
          (show t ∈ Icc (f b) (f a) from ⟨le_of_not_ge hlow, le_of_not_gt hhigh⟩)
        have heq (σ : Measure α) (hσ : ∀ᵐ y ∂σ, r y ≤ b) :
            σ {y | t ≤ f (max a (r y))} = σ {y | r y ≤ z} := by
          apply measure_congr
          filter_upwards [hσ] with y hy
          change (t ≤ f (max a (r y))) = (r y ≤ z)
          apply propext
          rw [← hzt]
          rw [hanti.le_iff_ge hz (hmax hy), max_le_iff]
          exact and_iff_right hz.1
        rw [heq μ hμ, heq ν hν]
        exact hball z hz
  have hlin : (∫⁻ y, ENNReal.ofReal (f (max a (r y))) ∂μ) ≤
      ENNReal.ofReal c * ∫⁻ y, ENNReal.ofReal (f (max a (r y))) ∂ν := by
    rw [lintegral_eq_lintegral_meas_le μ hnμ hiμ.aemeasurable,
      lintegral_eq_lintegral_meas_le ν hnν hiν.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono hlevel
  rw [← ofReal_integral_eq_lintegral_ofReal hiμ hnμ,
    ← ofReal_integral_eq_lintegral_ofReal hiν hnν,
    ← ENNReal.ofReal_mul hc] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hc (integral_nonneg_of_ae hnν))).mp hlin

/-- The far-field comparison, with the boundary term at the first controlled radius. -/
theorem integral_radial_tail_le
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (r : α → ℝ) (hr : Measurable r) {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hμ : ∀ᵐ y ∂μ, r y ≤ b) (hν : ∀ᵐ y ∂ν, r y ≤ b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hanti : StrictAntiOn f (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hiμ : Integrable (fun y => f (max a (r y))) μ)
    (hiν : Integrable (fun y => f (max a (r y))) ν)
    (hball : ∀ t ∈ Icc a b,
      μ {y | r y ≤ t} ≤ ENNReal.ofReal c * ν {y | r y ≤ t}) :
    (∫ y in {y | a ≤ r y}, f (r y) ∂μ) ≤
      c * (f a * ν.real {y | r y ≤ a} + ∫ y in {y | a < r y}, f (r y) ∂ν) := by
  have hnonneg : 0 ≤ᵐ[μ] fun y => f (max a (r y)) := by
    filter_upwards [hμ] with y hy
    exact hpos _ ⟨le_max_left _ _, max_le hab hy⟩
  have htail : (∫ y in {y | a ≤ r y}, f (r y) ∂μ) =
      ∫ y in {y | a ≤ r y}, f (max a (r y)) ∂μ := by
    apply setIntegral_congr_fun (measurableSet_le measurable_const hr)
    intro y hy
    change a ≤ r y at hy
    change f (r y) = f (max a (r y))
    rw [max_eq_right hy]
  have hsplit : (∫ y, f (max a (r y)) ∂ν) =
      f a * ν.real {y | r y ≤ a} + ∫ y in {y | a < r y}, f (r y) ∂ν := by
    rw [← integral_add_compl (s := {y | r y ≤ a})
      (measurableSet_le hr measurable_const) hiν]
    have heq : {y | r y ≤ a}ᶜ = {y | a < r y} := by ext y; simp
    rw [heq]
    congr 1
    · calc
        (∫ y in {y | r y ≤ a}, f (max a (r y)) ∂ν) =
            ∫ y in {y | r y ≤ a}, f a ∂ν := by
          apply setIntegral_congr_fun (measurableSet_le hr measurable_const)
          intro y hy
          change r y ≤ a at hy
          change f (max a (r y)) = f a
          rw [max_eq_left hy]
        _ = f a * ν.real {y | r y ≤ a} := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    · apply setIntegral_congr_fun (measurableSet_lt measurable_const hr)
      intro y hy
      change a < r y at hy
      change f (max a (r y)) = f (r y)
      rw [max_eq_right (le_of_lt hy)]
  rw [htail]
  calc
    _ ≤ ∫ y, f (max a (r y)) ∂μ := setIntegral_le_integral hiμ hnonneg
    _ ≤ c * ∫ y, f (max a (r y)) ∂ν :=
      integral_capped_radial_le μ ν r hab hc hμ hν hf hanti hpos hiμ hiν hball
    _ = _ := by rw [hsplit]

end Erdos1132.Counterexample
