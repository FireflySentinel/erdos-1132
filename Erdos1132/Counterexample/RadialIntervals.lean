import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Splitting a radial integral on the interpolation interval into its two sides -/

open MeasureTheory Set

namespace Erdos1132.Counterexample

def intervalRadialTail (x a : ℝ) : Set ℝ := Icc (-1) 1 ∩ {y | a ≤ |x - y|}

theorem intervalRadialTail_eq {x a : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (ha : 0 < a) :
    intervalRadialTail x a = Icc (-1) (x - a) ∪ Icc (x + a) 1 := by
  ext y
  simp only [intervalRadialTail, mem_inter_iff, mem_Icc, mem_ofPred_eq, le_abs, mem_union]
  constructor
  · rintro ⟨⟨hl, hu⟩, h | h⟩
    · exact Or.inl ⟨hl, by linarith⟩
    · exact Or.inr ⟨by linarith, hu⟩
  · rintro (⟨hl, hu⟩ | ⟨hl, hu⟩)
    · exact ⟨⟨hl, by linarith [hx.2]⟩, Or.inl (by linarith)⟩
    · exact ⟨⟨by linarith [hx.1], hu⟩, Or.inr (by linarith)⟩

theorem radial_left_integral {f : ℝ → ℝ} {x a : ℝ} (ha : 0 < a) :
    (∫ y in Icc (-1 : ℝ) (x - a), f |x - y|) =
      ∫ t in a..max a (1 + x), f t := by
  by_cases hlen : a ≤ 1 + x
  · rw [max_eq_right hlen]
    calc
      _ = ∫ y in Icc (-1 : ℝ) (x - a), f (x - y) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy
        dsimp
        rw [abs_of_pos (by linarith [hy.2])]
      _ = ∫ y in (-1 : ℝ)..(x - a), f (x - y) := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left f x]
        simp only [sub_sub_cancel, sub_neg_eq_add]
        congr 1; ring
  · rw [max_eq_left (le_of_not_ge hlen), intervalIntegral.integral_same,
      Icc_eq_empty_of_lt (by linarith)]
    simp

theorem radial_right_integral {f : ℝ → ℝ} {x a : ℝ} (ha : 0 < a) :
    (∫ y in Icc (x + a) (1 : ℝ), f |x - y|) =
      ∫ t in a..max a (1 - x), f t := by
  by_cases hlen : a ≤ 1 - x
  · rw [max_eq_right hlen]
    calc
      _ = ∫ y in Icc (x + a) (1 : ℝ), f (y - x) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy
        dsimp
        rw [abs_of_neg (by linarith [hy.1])]
        congr 1
        ring
      _ = ∫ y in (x + a)..(1 : ℝ), f (y - x) := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right f x]
        simp
  · rw [max_eq_left (le_of_not_ge hlen), intervalIntegral.integral_same,
      Icc_eq_empty_of_lt (by linarith)]
    simp

/-- The exact two-sided radial integration formula. -/
theorem integral_intervalRadialTail {f : ℝ → ℝ} {x a : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (ha : 0 < a)
    (hf : ContinuousOn f (Icc a 2)) :
    (∫ y in intervalRadialTail x a, f |x - y|) =
      (∫ t in a..max a (1 + x), f t) + ∫ t in a..max a (1 - x), f t := by
  have hleft : IntegrableOn (fun y => f |x - y|) (Icc (-1 : ℝ) (x - a)) := by
    apply ContinuousOn.integrableOn_Icc
    apply hf.comp (continuous_const.sub continuous_id).abs.continuousOn
    intro y hy
    change |x - y| ∈ Icc a 2
    rw [abs_of_pos (by linarith [hy.2])]
    exact ⟨by linarith [hy.2], by linarith [hy.1, hx.2]⟩
  have hright : IntegrableOn (fun y => f |x - y|) (Icc (x + a) (1 : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    apply hf.comp (continuous_const.sub continuous_id).abs.continuousOn
    intro y hy
    change |x - y| ∈ Icc a 2
    rw [abs_of_neg (by linarith [hy.1])]
    exact ⟨by linarith [hy.1], by linarith [hy.2, hx.1]⟩
  have hd : Disjoint (Icc (-1 : ℝ) (x - a)) (Icc (x + a) 1) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    linarith [hy.2, hz.1]
  rw [intervalRadialTail_eq hx ha, setIntegral_union hd measurableSet_Icc hleft hright,
    radial_left_integral ha, radial_right_integral ha]

theorem integrableOn_intervalRadialTail {f : ℝ → ℝ} {x a : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hf : ContinuousOn f (Icc a 2)) :
    IntegrableOn (fun y => f |x - y|) (intervalRadialTail x a) := by
  have hcompact : IsCompact (intervalRadialTail x a) := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_const.sub continuous_id).abs)
  apply ContinuousOn.integrableOn_compact hcompact
  apply hf.comp (continuous_const.sub continuous_id).abs.continuousOn
  intro y hy
  change |x - y| ∈ Icc a 2
  refine ⟨hy.2, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith [hx.1, hx.2, hy.1.1, hy.1.2]

/-- One-sided integral comparisons combine on the interpolation interval. -/
theorem integral_intervalRadialTail_le {f g : ℝ → ℝ} {x a C : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (ha : 0 < a) (ha2 : a ≤ 2)
    (hf : ContinuousOn f (Icc a 2)) (hg : ContinuousOn g (Icc a 2))
    (hav : ∀ b ∈ Icc a 2, (∫ t in a..b, f t) ≤ C * ∫ t in a..b, g t) :
    (∫ y in intervalRadialTail x a, f |x - y|) ≤
      C * ∫ y in intervalRadialTail x a, g |x - y| := by
  rw [integral_intervalRadialTail hx ha hf, integral_intervalRadialTail hx ha hg]
  have hl := hav (max a (1 + x)) ⟨le_max_left _ _, max_le ha2 (by linarith [hx.2])⟩
  have hr := hav (max a (1 - x)) ⟨le_max_left _ _, max_le ha2 (by linarith [hx.1])⟩
  linarith

end Erdos1132.Counterexample
