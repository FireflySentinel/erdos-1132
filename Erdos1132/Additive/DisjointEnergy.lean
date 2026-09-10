import Erdos1132.Additive.RieszEnergy

/-! # Energy expansion on a disjoint union of two finite measure spaces

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory
namespace Erdos1132

def disjointMeasure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) : Measure (α ⊕ β) :=
  Measure.map Sum.inl μ + Measure.map Sum.inr ν

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (disjointMeasure μ ν) := by unfold disjointMeasure; infer_instance

theorem integral_disjoint_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {H : (α ⊕ β) × (α ⊕ β) → ℝ} (hH : Measurable H)
    {C : ℝ} (hbound : ∀ p, ‖H p‖ ≤ C) :
    (∫ p, H p ∂(disjointMeasure μ ν).prod (disjointMeasure μ ν)) =
      (∫ p : α × α, H (Sum.inl p.1, Sum.inl p.2) ∂μ.prod μ) +
      (∫ p : α × β, H (Sum.inl p.1, Sum.inr p.2) ∂μ.prod ν) +
      (∫ p : β × α, H (Sum.inr p.1, Sum.inl p.2) ∂ν.prod μ) +
      (∫ p : β × β, H (Sum.inr p.1, Sum.inr p.2) ∂ν.prod ν) := by
  have hi (τ : Measure ((α ⊕ β) × (α ⊕ β))) [IsFiniteMeasure τ] : Integrable H τ :=
    (integrable_const C).mono' hH.aestronglyMeasurable (ae_of_all _ hbound)
  unfold disjointMeasure
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add,
    integral_add_measure (hi _) (hi _),
    integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _)]
  simp_rw [Measure.map_prod_map _ _ measurable_inl measurable_inl,
    Measure.map_prod_map _ _ measurable_inl measurable_inr,
    Measure.map_prod_map _ _ measurable_inr measurable_inl,
    Measure.map_prod_map _ _ measurable_inr measurable_inr,
    integral_map_of_stronglyMeasurable (measurable_inl.prodMap measurable_inl) hH.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_inl.prodMap measurable_inr) hH.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_inr.prodMap measurable_inl) hH.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_inr.prodMap measurable_inr) hH.stronglyMeasurable]
  simp only [add_assoc]
  rfl

/-- Positivity applied to the difference of two bounded weighted measures. -/
theorem riesz_energy_comparison {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {x a : α → ℝ} {y b : β → ℝ} (hx : Measurable x) (ha : Measurable a)
    (hy : Measurable y) (hb : Measurable b) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hxb : ∀ u, |x u| ≤ 1) (hyb : ∀ v, |y v| ≤ 1)
    (hab : ∀ u, |a u| ≤ B) (hbb : ∀ v, |b v| ≤ B) :
    2*(∫ p : α × β, a p.1*b p.2*rieszKernel ε (x p.1-y p.2) ∂μ.prod ν) -
        (∫ p : β × β, b p.1*b p.2*rieszKernel ε (y p.1-y p.2) ∂ν.prod ν) ≤
      ∫ p : α × α, a p.1*a p.2*rieszKernel ε (x p.1-x p.2) ∂μ.prod μ := by
  let X := Sum.elim x y
  let W := Sum.elim a (fun v => -b v)
  have hX : Measurable X := hx.sumElim hy
  have hW : Measurable W := ha.sumElim hb.neg
  have hXb (u : α ⊕ β) : |X u| ≤ 1 := by cases u with
    | inl u => exact hxb u
    | inr v => exact hyb v
  have hWb (u : α ⊕ β) : |W u| ≤ B := by cases u with
    | inl u => exact hab u
    | inr v => simpa [W] using hbb v
  let H (p : (α ⊕ β) × (α ⊕ β)) := W p.1*W p.2*rieszKernel ε (X p.1-X p.2)
  have hHm : Measurable H := by
    exact ((hW.comp measurable_fst).mul (hW.comp measurable_snd)).mul
      ((continuous_rieszKernel hε).measurable.comp
        ((hX.comp measurable_fst).sub (hX.comp measurable_snd)))
  have hHb (p : (α ⊕ β) × (α ⊕ β)) : ‖H p‖ ≤ B^2/ε := by
    dsimp [H]
    rw [abs_mul, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
    calc
      _ ≤ B^2*(1/ε) := mul_le_mul
        (by simpa only [pow_two] using mul_le_mul (hWb p.1) (hWb p.2) (abs_nonneg _) hB)
        (rieszKernel_le_diagonal hε _) (rieszKernel_pos hε _).le (sq_nonneg B)
      _ = _ := by ring
  have hp := riesz_energy_nonneg (disjointMeasure μ ν) hX hW hB hε hXb hWb
  change 0 ≤ ∫ p, H p ∂(disjointMeasure μ ν).prod (disjointMeasure μ ν) at hp
  rw [integral_disjoint_product μ ν hHm hHb] at hp
  dsimp [H, W, X] at hp
  simp only [mul_neg, neg_mul, neg_neg, integral_neg] at hp
  have hswap : (∫ p : β × α, b p.1*a p.2*rieszKernel ε (y p.1-x p.2) ∂ν.prod μ) =
      ∫ p : α × β, a p.1*b p.2*rieszKernel ε (x p.1-y p.2) ∂μ.prod ν := by
    rw [← integral_prod_swap]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by
      dsimp
      rw [show y p.2-x p.1 = -(x p.1-y p.2) by ring, rieszKernel_even]
      ring)
  rw [hswap] at hp
  linarith

end Erdos1132
