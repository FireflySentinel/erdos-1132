import Erdos1132.KernelConcentration

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos1132

theorem tendsto_poissonKernel_tail {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, poissonKernel (height a n) t) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg fun t => (poissonKernel_pos (height_pos a n) t).le)
    (fun n => poissonKernel_tail_bound (height_pos a n) hδ)
  simpa using ((tendsto_height ha).const_mul 2).div_const (Real.pi * δ)

theorem translated_poisson_tail {h R : ℝ} (hh : 0 < h) (hR : 0 < R) (x : ℝ) :
    (∫ y in (Icc (x - R * h) (x + R * h))ᶜ, poissonKernel h (x - y)) ≤ 2 / (Real.pi * R) := by
  have he := integral_sub_left_eq_self
    ((Icc (-(R * h)) (R * h))ᶜ.indicator (poissonKernel h)) volume x
  rw [integral_indicator measurableSet_Icc.compl] at he
  have he' : (∫ y in (Icc (x - R * h) (x + R * h))ᶜ, poissonKernel h (x - y)) =
      ∫ t in (Icc (-(R * h)) (R * h))ᶜ, poissonKernel h t := by
    rw [← he, ← integral_indicator measurableSet_Icc.compl]
    apply integral_congr_ae
    filter_upwards with y
    have hmem : y ∈ Icc (x - R * h) (x + R * h) ↔ x - y ∈ Icc (-(R * h)) (R * h) := by
      constructor <;> intro hy <;> constructor <;> linarith [hy.1, hy.2]
    simp only [Set.indicator, Set.mem_compl_iff, ← hmem]

  rw [he']
  have hb := poissonKernel_tail_bound hh (mul_pos hR hh)
  convert! hb using 1
  field_simp

theorem exists_localization_radius {q : ℝ} (hq : 0 < q) :
    ∃ R > 0, 2 / (Real.pi * R) < q / 4 := by
  refine ⟨1 + 8 / (Real.pi * q), by positivity, ?_⟩
  apply (div_lt_iff₀ (show 0 < Real.pi * (1 + 8 / (Real.pi * q)) by positivity)).mpr
  field_simp
  nlinarith [Real.pi_pos]

end Erdos1132
