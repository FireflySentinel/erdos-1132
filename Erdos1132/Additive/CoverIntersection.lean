import Erdos1132.Additive.ScaledCover

/-! # Intersections of high-value interval unions in two different rows

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset Real
open scoped BigOperators
namespace Erdos1132

theorem centeredCover_intersection_from_local_bound {ι : Type*}
    (s : Finset ι) (y : ι → ℝ) {r C L m : ℝ} (hr : 0 ≤ r) (T : Set ℝ)
    (hlocal : ∀ a b : ℝ, a ≤ b → volume.real (T ∩ Icc a b) ≤ C*((b-a)/L+1/(m*L))) :
    volume.real (centeredCover s y r ∩ T) ≤
      C*((2*r*(s.card:ℝ))/L+(s.card:ℝ)/(m*L)) := by
  have he : centeredCover s y r ∩ T = ⋃ i ∈ s, T ∩ Icc (y i-r) (y i+r) := by
    ext x
    simp only [centeredCover, Set.mem_inter_iff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨⟨i, hi, hx⟩, ht⟩
      exact ⟨i, hi, ht, hx⟩
    · rintro ⟨i, hi, ht, hx⟩
      exact ⟨⟨i, hi, hx⟩, ht⟩
  rw [he]
  have h1 := measureReal_biUnion_finset_le (μ := volume) s (fun i => T ∩ Icc (y i-r) (y i+r))
  have h2 := sum_le_sum (s := s) (fun i hi => hlocal (y i-r) (y i+r) (by linarith))
  have heq : (∑ i ∈ s, C*(((y i+r)-(y i-r))/L+1/(m*L))) =
      C*((2*r*(s.card:ℝ))/L+(s.card:ℝ)/(m*L)) := by
    simp_rw [show ∀ i : ι, (y i+r)-(y i-r) = 2*r by intro i; ring]
    simp only [sum_const, nsmul_eq_mul]
    ring
  exact h1.trans (h2.trans_eq heq)

theorem scaled_cover_intersection {n m : ℕ} (s : Finset (Fin n)) (y : Fin n → ℝ)
    {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) (hn : 0 < n) (hm : 0 < m)
    (hln : 0 < Real.log (n:ℝ)) (hlm : 0 < Real.log (m:ℝ)) (T : Set ℝ)
    (hlocal : ∀ a b : ℝ, a ≤ b → volume.real (T ∩ Icc a b) ≤
      C*((b-a)/Real.log m+1/((m:ℝ)*Real.log m))) :
    volume.real (centeredCover s y (β/((n:ℝ)*Real.log n)) ∩ T) ≤
      C*(2*β/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hsn : (s.card:ℝ) ≤ n := by
    exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_univ (s := s))
  have hh := centeredCover_intersection_from_local_bound s y
    (r := β/((n:ℝ)*Real.log n)) (by positivity) T hlocal
  have h1 := mul_le_mul_of_nonneg_left hsn (by positivity : 0 ≤ 2*(β/((n:ℝ)*Real.log n)))
  have h2 := div_le_div_of_nonneg_right h1 hlm.le
  have h3 := div_le_div_of_nonneg_right hsn (by positivity : 0 ≤ (m:ℝ)*Real.log m)
  have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hC
  have he : C*((2*(β/((n:ℝ)*Real.log n))*(n:ℝ))/Real.log m+(n:ℝ)/((m:ℝ)*Real.log m)) =
      C*(2*β/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m)) := by field_simp
  exact hh.trans (h4.trans_eq he)

end Erdos1132
