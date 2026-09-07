import Erdos1132.Additive.ExteriorDensity

/-! # The local complex-potential expansion with an explicit remainder

Paper: §2, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Real
namespace Erdos1132.Nodes
variable {n : ℕ} (X : Nodes n)

theorem poisson_exterior_decomposition (hn : 0 < n) {a b d x h : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1)
    (hh : 0 < h) (α : ℝ) :
    X.complexLogPotential x h = α - Real.pi*h*X.exteriorDensity a b α x h +
      ∫ y in Icc a b, poissonKernel h (y-x)*(X.empiricalLogPotential y-α) := by
  have hi := X.integrable_poisson_potential_sub hh x α
  have he := integral_add_compl (s := Icc a b) measurableSet_Icc hi
  have hout := (X.exterior_density_integrable_and_bound hn hd hx hx1 α h).1
  have hex : (∫ y in (Icc a b)ᶜ, poissonKernel h (y-x)*(X.empiricalLogPotential y-α)) =
      -Real.pi*h*X.exteriorDensity a b α x h := by
    unfold exteriorDensity
    have heq (y : ℝ) : poissonKernel h (y-x)*(X.empiricalLogPotential y-α) =
        (h/Real.pi)*((X.empiricalLogPotential y-α)/((y-x)^2+h^2)) := by
      unfold poissonKernel
      rw [div_mul_eq_div_div]
      ring
    simp_rw [heq]
    rw [integral_const_mul]
    field_simp
  rw [hex] at he
  rw [X.poisson_potential_sub hh x α]
  linarith

/-- The density is its real-axis exterior integral. All error terms are explicit. -/
theorem complex_potential_expansion (hn : 0 < n) {a b d x h δ Λ : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1)
    (hI : Icc a b ⊆ Icc (-1) 1) (hh : 0 < h) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hΛ : ∀ y ∈ Icc a b, X.lebesgue y ≤ Λ) (hΛ1 : 1 ≤ Λ) :
    |X.complexLogPotential x h-X.potentialNormalization +
      Real.pi*h*X.exteriorDensity a b X.potentialNormalization x 0| ≤
      max (Real.log (2*Λ)) (-Real.log δ)/n +
        (Real.sqrt (2*n*δ*logSquareBound) + |X.potentialNormalization| *(2*n*δ))/(Real.pi*h) +
        (exteriorKernelBound d*(weightedLogBound+|X.potentialNormalization|)/(Real.pi*d^2))*h^3 := by
  have hp := X.poisson_exterior_decomposition hn hd hx hx1 hh X.potentialNormalization
  have herr := X.local_poisson_potential_bound hn hI hδ hδ1 hh hΛ x hΛ1
  have hheight := X.exteriorDensity_height_bound hn hd hx hx1 X.potentialNormalization h
  have heq : X.complexLogPotential x h-X.potentialNormalization +
      Real.pi*h*X.exteriorDensity a b X.potentialNormalization x 0 =
      (∫ y in Icc a b, poissonKernel h (y-x)*(X.empiricalLogPotential y-X.potentialNormalization)) +
        Real.pi*h*(X.exteriorDensity a b X.potentialNormalization x 0-
          X.exteriorDensity a b X.potentialNormalization x h) := by rw [hp]; ring
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hheight (mul_nonneg Real.pi_pos.le hh.le)
  rw [abs_sub_comm] at hmul
  have he : Real.pi*h*((exteriorKernelBound d/Real.pi^2)*
        (weightedLogBound+|X.potentialNormalization|)/d^2*h^2) =
      (exteriorKernelBound d*(weightedLogBound+|X.potentialNormalization|)/(Real.pi*d^2))*h^3 := by
    field_simp
  rw [he] at hmul
  calc
    _ ≤ |∫ y in Icc a b, poissonKernel h (y-x)*(X.empiricalLogPotential y-X.potentialNormalization)| +
        |Real.pi*h*(X.exteriorDensity a b X.potentialNormalization x 0-
          X.exteriorDensity a b X.potentialNormalization x h)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos (mul_pos Real.pi_pos hh)]
      exact add_le_add herr hmul

end Erdos1132.Nodes
