import Erdos1132.BernsteinError
import Erdos1132.RescaledRiesz
import Erdos1132.DensityPositive

/-! # The sharp local first derivative estimate for actual interpolation rows -/

noncomputable section
open Real Complex Set Filter
open scoped Topology
namespace Erdos1132

theorem frequency_majorant {N ρ c t : ℝ} (hN : 0 ≤ N) (hc : 0 < c) (hρ : c ≤ ρ) (ht : 0 < t) :
    Real.pi*N*(ρ+1/t) ≤ (Real.pi*N*ρ)*(1+1/(c*t)) := by
  have hm := mul_le_mul_of_nonneg_right hρ (show 0 ≤ 1/(c*t) by positivity)
  have he : c*(1/(c*t)) = 1/t := by field_simp
  rw [he] at hm
  have h' : ρ+1/t ≤ ρ*(1+1/(c*t)) := by nlinarith
  have hp := mul_le_mul_of_nonneg_left h' (show 0 ≤ Real.pi*N by positivity)
  nlinarith

theorem derivative_multiplier_bound {N ρ c t A E e : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hρ : c ≤ ρ) (ht : 0 < t)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (he0 : 0 ≤ e) (he : e ≤ 32/t^2) :
    (Real.pi*N*(ρ+1/t))*(A*E)*(1+e) ≤
      (Real.pi*N*ρ)*(A*(E*(1+1/(c*t))*(1+32/t^2))) := by
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hf := frequency_majorant hN hc hρ ht
  have h1 := mul_le_mul_of_nonneg_right hf (mul_nonneg hA hE)
  have h2 := mul_le_mul h1 (by linarith : 1+e ≤ 1+32/t^2)
    (by linarith : 0 ≤ 1+e) (by positivity : 0 ≤ (Real.pi*N*ρ)*(1+1/(c*t))*(A*E))
  convert! h2 using 1 <;> ring

/-- Under a local logarithmic upper bound, every bounded-data interpolant has
normalized first derivative at most that upper level plus any fixed positive error. -/
theorem eventually_sharp_interpolant_derivative (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ v : Fin n → ℝ,
      (∀ i, |v i| ≤ 1) →
      |((X n).interpolant v).derivative.eval x| ≤
        (Real.pi*n*(X n).exteriorDensity l r (X n).potentialNormalization x 0)*
          (logarithmicLevel a b n+η) := by
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hXn : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c, hc, hdensity⟩ := eventually_exterior_density_positive X hlr hI
    (by linarith : 0 < 2*d) hXn
  have herr := (tendsto_localDerivativeMultiplier_error hlr hc a b).eventually
    (gt_mem_nhds hη)
  filter_upwards [hupper, hlevels, hXn, hdensity, eventually_interpolant_local_growth hlr hI hd,
    eventually_riesz_radius (l := l) (r := r) hc, herr]
    with n hu hl hn hdens hgrow hrad he
  intro x hx v hv
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  let A := logarithmicLevel a b n
  let E := Real.exp (localRectangleLoss l r n)
  let t := eighthRoot (n : ℝ)
  let ω := localFrequency (X n) l r x
  have hρ : c ≤ ρ := hdens x hx
  have ht : 0 < t := eighthRoot_pos (by exact_mod_cast hl.1)
  have hA : 0 < A := zero_lt_one.trans_le hl.2.1
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨hm, hω, hr, hh, herr⟩ := hrad (X n) x hρ
  have hg := hgrow (X n) hn A hl.2.1 hu x hx (hc.le.trans hρ) v hv
  have hbound := polynomial_local_derivative_bound hm hω (mul_pos hA hE) hr hh hg
  have hmajor := derivative_multiplier_bound (N := (n : ℝ)) (A := A) (E := E)
    (Nat.cast_nonneg n) hc hρ ht hA.le hE.le (by positivity) herr
  have hAerr : A*localDerivativeMultiplier l r c n ≤ A+η := by
    change A*(localDerivativeMultiplier l r c n-1) < η at he
    nlinarith
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hfinal := mul_le_mul_of_nonneg_left hAerr
    (show 0 ≤ Real.pi*n*ρ by positivity)
  exact hbound.trans (hmajor.trans hfinal)

end Erdos1132
