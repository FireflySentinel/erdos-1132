import Erdos1132.Additive.SignedInterpolants
import Mathlib.Analysis.Calculus.MeanValue

/-! # A local Lipschitz bound for the whole Lebesgue function

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Real
open scoped Topology
namespace Erdos1132
namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem lebesgue_lipschitz_of_interpolant_derivative {a b K : ℝ}
    (hbound : ∀ t ∈ Icc a b, ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      |(X.interpolant v).derivative.eval t| ≤ K)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |X.lebesgue x-X.lebesgue y| ≤ K*|x-y| := by
  have hle (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
      X.lebesgue x-X.lebesgue y ≤ K*|x-y| := by
    obtain ⟨v, hv, he⟩ := X.exists_interpolant_attaining x
    have hdiff := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (X.interpolant v).differentiableAt)
      (fun t ht => by simpa only [Polynomial.deriv, Real.norm_eq_abs] using hbound t ht v hv)
      (convex_Icc a b) hy hx
    have hyv : (X.interpolant v).eval y ≤ X.lebesgue y :=
      (le_abs_self _).trans (X.interpolant_eval_le v hv y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hdiff
    have hd := (le_abs_self ((X.interpolant v).eval x-(X.interpolant v).eval y)).trans hdiff
    rw [he] at hd
    linarith
  apply abs_le.mpr
  constructor
  · have hh := hle y x hy hx
    rw [abs_sub_comm y x] at hh
    linarith
  · exact hle x y hx hy

end Nodes

theorem eventually_lebesgue_lipschitz (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d),
      ∀ y ∈ Icc (l+2*d) (r-2*d),
        |(X n).lebesgue x-(X n).lebesgue y| ≤ C*(n:ℝ)*Real.log n*|x-y| := by
  obtain ⟨D, hD, hDb⟩ := uniform_exterior_density_bounds hlr hI (by linarith : 0 < 2*d)
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨Real.pi*D*(a+|b|+2), by positivity, ?_⟩
  filter_upwards [hupper, hlevels, hlog,
    eventually_sharp_interpolant_derivative X hlr hI hd ha hupper (by norm_num : (0:ℝ)<1)]
    with n hu hl hln hder
  have hnΛ (y : ℝ) (hy : y ∈ Icc l r) : (X n).lebesgue y ≤ n := (hu y hy).trans hl.2.2
  have hρb := (hDb n (X n) hl.1 hnΛ).1
  have hlev : logarithmicLevel a b n+1 ≤ (a+|b|+2)*Real.log n := by
    dsimp [logarithmicLevel]
    nlinarith [le_abs_self b, abs_nonneg b]
  intro x hx y hy
  apply (X n).lebesgue_lipschitz_of_interpolant_derivative (a := l+2*d) (b := r-2*d) ?_ hx hy
  intro t ht v hv
  have hρ := (le_abs_self _).trans (hρb t ht)
  have h1 := mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ Real.pi*(n:ℝ))
  have h2 := mul_le_mul h1 hlev (by linarith [hl.2.1] : 0 ≤ logarithmicLevel a b n+1)
    (by positivity : 0 ≤ Real.pi*(n:ℝ)*D)
  exact (hder t ht v hv).trans (h2.trans_eq (by ring))

end Erdos1132
