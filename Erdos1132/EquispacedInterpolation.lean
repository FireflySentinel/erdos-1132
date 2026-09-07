import Erdos1132.Interpolation
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # A global complex bound from interpolation on a fixed real interval -/

noncomputable section
open Polynomial Finset Set Complex
open scoped BigOperators
namespace Erdos1132

def equispacedPoint (n : ℕ) (l r : ℝ) (i : Fin n) : ℝ := l+(r-l)*(i.val : ℝ)/n

theorem equispacedPoint_mem {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r) (i : Fin n) :
    equispacedPoint n l r i ∈ Set.Icc l r := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hfrac : 0 ≤ (r-l)*(i.val : ℝ)/n := by positivity
  have hfrac1 : (r-l)*(i.val : ℝ)/n ≤ r-l := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  constructor <;> dsimp [equispacedPoint] <;> linarith

theorem equispacedPoint_separated {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r)
    {i j : Fin n} (hij : i ≠ j) :
    (r-l)/n ≤ |equispacedPoint n l r i-equispacedPoint n l r j| := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 1 ≤ |(i.val : ℝ)-(j.val : ℝ)| := by
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hne with h | h
    · have hc : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast (show j.val+1 ≤ i.val by omega)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have he : equispacedPoint n l r i-equispacedPoint n l r j =
      ((r-l)/n)*((i.val : ℝ)-(j.val : ℝ)) := by dsimp [equispacedPoint]; ring
  rw [he, abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hlr.le) hnR.le)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (div_nonneg (sub_nonneg.mpr hlr.le) hnR.le)

theorem equispacedPoint_injective {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r) :
    Function.Injective (equispacedPoint n l r) := by
  intro i j he
  by_contra hij
  have hs := equispacedPoint_separated hn hlr hij
  rw [he, sub_self, abs_zero] at hs
  exact (div_pos (sub_pos.mpr hlr) (by exact_mod_cast hn)).not_ge hs

theorem equispaced_basis_complex_bound {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r)
    (hI : Set.Icc l r ⊆ Set.Icc (-1) 1) (i : Fin n) {z : ℂ} (hz : ‖z‖ ≤ 3) :
    ‖(Lagrange.basis Finset.univ (equispacedPoint n l r) i).eval₂ (algebraMap ℝ ℂ) z‖ ≤
      (1+4*(n : ℝ)/(r-l))^n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (r-l)/n := div_pos (sub_pos.mpr hlr) hnR
  let K : ℝ := 1+4*(n : ℝ)/(r-l)
  have hK : 1 ≤ K := by
    have hpos : 0 ≤ 4*(n : ℝ)/(r-l) := div_nonneg (by positivity) (sub_nonneg.mpr hlr.le)
    dsimp [K]
    linarith
  simp only [Lagrange.basis, eval₂_finsetProd, norm_prod]
  apply le_trans (Finset.prod_le_prod (g := fun _ => K) (fun _ _ => norm_nonneg _) ?_) ?_
  · intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hdist := equispacedPoint_separated hn hlr hji.symm
    have hpoint := hI (equispacedPoint_mem hn hlr j)
    have habs : |equispacedPoint n l r j| ≤ 1 := abs_le.mpr hpoint
    have hnum : ‖z-(equispacedPoint n l r j : ℂ)‖ ≤ 4 := by
      have ht := norm_sub_le z (equispacedPoint n l r j : ℂ)
      simp only [Complex.norm_real, Real.norm_eq_abs] at ht
      linarith
    simp only [Lagrange.basisDivisor, eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, norm_mul, map_inv₀]
    change ‖((equispacedPoint n l r i-equispacedPoint n l r j : ℝ) : ℂ)⁻¹‖*
      ‖z-(equispacedPoint n l r j : ℂ)‖ ≤ K
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have hi := one_div_le_one_div_of_le hd hdist
    have hn0 := norm_nonneg (z-(equispacedPoint n l r j : ℂ))
    calc
      _ ≤ ((r-l)/(n : ℝ))⁻¹*4 :=
        mul_le_mul (by simpa only [one_div] using hi) hnum hn0 (inv_nonneg.mpr hd.le)
      _ ≤ K := by dsimp [K]; field_simp; nlinarith
  · rw [Finset.prod_const]
    apply pow_le_pow_right₀ hK
    exact (Finset.card_erase_le).trans (by simp)

theorem polynomial_complex_bound_from_interval {n : ℕ} {l r Λ : ℝ} {p : ℝ[X]}
    (hn : 0 < n) (hlr : l < r) (hI : Set.Icc l r ⊆ Set.Icc (-1) 1)
    (hΛ : 0 ≤ Λ) (hp : p.degree < n) (hbound : ∀ x ∈ Set.Icc l r, |p.eval x| ≤ Λ)
    {z : ℂ} (hz : ‖z‖ ≤ 3) :
    ‖p.eval₂ (algebraMap ℝ ℂ) z‖ ≤ Λ*n*(1+4*(n : ℝ)/(r-l))^n := by
  have hrepr := Lagrange.eq_interpolate (f := p) (s := Finset.univ)
    (equispacedPoint_injective hn hlr).injOn (by simpa using hp)
  conv_lhs => rw [hrepr]
  simp only [Lagrange.interpolate_apply, eval₂_finsetSum, eval₂_mul, eval₂_C]
  apply (norm_sum_le _ _).trans
  have he : Λ*n*(1+4*(n : ℝ)/(r-l))^n =
      ∑ _i : Fin n, Λ*(1+4*(n : ℝ)/(r-l))^n := by simp; ring
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  apply mul_le_mul _ (equispaced_basis_complex_bound hn hlr hI i hz) (norm_nonneg _) hΛ
  change ‖((p.eval (equispacedPoint n l r i) : ℝ) : ℂ)‖ ≤ Λ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    hbound _ (equispacedPoint_mem hn hlr i)

/-- A deliberately coarse exponential form sufficient on the vertical sides
of the local rectangle. -/
theorem polynomial_complex_exponential_bound {n : ℕ} {l r Λ : ℝ} {p : ℝ[X]}
    (hn : 0 < n) (hlr : l < r) (hI : Set.Icc l r ⊆ Set.Icc (-1) 1)
    (hΛ : 0 ≤ Λ) (hp : p.degree < n) (hbound : ∀ x ∈ Set.Icc l r, |p.eval x| ≤ Λ)
    {z : ℂ} (hz : ‖z‖ ≤ 3) :
    ‖p.eval₂ (algebraMap ℝ ℂ) z‖ ≤ Λ*Real.exp ((2+4/(r-l))*(n : ℝ)^2) := by
  have hb := polynomial_complex_bound_from_interval hn hlr hI hΛ hp hbound hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let c : ℝ := 4/(r-l)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hN : (n : ℝ) ≤ Real.exp ((n : ℝ)^2) := by
    have he := Real.add_one_le_exp ((n : ℝ)^2)
    nlinarith
  have hK : 1+4*(n : ℝ)/(r-l) ≤ Real.exp ((1+c)*n) := by
    have he := Real.add_one_le_exp ((1+c)*(n : ℝ))
    have hid : 4*(n : ℝ)/(r-l) = c*n := by dsimp [c]; ring
    rw [hid]
    nlinarith
  have hpw := pow_le_pow_left₀ (by positivity : 0 ≤ 1+4*(n : ℝ)/(r-l)) hK n
  rw [← Real.exp_nat_mul] at hpw
  have hm := mul_le_mul hN hpw (pow_nonneg (by positivity : 0 ≤ 1+4*(n : ℝ)/(r-l)) n)
    (Real.exp_pos _).le
  rw [← Real.exp_add] at hm
  have he : (n : ℝ)^2+n*((1+c)*n) = (2+4/(r-l))*(n : ℝ)^2 := by dsimp [c]; ring
  rw [he] at hm
  exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm hΛ)

end Erdos1132
