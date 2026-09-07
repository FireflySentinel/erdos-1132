import Erdos1132.Additive.AtomicEnergyBound
import Erdos1132.Additive.WeightedQuadrature
import Erdos1132.Additive.JumpEnergy

/-! # The weighted derivative-jump lower bound for an actual node array

Paper: §3, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace Erdos1132

theorem eventually_weighted_jump_lower (X : ∀ n, Nodes n)
    {a b d l r M L : ℝ} (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hd : 0 < d) (hlr : l ≤ r) (hJ : Icc l r ⊆ Icc (a+d) (b-d))
    (hM : 0 ≤ M) (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hMf : ∀ x, f x ≤ M)
    (hlip : ∀ x y, |f x-f y| ≤ L*|x-y|) (hsupp : ∀ x, x ∉ Icc l r → f x = 0)
    (hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      (2/Real.pi)*Real.log n*(∫ x, (f x)^2)-C ≤
        ∑ i, ((f ((X n).point i))^2/
          ((n:ℝ)*(X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0))*
          ((X n).derivativeJump i/(2*Real.pi*(n:ℝ)*
            (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)) := by
  have hMf' (x : ℝ) : |f x| ≤ M := by rw [abs_of_nonneg (hf0 x)]; exact hMf x
  have hsuppI (x : ℝ) (hx : x ∉ Icc (-1:ℝ) 1) : f x = 0 :=
    hsupp x (fun hxJ => hx (hI (mem_interval_of_inset hd.le (hJ hxJ))))
  obtain ⟨c, hc, hpos⟩ := eventually_exterior_density_positive X hab hI hd hΛ
  obtain ⟨Q, hQ, hquad⟩ := eventually_weighted_square_quadrature X hab hI hd hlr hJ
    hM hL hfm hMf' hlip hsupp hΛ
  let A := M/c
  let B := 2*L+(∫ t, |f t|)+2*M*Real.log 3
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  let C := 16*Q+2*B*A+B*(∫ t, f t)+A^2+1
  have hC : 0 < C := by
    have hi : 0 ≤ ∫ t, f t := integral_nonneg hf0
    dsimp [C]
    positivity
  refine ⟨C/Real.pi, by positivity, ?_⟩
  filter_upwards [hpos, hquad, eventually_gt_atTop (0:ℕ)] with n hnp hnq hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hε : 0 < 1/(n:ℝ) := by positivity
  let ρ (x : ℝ) := (X n).exteriorDensity a b (X n).potentialNormalization x 0
  let w (i : Fin n) := f ((X n).point i)/ρ ((X n).point i)
  have hw (i : Fin n) : 0 ≤ w i ∧ w i ≤ A := by
    by_cases hi : (X n).point i ∈ Icc l r
    · have hρ := hc.trans_le (hnp _ (hJ hi))
      refine ⟨div_nonneg (hf0 _) hρ.le, ?_⟩
      exact div_le_div₀ hM (hMf _) hc (hnp _ (hJ hi))
    · simp [w, hsupp _ hi, hA]
  have hconv (t : ℝ) : |rieszConvolution (1/(n:ℝ)) f t-2*Real.log n*f t| ≤ B := by
    have he := riesz_convolution_log_error hε
      (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn1)
      hL hf hMf' hlip t
    simpa only [one_div, inv_inv, rieszConvolution] using he
  have hqw : |(∑ i, w i*f ((X n).point i))/(n:ℝ)-(∫ t, (f t)^2)| ≤ Q/quarterRoot n := by
    convert! hnq using 2
    congr 2
    apply sum_congr rfl
    intro i hi
    dsimp [w, ρ]
    ring
  have hmain := atomic_riesz_lower_bound hn (X n).point w
    (fun i => abs_le.mpr ((X n).mem_interval i)) hA hM hB
    (fun i => (hw i).1) (fun i => (hw i).2) hf hfm hf0 hMf hsuppI hconv hqw
  have hreg := regularized_energy_le_reciprocal_add_diag (X n).point w
    (X n).injective (fun i => (hw i).1) hε
  have hdiag : (∑ i, (w i)^2/(1/(n:ℝ)))/(n:ℝ)^2 ≤ A^2 := by
    have he : (∑ i, (w i)^2/(1/(n:ℝ)))/(n:ℝ)^2 = (∑ i, (w i)^2)/(n:ℝ) := by
      simp_rw [sum_div]
      apply sum_congr rfl
      intro i hi
      field_simp
    rw [he]
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ ∑ _i : Fin n, A^2 := sum_le_sum (fun i _ => by nlinarith [(hw i).1, (hw i).2])
      _ = _ := by simp; ring
  have hlogQ : 4*Real.log n*(Q/quarterRoot n) ≤ 16*Q := by
    have hh := mul_le_mul_of_nonneg_left (log_div_quarterRoot_le hnR) (by positivity : 0 ≤ 4*Q)
    convert! hh using 1 <;> ring
  have hreg' := div_le_div_of_nonneg_right hreg (sq_nonneg (n:ℝ))
  rw [add_div] at hreg'
  have hrec : 2*Real.log n*(∫ t, (f t)^2)-C ≤
      (∑ i, ∑ j, w i*w j/|(X n).point i-(X n).point j|)/(n:ℝ)^2 := by
    dsimp only [C]
    linarith
  have hjump := div_le_div_of_nonneg_right ((X n).reciprocal_energy_le_jumpEnergy w) (sq_nonneg (n:ℝ))
  have hfinal := div_le_div_of_nonneg_right (hrec.trans hjump) Real.pi_pos.le
  have he : (∑ i, (w i)^2*(X n).derivativeJump i/2)/(n:ℝ)^2/Real.pi =
      ∑ i, ((f ((X n).point i))^2/((n:ℝ)*ρ ((X n).point i)))*
        ((X n).derivativeJump i/(2*Real.pi*(n:ℝ)*ρ ((X n).point i))) := by
    rw [sum_div, sum_div]
    apply sum_congr rfl
    intro i hi
    dsimp only [w]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  rw [he] at hfinal
  convert! hfinal using 1 <;> ring

end Erdos1132
