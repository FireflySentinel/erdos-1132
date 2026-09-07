import Erdos1132.Additive.JumpEnergyLower
import Erdos1132.Additive.SignedInterpolants
import Erdos1132.Additive.WeightedDeficit

/-! # A positive proportion of nodes have large normalized derivative jumps

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace Erdos1132

namespace Nodes
variable {n : ℕ} (X : Nodes n)

def jumpNodeWeight (a b : ℝ) (f : ℝ → ℝ) (i : Fin n) : ℝ :=
  (f (X.point i))^2/((n:ℝ)*X.exteriorDensity a b X.potentialNormalization (X.point i) 0)

def normalizedJump (a b : ℝ) (i : Fin n) : ℝ :=
  X.derivativeJump i/(2*Real.pi*(n:ℝ)*X.exteriorDensity a b X.potentialNormalization (X.point i) 0)

end Nodes

theorem eventually_many_large_jumps (X : ∀ n, Nodes n)
    {a b d l r M L c : ℝ} (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hd : 0 < d) (hlr : l ≤ r) (hJ : Icc l r ⊆ Icc (a+2*d) (b-2*d))
    (hM : 0 ≤ M) (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hMf : ∀ x, f x ≤ M)
    (hlip : ∀ x y, |f x-f y| ≤ L*|x-y|) (hsupp : ∀ x, x ∉ Icc l r → f x = 0)
    (hW : 0 < ∫ x, (f x)^2)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b,
      (X n).lebesgue y ≤ logarithmicLevel (2/Real.pi) c n) :
    ∃ D > 0, ∃ κ > 0, ∀ᶠ n : ℕ in atTop,
      κ*(n:ℝ) ≤ ((univ.filter (fun i => (X n).point i ∈ Icc l r ∧
        (2/Real.pi)*Real.log n-D ≤ (X n).normalizedJump a b i)).card : ℝ) := by
  have hc0 : 0 < 2/Real.pi := by positivity
  have hlevels := eventually_logarithmicLevel_bounds hc0 c
  have hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  have hMf' (x : ℝ) : |f x| ≤ M := by rw [abs_of_nonneg (hf0 x)]; exact hMf x
  obtain ⟨ρ₀, hρ₀, hpos⟩ := eventually_exterior_density_positive X hab hI (by linarith : 0 < 2*d) hΛ
  obtain ⟨Q, hQ, hquad⟩ := eventually_weighted_square_quadrature X hab hI
    (by linarith : 0 < 2*d) hlr hJ hM hL hfm hMf' hlip hsupp hΛ
  obtain ⟨E, hE, henergy⟩ := eventually_weighted_jump_lower X hab hI
    (by linarith : 0 < 2*d) hlr hJ hM hL hf hfm hf0 hMf hlip hsupp hΛ
  let W := ∫ x, (f x)^2
  let B := M^2/ρ₀+1
  let C := E+|c+1| * W+Q*(4*(2/Real.pi)+|c+1|)+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  let D₀ := 4*(C+1)/W
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  let D := D₀+|c+1|+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall : C/D₀ ≤ W/4 := by
    apply (div_le_iff₀ hD₀).mpr
    have he : (W/4)*D₀ = C+1 := by dsimp [D₀]; field_simp [show W ≠ 0 from hW.ne']
    rw [he]; linarith
  have hqsmall : ∀ᶠ n : ℕ in atTop, Q/quarterRoot n ≤ W/4 := by
    have hh := tendsto_inv_quarterRoot_nat.const_mul Q
    simp only [mul_zero, mul_one_div] at hh
    exact (hh.eventually (gt_mem_nhds (by positivity : (0:ℝ)<W/4))).mono (fun n hn => hn.le)
  refine ⟨D, hD, W/(2*B), by positivity, ?_⟩
  filter_upwards [hpos, hquad, henergy, hlevels, hqsmall,
    eventually_normalized_jump_upper X hab hI hd hc0 hupper (by norm_num : (0:ℝ)<1)]
    with n hnp hnq hne hnl hns hnu
  have hn := hnl.1
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hroot := one_le_quarterRoot hn1
  have hroot0 := quarterRoot_pos hnR
  let w := (X n).jumpNodeWeight a b f
  let T := (X n).normalizedJump a b
  let U := logarithmicLevel (2/Real.pi) c n+1
  have hU : 0 ≤ U := by dsimp [U]; linarith [hnl.2.1]
  have hw0 (i : Fin n) : 0 ≤ w i := by
    by_cases hi : (X n).point i ∈ Icc l r
    · have hρ : 0 < (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0 :=
        hρ₀.trans_le (hnp _ (hJ hi))
      dsimp [w, Nodes.jumpNodeWeight]; positivity
    · simp [w, Nodes.jumpNodeWeight, hsupp _ hi]
  have hwpos (i : Fin n) (hi : 0 < w i) : (X n).point i ∈ Icc l r := by
    by_contra hh
    simp [w, Nodes.jumpNodeWeight, hsupp _ hh] at hi
  have hwb (i : Fin n) : w i ≤ B/(n:ℝ) := by
    by_cases hi : (X n).point i ∈ Icc l r
    · have hs := square_div_bound hρ₀ (hnp _ (hJ hi)) hM (hMf' ((X n).point i))
      have he : w i = ((f ((X n).point i))^2/
          (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)/(n:ℝ) := by
        dsimp [w, Nodes.jumpNodeWeight]; ring
      rw [he]
      exact div_le_div_of_nonneg_right ((le_abs_self _).trans hs |>.trans (by dsimp [B]; linarith)) hnR.le
    · simp [w, Nodes.jumpNodeWeight, hsupp _ hi, (div_pos hB hnR).le]
  have htupper (i : Fin n) (hi : 0 < w i) : T i ≤ U := by
    have hρ := hρ₀.trans_le (hnp _ (hJ (hwpos i hi)))
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi*(n:ℝ)*
      (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)).mpr
    have hh := hnu i (hJ (hwpos i hi))
    convert! hh using 1 <;> ring
  have hwsum : (∑ i, w i) =
      (∑ i, (f ((X n).point i))^2/
        (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)/(n:ℝ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    dsimp [w, Nodes.jumpNodeWeight]
    ring
  have hq : |(∑ i, w i)-W| ≤ Q/quarterRoot n := by rw [hwsum]; exact hnq
  have htotal : 3*W/4 ≤ ∑ i, w i := by have hh := (abs_le.mp hq).1; linarith
  have he : (2/Real.pi)*Real.log n*W-E ≤ ∑ i, w i*T i := hne
  have hUQ : U*(Q/quarterRoot n) ≤ Q*(4*(2/Real.pi)+|c+1|) := by
    have hl := mul_le_mul_of_nonneg_left (log_div_quarterRoot_le hnR) hc0.le
    have hb : (c+1)/quarterRoot n ≤ |c+1| := by
      calc
        _ ≤ |c+1|/quarterRoot n := div_le_div_of_nonneg_right (le_abs_self _) hroot0.le
        _ ≤ |c+1| := (div_le_self (abs_nonneg _) hroot)
    have hu : U/quarterRoot n ≤ 4*(2/Real.pi)+|c+1| := by
      dsimp [U, logarithmicLevel]
      have he' : ((2/Real.pi)*Real.log n+c+1)/quarterRoot n =
        (2/Real.pi)*(Real.log n/quarterRoot n)+(c+1)/quarterRoot n := by ring
      rw [he']; linarith
    have hh := mul_le_mul_of_nonneg_left hu hQ.le
    convert! hh using 1 <;> ring
  have hdef : (∑ i, w i*(U-T i)) ≤ C := by
    have hq' := mul_le_mul_of_nonneg_left (abs_le.mp hq).2 hU
    have heq : (∑ i, w i*(U-T i)) = U*(∑ i, w i)-(∑ i, w i*T i) := by
      rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro i hi; ring
    rw [heq]
    have hcW := mul_le_mul_of_nonneg_right (le_abs_self (c+1)) hW.le
    dsimp [C, U, logarithmicLevel] at *
    nlinarith
  have hg := many_large_values_of_weighted_deficit hn w T hD₀ hW hB hw0 hwb htupper htotal hdef hsmall
  apply hg.trans
  exact_mod_cast Finset.card_le_card (show (univ.filter (fun i => 0 < w i ∧ U-D₀ ≤ T i)) ⊆
      (univ.filter (fun i => (X n).point i ∈ Icc l r ∧ (2/Real.pi)*Real.log n-D ≤ T i)) by
    intro i hi
    obtain ⟨hi0, hiT⟩ := (mem_filter.mp hi).2
    refine mem_filter.mpr ⟨mem_univ i, hwpos i hi0, ?_⟩
    dsimp [U, logarithmicLevel, D] at *
    have hc := neg_abs_le (c+1)
    linarith)

end Erdos1132
