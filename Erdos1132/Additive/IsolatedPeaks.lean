import Erdos1132.Additive.LargeJumps
import Erdos1132.Additive.IsolatedPacking
import Erdos1132.Additive.InterpolantPeak

/-! # Large-jump nodes yield nearby high values and one-sided separation

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Real
open scoped Topology
namespace Erdos1132

theorem eventually_isolated_peaks (X : ∀ n, Nodes n)
    {l r d c : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r,
      (X n).lebesgue y ≤ logarithmicLevel (2/Real.pi) c n) (D : ℝ) :
    ∃ s > 0, ∃ K > 0, ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin n, (X n).point k ∈ Icc (l+4*d) (r-4*d) →
        (2/Real.pi)*Real.log n-D ≤ (X n).normalizedJump l r k →
        (X n).OneSidedIsolated k (s/(n:ℝ)) ∧
        ∃ y ∈ Icc (l+d) (r-d), |y-(X n).point k| ≤ K/n ∧
          (2/Real.pi)*Real.log n-K ≤ (X n).lebesgue y := by
  have hc0 : 0 < 2/Real.pi := by positivity
  have hlevels := eventually_logarithmicLevel_bounds hc0 c
  have hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c₀, hc₀, hpos⟩ := eventually_exterior_density_positive X hlr hI (by linarith : 0 < 4*d) hΛ
  obtain ⟨B, hB, hsecond⟩ := eventually_interpolant_second_derivative X hlr hI hd hc0 hupper
  obtain ⟨K, hK, hpeak⟩ := eventually_interpolant_peak X hlr hI hd hc0 hupper D
  let s := min d (c₀/(B+1))
  have hs : 0 < s := lt_min hd (by positivity)
  have hsB : B*s ≤ c₀ := by
    have hh := min_le_right d (c₀/(B+1))
    have hh' := (le_div_iff₀ (by positivity : 0 < B+1)).mp hh
    change s*(B+1) ≤ c₀ at hh'
    nlinarith
  have hlog : ∀ᶠ n : ℕ in atTop, max 1 (Real.pi*D) ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  refine ⟨s, hs, K, hK, ?_⟩
  filter_upwards [hlevels, hpos, hsecond, hpeak, hlog] with n hnl hnp hns hnk hln
  have hn := hnl.1
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ Real.log (n:ℝ) := (le_max_left _ _).trans hln
  have hlog0 : 0 < Real.log (n:ℝ) := by linarith
  intro k hk hlarge
  let x := (X n).point k
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  have hρc : c₀ ≤ ρ := hnp _ hk
  have hρ : 0 < ρ := hc₀.trans_le hρc
  have hx2 : x ∈ Icc (l+2*d) (r-2*d) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hδ : 0 < s/(n:ℝ) := by positivity
  have hδd : s/(n:ℝ) ≤ d := (div_le_self hs.le hn1).trans (min_le_left _ _)
  have hmargin : Icc (x-s/(n:ℝ)) (x+s/(n:ℝ)) ⊆ Icc (l+2*d) (r-2*d) := by
    intro y hy
    exact ⟨by linarith [hy.1, hk.1], by linarith [hy.2, hk.2]⟩
  have hBd : (B*(n:ℝ)^2*Real.log n)*(s/(n:ℝ)) ≤ c₀*(n:ℝ)*Real.log n := by
    have hh := mul_le_mul_of_nonneg_right hsB (by positivity : 0 ≤ (n:ℝ)*Real.log n)
    convert! hh using 1 <;> field_simp <;> ring
  have hlarge' : ((2/Real.pi)*Real.log n-D)*(2*Real.pi*(n:ℝ)*ρ) ≤ (X n).derivativeJump k :=
    (le_div_iff₀ (by positivity : 0 < 2*Real.pi*(n:ℝ)*ρ)).mp hlarge
  have hDlog : D ≤ Real.log n/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    simpa only [mul_comm D] using (le_max_right 1 (Real.pi*D)).trans hln
  have hmain : (Real.log n/Real.pi)*(2*Real.pi*(n:ℝ)*ρ) ≤ (X n).derivativeJump k := by
    have hh : Real.log n/Real.pi ≤ (2/Real.pi)*Real.log n-D := by
      have he : (2/Real.pi)*Real.log n = 2*(Real.log n/Real.pi) := by ring
      rw [he]; linarith
    exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans hlarge'
  have hmain' : 2*ρ*(n:ℝ)*Real.log n ≤ (X n).derivativeJump k := by
    convert! hmain using 1 <;> field_simp <;> ring
  have hjump : 2*(c₀*(n:ℝ)*Real.log n) ≤ (X n).derivativeJump k := by
    have hh := mul_le_mul_of_nonneg_right hρc (by positivity : 0 ≤ 2*(n:ℝ)*Real.log n)
    nlinarith
  constructor
  · exact (X n).oneSidedIsolated_of_large_jump k (by positivity) hδ hmargin hBd hjump
      (fun v hv t ht => hns t ht v hv)
  · obtain ⟨v, hv, he⟩ := (X n).exists_interpolant_jump k
    apply hnk x hx2 v hv
    have hident : |((X n).interpolant v).derivative.eval x|/(Real.pi*(n:ℝ)*ρ) =
        (X n).normalizedJump l r k := by
      rw [he, abs_of_nonneg (div_nonneg ((X n).derivativeJump_nonneg k) (by norm_num))]
      dsimp [Nodes.normalizedJump, ρ, x]
      ring
    rw [hident]
    exact hlarge

end Erdos1132
