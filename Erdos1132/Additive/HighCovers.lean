import Erdos1132.Additive.IntervalWeight
import Erdos1132.Additive.IsolatedPeaks
import Erdos1132.Additive.CoverIntersection

/-! # Actual high-value sets with uniform measure and intersection bounds

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped Topology BigOperators
namespace Erdos1132

theorem exists_high_covers (X : ∀ n, Nodes n) {a b c : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc a b,
      (X n).lebesgue x ≤ logarithmicLevel (2/Real.pi) c n) :
    ∃ A : ℕ → Set ℝ, ∃ D > 0, ∃ c₁ > 0, ∃ C > 0, ∃ N : ℕ,
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n ≥ N, 0 < n ∧ 1 ≤ Real.log (n:ℝ) ∧ A n ⊆ Icc a b ∧
        (∀ x ∈ A n, (2/Real.pi)*Real.log n-D ≤ (X n).lebesgue x) ∧
        c₁/Real.log n ≤ volume.real (A n) ∧ volume.real (A n) ≤ C/Real.log n) ∧
      (∀ n m : ℕ, N ≤ n → N ≤ m → n < m → volume.real (A n ∩ A m) ≤
        C*(1/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m))) := by
  classical
  let d := (b-a)/16
  have hd : 0 < d := by dsimp [d]; linarith
  let l := a+4*d
  let r := b-4*d
  have hlr : l < r := by dsimp [l, r, d]; linarith
  let f := intervalWeight l r
  have hf := integrable_intervalWeight l r
  have hfm := (continuous_intervalWeight l r).measurable
  have hfl (x y : ℝ) : |f x-f y| ≤ 1*|x-y| := by simpa using intervalWeight_lipschitz l r x y
  obtain ⟨D, hD, κ, hκ, hmany⟩ := eventually_many_large_jumps X hab hI
    (by linarith : 0 < 2*d) hlr.le
    (show Icc l r ⊆ Icc (a+2*(2*d)) (b-2*(2*d)) by
      intro x hx; dsimp [l, r] at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (sub_nonneg.mpr hlr.le) (by norm_num : (0:ℝ) ≤ 1) hf hfm
    (intervalWeight_nonneg l r) (intervalWeight_bound hlr.le) hfl
    (fun x hx => intervalWeight_zero_off hx) (integral_intervalWeight_sq_pos hlr) hupper
  obtain ⟨δ, hδ, K, hK, hpeaks⟩ := eventually_isolated_peaks X hab hI hd hupper D
  obtain ⟨L, hL, hlipschitz⟩ := eventually_lebesgue_lipschitz X hab hI
    (by linarith : 0 < d/4) (by positivity : 0 < 2/Real.pi) hupper
  let β := 1/(L+1)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβL : L*β ≤ 1 := by
    dsimp [β]; rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < L+1)).mpr
    linarith
  let S (n : ℕ) := univ.filter (fun i : Fin n => (X n).point i ∈ Icc l r ∧
    (2/Real.pi)*Real.log n-D ≤ (X n).normalizedJump a b i)
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ n : ℕ in atTop, β/(n:ℝ) ≤ d/2 := by
    have ht : Tendsto (fun n : ℕ => β/(n:ℝ)) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.const_div_atTop β
    exact (ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<d/2))).mono (fun n hn => hn.le)
  have hall := (eventually_gt_atTop (0:ℕ)).and (hlog.and (hmany.and (hpeaks.and (hlipschitz.and hsmall))))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  have hex (n : ℕ) (i : Fin n) : ∃ y : ℝ, N ≤ n → i ∈ S n →
      y ∈ Icc (a+d) (b-d) ∧ |y-(X n).point i| ≤ K/n ∧
        (2/Real.pi)*Real.log n-K ≤ (X n).lebesgue y := by
    by_cases hn : N ≤ n
    · by_cases hi : i ∈ S n
      · have hh := (mem_filter.mp hi).2
        have hp := (hN n hn).2.2.2.1 i hh.1 hh.2
        obtain ⟨y, hy, hm, hv⟩ := hp.2
        exact ⟨y, fun _ _ => ⟨hy, hm, hv⟩⟩
      · exact ⟨0, fun _ hi' => False.elim (hi hi')⟩
    · exact ⟨0, fun hn' _ => False.elim (hn hn')⟩
  choose y hy using hex
  let A (n : ℕ) := centeredCover (S n) (y n) (β/((n:ℝ)*Real.log n))
  let B := coverMultiplicity δ K β
  let C₀ := 4*β/δ+2*β*B+1
  let C := 2*β+C₀*(2*β+2)+1
  have hB : 0 < B := coverMultiplicity_pos hδ hK.le hβ
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hrow (n : ℕ) (hn : N ≤ n) : A n ⊆ Icc a b ∧
      (∀ x ∈ A n, (2/Real.pi)*Real.log n-(K+1) ≤ (X n).lebesgue x) ∧
      (2*β*κ/B)/Real.log n ≤ volume.real (A n) ∧ volume.real (A n) ≤ 2*β/Real.log n ∧
      (∀ u v : ℝ, u ≤ v → volume.real (A n ∩ Icc u v) ≤ C₀*((v-u)/Real.log n+1/((n:ℝ)*Real.log n))) := by
    obtain ⟨hn0, hln, hcard, hp, hLip, hsmall⟩ := hN n hn
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
    have hl : 0 < Real.log (n:ℝ) := by linarith
    let rad := β/((n:ℝ)*Real.log n)
    have hrad : 0 < rad := by dsimp [rad]; positivity
    have hradd : rad ≤ d/2 :=
      (div_le_div_of_nonneg_left hβ.le hnR (by nlinarith : (n:ℝ) ≤ (n:ℝ)*Real.log n)).trans hsmall
    have hiso (i : Fin n) (hi : i ∈ S n) : (X n).OneSidedIsolated i (δ/(n:ℝ)) :=
      (hp i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2).1
    have hmove (i : Fin n) (hi : i ∈ S n) : |y n i-(X n).point i| ≤ K/(n:ℝ) := (hy n i hn hi).2.1
    have hmeasure := (X n).scaled_cover_bounds (S n) (y n) hn0 hln hδ hK.le hβ hκ hcard hiso hmove
    have hpoint (x : ℝ) (hx : x ∈ A n) : x ∈ Icc (a+2*(d/4)) (b-2*(d/4)) ∧
        (2/Real.pi)*Real.log n-(K+1) ≤ (X n).lebesgue x := by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      have hiy := (hy n i hn hi).1
      have hix : x ∈ Icc (a+2*(d/4)) (b-2*(d/4)) :=
        ⟨by linarith [hxi.1, hiy.1], by linarith [hxi.2, hiy.2]⟩
      have hiy' : y n i ∈ Icc (a+2*(d/4)) (b-2*(d/4)) :=
        ⟨by linarith [hiy.1], by linarith [hiy.2]⟩
      have hdist : |x-y n i| ≤ rad := abs_le.mpr ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
      have hdif := (hLip x hix (y n i) hiy').trans
        (mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ L*(n:ℝ)*Real.log n))
      have he : L*(n:ℝ)*Real.log n*rad = L*β := by dsimp [rad]; field_simp
      rw [he] at hdif
      have hv := (hy n i hn hi).2.2
      have hh := (abs_le.mp hdif).1
      exact ⟨hix, by linarith⟩
    refine ⟨?_, fun x hx => (hpoint x hx).2, hmeasure.2.1, hmeasure.1, hmeasure.2.2⟩
    intro x hx
    exact ⟨by linarith [(hpoint x hx).1.1], by linarith [(hpoint x hx).1.2]⟩
  refine ⟨A, K+1, by positivity, 2*β*κ/B, by positivity, C, hC, N,
    fun n => measurableSet_centeredCover _ _ _, ?_, ?_⟩
  · intro n hn
    have hh := hrow n hn
    refine ⟨(hN n hn).1, (hN n hn).2.1, hh.1, hh.2.1, hh.2.2.1, ?_⟩
    exact hh.2.2.2.1.trans (div_le_div_of_nonneg_right (by dsimp [C]; nlinarith)
      (by linarith [(hN n hn).2.1]))
  · intro n m hn hm hnm
    have hn0 := (hN n hn).1
    have hm0 := (hN m hm).1
    have hln : 0 < Real.log (n:ℝ) := by linarith [(hN n hn).2.1]
    have hlm : 0 < Real.log (m:ℝ) := by linarith [(hN m hm).2.1]
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm0
    have hh := scaled_cover_intersection (S n) (y n) hβ.le hC₀.le hn0 hm0 hln hlm (A m)
      (hrow m hm).2.2.2.2
    have hC1 : C₀*(2*β) ≤ C := by dsimp [C]; nlinarith
    have hC2 : C₀ ≤ C := by dsimp [C]; nlinarith
    have h1 := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ 1/(Real.log n*Real.log m))
    have h2 := mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ (n:ℝ)/((m:ℝ)*Real.log m))
    have he : C₀*(2*β/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m)) =
        C₀*(2*β)*(1/(Real.log n*Real.log m))+C₀*((n:ℝ)/((m:ℝ)*Real.log m)) := by ring
    rw [he] at hh
    exact hh.trans (by nlinarith)

end Erdos1132
