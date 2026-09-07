import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # An explicit local Phragmén–Lindelöf estimate on a rectangle -/

noncomputable section
open Complex Real Metric Set
open scoped Topology
namespace Erdos1132

def rectangleBarrier (T B : ℝ) (z : ℂ) : ℂ :=
  2*B*(Complex.exp (z-T)+Complex.exp (-z-T))

theorem rectangleBarrier_re (T B : ℝ) (z : ℂ) :
    (rectangleBarrier T B z).re =
      2*B*(Real.exp (z.re-T)+Real.exp (-z.re-T))*Real.cos z.im := by
  simp [rectangleBarrier, Complex.exp_re, Real.cos_neg]
  ring

theorem cos_ge_half_of_abs_le_half {v : ℝ} (hv : |v| ≤ 1/2) : 1/2 ≤ Real.cos v := by
  have h := Real.lipschitzWith_cos.dist_le_mul v 0
  simp only [Real.dist_eq, Real.cos_zero, NNReal.coe_one, one_mul, sub_zero] at h
  have h' := (abs_le.mp h).1
  linarith

theorem rectangleBarrier_nonneg {T B : ℝ} (hB : 0 ≤ B) {z : ℂ}
    (hz : |z.im| ≤ 1/2) : 0 ≤ (rectangleBarrier T B z).re := by
  rw [rectangleBarrier_re]
  exact mul_nonneg (by positivity) (by linarith [cos_ge_half_of_abs_le_half hz])

theorem rectangleBarrier_side {T B : ℝ} (hB : 0 ≤ B) {z : ℂ}
    (hx : |z.re| = T) (hy : |z.im| ≤ 1/2) : B ≤ (rectangleBarrier T B z).re := by
  have he : 1 ≤ Real.exp (z.re-T)+Real.exp (-z.re-T) := by
    rcases (le_total 0 z.re) with h | h
    · rw [abs_of_nonneg h] at hx
      rw [hx, sub_self, Real.exp_zero]
      linarith [Real.exp_pos (-T-T)]
    · rw [abs_of_nonpos h] at hx
      rw [hx, sub_self, Real.exp_zero]
      linarith [Real.exp_pos (z.re-T)]
  rw [rectangleBarrier_re]
  have hc := cos_ge_half_of_abs_le_half hy
  have hp : B ≤ 2*B*(Real.exp (z.re-T)+Real.exp (-z.re-T))*(1/2) := by nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left hc (by positivity))

theorem rectangleBarrier_center {T B : ℝ} (hB : 0 ≤ B) {z : ℂ}
    (hx : |z.re| ≤ T/2) : (rectangleBarrier T B z).re ≤ 4*B*Real.exp (-T/2) := by
  have he1 : Real.exp (z.re-T) ≤ Real.exp (-T/2) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).2])
  have he2 : Real.exp (-z.re-T) ≤ Real.exp (-T/2) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
  rw [rectangleBarrier_re]
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one z.im)
    (show 0 ≤ 2*B*(Real.exp (z.re-T)+Real.exp (-z.re-T)) by positivity)
  nlinarith

/-- Horizontal boundary bound one, vertical boundary bound `exp B`, and an
explicit exponentially small loss on the middle half of the rectangle. -/
theorem local_pl_unit_strip {f : ℂ → ℂ} {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hf : Differentiable ℂ f)
    (hhorizontal : ∀ z : ℂ, |z.re| ≤ T → |z.im| = 1/2 → ‖f z‖ ≤ 1)
    (hvertical : ∀ z : ℂ, |z.re| = T → |z.im| ≤ 1/2 → ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hzre : |z.re| ≤ T/2) (hzim : |z.im| ≤ 1/2) :
    ‖f z‖ ≤ Real.exp (4*B*Real.exp (-T/2)) := by
  let U : Set ℂ := Ioo (-T) T ×ℂ Ioo (-(1/2 : ℝ)) (1/2)
  let F : ℂ → ℂ := fun w => f w*Complex.exp (-rectangleBarrier T B w)
  have hd : Differentiable ℂ F := by
    dsimp [F, rectangleBarrier]
    fun_prop
  have hnorm (w : ℂ) : ‖F w‖ = ‖f w‖*Real.exp (-(rectangleBarrier T B w).re) := by
    simp [F, Complex.norm_exp]
  have hb : ∀ w ∈ frontier U, ‖F w‖ ≤ 1 := by
    intro w hw
    dsimp [U] at hw
    rw [frontier_reProdIm, closure_Ioo (neg_lt_self hT).ne,
      closure_Ioo (by norm_num : (-(1/2 : ℝ)) ≠ 1/2),
      frontier_Ioo (a := -T) (b := T) (neg_lt_self hT),
      frontier_Ioo (by norm_num : (-(1/2 : ℝ)) < 1/2)] at hw
    have hcases : (|w.re| ≤ T ∧ |w.im| = 1/2) ∨ (|w.re| = T ∧ |w.im| ≤ 1/2) := by
      rcases hw with hw | hw
      · left
        refine ⟨abs_le.mpr hw.1, ?_⟩
        rcases hw.2 with h | h <;> simp_all
      · right
        refine ⟨?_, abs_le.mpr hw.2⟩
        rcases hw.1 with h | h <;> simp_all [abs_of_nonneg hT.le]
    rw [hnorm]
    rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hbar := rectangleBarrier_nonneg (T := T) hB (le_of_eq hy)
      have he : Real.exp (-(rectangleBarrier T B w).re) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      exact (mul_le_mul_of_nonneg_right (hhorizontal w hx hy) (Real.exp_pos _).le).trans
        (by simpa using he)
    · have hbar := rectangleBarrier_side hB hx hy
      calc
        ‖f w‖*Real.exp (-(rectangleBarrier T B w).re) ≤
            Real.exp B*Real.exp (-(rectangleBarrier T B w).re) :=
          mul_le_mul_of_nonneg_right (hvertical w hx hy) (Real.exp_pos _).le
        _ = Real.exp (B-(rectangleBarrier T B w).re) := by rw [← Real.exp_add]; rfl
        _ ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr hbar)
  have hz : z ∈ closure U := by
    dsimp [U]
    rw [closure_reProdIm, closure_Ioo (neg_lt_self hT).ne,
      closure_Ioo (by norm_num : (-(1/2 : ℝ)) ≠ 1/2)]
    exact ⟨abs_le.mp (hzre.trans (by linarith)), abs_le.mp hzim⟩
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) hd.diffContOnCl hb hz
  rw [hnorm] at hmax
  have hn : ‖f z‖ ≤ Real.exp (rectangleBarrier T B z).re := by
    have hm := mul_le_mul_of_nonneg_right hmax (Real.exp_pos (rectangleBarrier T B z).re).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at hm
    exact hm
  exact hn.trans (Real.exp_le_exp.mpr (rectangleBarrier_center hB hzre))

/-- Rescaled upper-rectangle form, with arbitrary positive horizontal bound. -/
theorem local_pl_rectangle {f : ℂ → ℂ} {L H A B : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hA : 0 < A) (hB : 0 ≤ B)
    (hf : Differentiable ℂ f)
    (hbottom : ∀ w : ℂ, |w.re| ≤ L → w.im = 0 → ‖f w‖ ≤ A)
    (htop : ∀ w : ℂ, |w.re| ≤ L → w.im = H → ‖f w‖ ≤ A)
    (hside : ∀ w : ℂ, |w.re| = L → 0 ≤ w.im → w.im ≤ H → ‖f w‖ ≤ A*Real.exp B)
    {z : ℂ} (hx : |z.re| ≤ L/2) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ H) :
    ‖f z‖ ≤ A*Real.exp (4*B*Real.exp (-L/(2*H))) := by
  let g : ℂ → ℂ := fun w => f ((H : ℂ)*w+(H/2 : ℝ)*I)/(A : ℂ)
  have hc (w : ℂ) : ((H : ℂ)*w+(H/2 : ℝ)*I).re = H*w.re ∧
      ((H : ℂ)*w+(H/2 : ℝ)*I).im = H*(w.im+1/2) := by
    constructor <;> simp <;> ring
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hgn (w : ℂ) : ‖g w‖ = ‖f ((H : ℂ)*w+(H/2 : ℝ)*I)‖/A := by
    simp [g, abs_of_pos hA]
  have hb (w : ℂ) (hw : |w.re| ≤ L/H) : |((H : ℂ)*w+(H/2 : ℝ)*I).re| ≤ L := by
    rw [(hc w).1, abs_mul, abs_of_pos hH]
    have hh := mul_le_mul_of_nonneg_left hw hH.le
    have he : H*(L/H) = L := by field_simp
    rwa [he] at hh
  have hv (w : ℂ) (hw : |w.im| ≤ 1/2) :
      0 ≤ ((H : ℂ)*w+(H/2 : ℝ)*I).im ∧ ((H : ℂ)*w+(H/2 : ℝ)*I).im ≤ H := by
    rw [(hc w).2]
    constructor <;> nlinarith [(abs_le.mp hw).1, (abs_le.mp hw).2]
  let w : ℂ := (z-(H/2 : ℝ)*I)/(H : ℂ)
  have hwre : w.re = z.re/H := by dsimp [w]; simp [Complex.div_ofReal_re]
  have hwim : w.im = z.im/H-1/2 := by
    dsimp [w]
    simp only [Complex.div_ofReal_im, sub_im, mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, mul_zero, add_zero]
    field_simp
  have hwr : |w.re| ≤ (L/H)/2 := by
    rw [hwre, abs_div, abs_of_pos hH]
    calc
      |z.re|/H ≤ (L/2)/H := div_le_div_of_nonneg_right hx hH.le
      _ = (L/H)/2 := by ring
  have hwi : |w.im| ≤ 1/2 := by
    rw [hwim]
    apply abs_le.mpr
    constructor
    · have hh := div_nonneg hy0 hH.le; linarith
    · have hh := (div_le_one hH).mpr hy1; linarith
  have hresult := local_pl_unit_strip (div_pos hL hH) hB hg (fun u hu hhu => by
      rw [hgn, div_le_one hA]
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1/2)).mp hhu with hh | hh
      · apply htop _ (hb u hu)
        rw [(hc u).2, hh]
        ring
      · apply hbottom _ (hb u hu)
        rw [(hc u).2, hh]
        ring)
    (fun u hu hhu => by
      rw [hgn]
      apply (div_le_iff₀ hA).mpr
      have hh := hside ((H : ℂ)*u+(H/2 : ℝ)*I) (by
        rw [(hc u).1, abs_mul, abs_of_pos hH, hu]
        field_simp) (hv u hhu).1 (hv u hhu).2
      simpa only [mul_comm A] using hh) hwr hwi
  have hw : (H : ℂ)*w+(H/2 : ℝ)*I = z := by
    have hn : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    dsimp [w]
    field_simp [hn]
    ring
  rw [hgn, hw] at hresult
  have hm := (div_le_iff₀ hA).mp hresult
  have he : -(L/H)/2 = -L/(2*H) := by ring
  simpa only [he, mul_comm A] using hm

/-- Removing a prescribed exponential growth on the upper edge gives the same
exponential type in the middle of the rectangle. -/
theorem local_exponential_growth {f : ℂ → ℂ} {L H A B ω : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hA : 0 < A) (hB : 0 ≤ B) (hω : 0 ≤ ω)
    (hf : Differentiable ℂ f)
    (hbottom : ∀ w : ℂ, |w.re| ≤ L → w.im = 0 → ‖f w‖ ≤ A)
    (htop : ∀ w : ℂ, |w.re| ≤ L → w.im = H → ‖f w‖ ≤ A*Real.exp (ω*H))
    (hside : ∀ w : ℂ, |w.re| = L → 0 ≤ w.im → w.im ≤ H → ‖f w‖ ≤ A*Real.exp B)
    {z : ℂ} (hx : |z.re| ≤ L/2) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ H) :
    ‖f z‖ ≤ A*Real.exp (4*B*Real.exp (-L/(2*H)))*Real.exp (ω*z.im) := by
  let g : ℂ → ℂ := fun w => f w*Complex.exp (I*ω*w)
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hn (w : ℂ) : ‖g w‖ = ‖f w‖*Real.exp (-ω*w.im) := by
    simp [g, Complex.norm_exp]
  have hb (w : ℂ) (hw : |w.re| ≤ L) (hi : w.im = 0) : ‖g w‖ ≤ A := by
    rw [hn, hi]
    simpa using hbottom w hw hi
  have ht (w : ℂ) (hw : |w.re| ≤ L) (hi : w.im = H) : ‖g w‖ ≤ A := by
    rw [hn, hi]
    have hh := mul_le_mul_of_nonneg_right (htop w hw hi) (Real.exp_pos (-ω*H)).le
    simpa only [mul_assoc, ← Real.exp_add, mul_neg, neg_mul, add_neg_cancel,
      Real.exp_zero, mul_one] using hh
  have hs (w : ℂ) (hw : |w.re| = L) (hi0 : 0 ≤ w.im) (hi1 : w.im ≤ H) :
      ‖g w‖ ≤ A*Real.exp B := by
    rw [hn]
    have he : Real.exp (-ω*w.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      _ ≤ ‖f w‖*1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ _ := by simpa using hside w hw hi0 hi1
  have hp := local_pl_rectangle hL hH hA hB hg hb ht hs hx hy0 hy1
  rw [hn] at hp
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (ω*z.im)).le
  simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh

end Erdos1132
