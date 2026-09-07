import Erdos1132.Shared.Cayley
import Erdos1132.Shared.Cauchy
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-! # Harmonic measure of a boundary interval

Paper: Shared analytic tools for §§2–6.
-/

noncomputable section

open Complex Filter InnerProductSpace
open scoped Topology

namespace Erdos1132

def intervalHarmonic (a b : ℝ) (z : ℂ) : ℝ := ((z - a) / (z - b)).arg / Real.pi

theorem interval_quotient_im (a b : ℝ) (z : ℂ) :
    ((z - a) / (z - b)).im = (a - b) * z.im / normSq (z - b) := by
  simp [div_im]
  ring

theorem interval_quotient_im_pos {a b : ℝ} (hab : a < b) {z : ℂ} (hz : z.im < 0) :
    0 < ((z - a) / (z - b)).im := by
  rw [interval_quotient_im]
  have hzb : z - (b : ℂ) ≠ 0 := by
    intro he
    have := congrArg Complex.im he
    simp at this
    linarith
  exact div_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hab) hz) (normSq_pos.mpr hzb)

theorem abs_intervalHarmonic_le_one (a b : ℝ) (z : ℂ) : |intervalHarmonic a b z| ≤ 1 := by
  rw [intervalHarmonic, abs_div, abs_of_pos Real.pi_pos]
  exact (div_le_one Real.pi_pos).mpr (abs_arg_le_pi _)

theorem harmonicAt_intervalHarmonic_comp {F : ℂ → ℂ} {z : ℂ} {a b : ℝ}
    (hab : a < b) (hF : AnalyticAt ℂ F z) (hi : (F z).im < 0) :
    HarmonicAt (fun w => intervalHarmonic a b (F w)) z := by
  have hn : F z - (b : ℂ) ≠ 0 := by
    intro he
    have := congrArg Complex.im he
    simp at this
    linarith
  have hq : AnalyticAt ℂ (fun w => (F w - a) / (F w - b)) z := by
    fun_prop (disch := exact hn)
  have hs : (F z - a) / (F z - b) ∈ slitPlane :=
    Or.inr (ne_of_gt (interval_quotient_im_pos hab hi))
  have hh := (hq.clog hs).harmonicAt_im
  convert! hh.const_smul (c := Real.pi⁻¹) using 1
  funext w
  simp [intervalHarmonic, Complex.log_im, div_eq_mul_inv, mul_comm]

theorem tendsto_intervalHarmonic_real {a b t : ℝ} (hab : a < b)
    (hta : t ≠ a) (htb : t ≠ b) {f : ℕ → ℂ}
    (hf : Tendsto f atTop (𝓝 (t : ℂ))) (hi : ∀ n, (f n).im < 0) :
    Tendsto (fun n => intervalHarmonic a b (f n)) atTop
      (𝓝 (if a < t ∧ t < b then 1 else 0)) := by
  have hq := (hf.sub_const (a : ℂ)).div (hf.sub_const (b : ℂ))
    (by exact_mod_cast sub_ne_zero.mpr htb)
  have hq' : Tendsto (fun n => (f n - a) / (f n - b)) atTop
      (𝓝 (((t - a) / (t - b) : ℝ) : ℂ)) := by
    convert! hq using 1
    simp
  by_cases ht : a < t ∧ t < b
  · have hneg : (t - a) / (t - b) < 0 :=
      div_neg_of_pos_of_neg (sub_pos.mpr ht.1) (sub_neg.mpr ht.2)
    have hwithin : Tendsto (fun n => (f n - a) / (f n - b)) atTop
        (𝓝[{z : ℂ | 0 ≤ z.im}] (((t - a) / (t - b) : ℝ) : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hq', .of_forall fun n => (interval_quotient_im_pos hab (hi n)).le⟩
    have harg := (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hneg rfl).comp hwithin
    simpa [intervalHarmonic, ht, Real.pi_ne_zero] using harg.div_const Real.pi
  · have hpos : 0 < (t - a) / (t - b) := by
      by_cases h : t < a
      · exact div_pos_of_neg_of_neg (sub_neg.mpr h) (sub_neg.mpr (h.trans hab))
      · have h₁ : a < t := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hta)
        have h₂ : b < t := lt_of_le_of_ne (not_lt.mp (fun h' => ht ⟨h₁, h'⟩)) (Ne.symm htb)
        exact div_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)
    have harg := (continuousAt_arg (Or.inl hpos)).tendsto.comp hq'
    simpa only [intervalHarmonic, if_neg ht, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      arg_ofReal_of_nonneg hpos.le, zero_div, Function.comp_def] using harg.div_const Real.pi

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem cauchy_im_neg {z : ℂ} (hz : 0 < z.im) : (μ.cauchy z).im < 0 := by
  have h := μ.neg_im_cauchy z.im z.re
  rw [Complex.re_add_im] at h
  linarith [μ.gamma_pos hz z.re]

theorem analyticAt_cauchy {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
    AnalyticAt ℂ μ.cauchy z := by
  unfold cauchy
  fun_prop (disch := exact sub_ne_zero.mpr (hz _))

theorem analyticAt_cauchy_upper {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ μ.cauchy z := by
  apply μ.analyticAt_cauchy
  intro i hi
  simp [hi] at hz

end AtomicProbability

end Erdos1132
