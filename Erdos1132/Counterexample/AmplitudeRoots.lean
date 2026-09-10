import Erdos1132.Counterexample.AmplitudePhase
import Erdos1132.Interpolation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Interior roots and derivative weights of the amplitude polynomial

The increasing phase gives all `n` roots and the exact derivative formula
in (7.20). The resulting row has distinct nodes in the open interval.

Companion note: §3, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set Polynomial Filter
open scoped BigOperators

namespace Erdos1132.Counterexample

theorem oscillatory_root_derivative {P : ℝ[X]} {w ψ : ℝ → ℝ} {n : ℕ} {θ : ℝ}
    (hw : DifferentiableAt ℝ w θ) (hψ : DifferentiableAt ℝ ψ θ)
    (heq : ∀ t, P.eval (Real.cos t) = w t * Real.cos (n * t - ψ t))
    (hc : Real.cos (n * θ - ψ θ) = 0)
    (hw0 : 0 ≤ w θ) (hphase : 0 < (n : ℝ) - deriv ψ θ)
    (hsin : 0 < Real.sin θ) :
    |P.derivative.eval (Real.cos θ)| = w θ * (n - deriv ψ θ) / Real.sin θ := by
  have hid : (fun t => P.eval (Real.cos t)) =
      (fun t => w t * Real.cos (n * t - ψ t)) := funext heq
  have hleft := (P.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
  have hright := hw.hasDerivAt.mul
    (((hasDerivAt_id θ).const_mul (n : ℝ)).sub hψ.hasDerivAt).cos
  change HasDerivAt (fun t => P.eval (Real.cos t)) _ θ at hleft
  rw [hid] at hleft
  have he := hleft.unique hright
  have hsinphase : |Real.sin (n * θ - ψ θ)| = 1 := by
    have h := Real.sin_sq_add_cos_sq (n * θ - ψ θ)
    rw [hc] at h
    nlinarith [sq_abs (Real.sin (n * θ - ψ θ)), abs_nonneg (Real.sin (n * θ - ψ θ))]
  simp only [Pi.sub_apply, id_eq, mul_one] at he
  have heabs := congrArg abs he
  simp only [hc, mul_zero, zero_add, abs_mul, abs_neg,
    abs_of_pos hsin, abs_of_nonneg hw0, hsinphase, abs_of_pos hphase, one_mul] at heabs
  exact (eq_div_iff hsin.ne').mpr heabs

/-- An increasing phase from `0` to `nπ` has an interior preimage of each
half-integer phase value; these preimages are pairwise distinct. -/
theorem exists_phase_angles {ψ : ℝ → ℝ} {n : ℕ}
    (hψ : Differentiable ℝ ψ) (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0)
    (hderiv : ∀ θ ∈ Icc 0 Real.pi, deriv ψ θ < n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, θ i ∈ Ioo 0 Real.pi) ∧ Function.Injective θ ∧
      ∀ i, (n : ℝ) * θ i - ψ (θ i) = ((i : ℝ) + 1 / 2) * Real.pi := by
  let φ : ℝ → ℝ := fun t => n * t - ψ t
  have hd (t : ℝ) : HasDerivAt φ (n - deriv ψ t) t :=
    by simpa [φ] using! ((hasDerivAt_id t).const_mul (n : ℝ)).sub (hψ t).hasDerivAt
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hmono : StrictMonoOn φ (Icc 0 Real.pi) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hφc.continuousOn (fun t ht => by
      rw [(hd t).deriv]
      exact sub_pos.mpr (hderiv t (interior_subset ht)))
  have hφ0 : φ 0 = 0 := by simp [φ, h0]
  have hφπ : φ Real.pi = n * Real.pi := by simp [φ, hπ]
  have hex (i : Fin n) : ∃ t ∈ Ioo 0 Real.pi,
      φ t = ((i : ℝ) + 1 / 2) * Real.pi := by
    have hi : (i : ℝ) < n := by exact_mod_cast i.isLt
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have ha : 0 < ((i : ℝ) + 1 / 2) * Real.pi := by positivity
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast (show i.val + 1 ≤ n by omega)
    have hb : ((i : ℝ) + 1 / 2) * Real.pi < n * Real.pi :=
      mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc Real.pi_pos.le hφc.continuousOn
      (show ((i : ℝ) + 1 / 2) * Real.pi ∈ Icc (φ 0) (φ Real.pi) by
        rw [hφ0, hφπ]; exact ⟨ha.le, hb.le⟩)
    have ht0 : t ≠ 0 := by intro hz; rw [hz, hφ0] at he; linarith
    have htπ : t ≠ Real.pi := by intro hz; rw [hz, hφπ] at he; linarith
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htπ⟩, he⟩
  choose θ hθ he using hex
  refine ⟨θ, hθ, ?_, he⟩
  intro i j hij
  have heq := congrArg φ hij
  rw [he i, he j] at heq
  have heq' : (i : ℝ) = j := by nlinarith [Real.pi_pos]
  exact Fin.ext (by exact_mod_cast heq')

/-- Every zero-free amplitude supplies all interior simple roots for every
sufficiently large degree, together with their exact derivative weights. -/
theorem eventually_exists_amplitude_roots (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ⊤ ψ ∧ ψ 0 = 0 ∧ ψ Real.pi = 0 ∧
      (∀ n : ℕ, h.natDegree < n → ∀ t : ℝ,
        (amplitudePolynomial h n).eval (Real.cos t) =
          ‖(complexPolynomial h).eval (circlePoint t)‖ * Real.cos (n * t - ψ t)) ∧
      ∀ᶠ n : ℕ in atTop, h.natDegree < n ∧
        ∃ θ : Fin n → ℝ,
          (∀ i, θ i ∈ Ioo 0 Real.pi) ∧ Function.Injective (fun i => Real.cos (θ i)) ∧
          (∀ i, (n : ℝ) * θ i - ψ (θ i) = ((i : ℝ) + 1 / 2) * Real.pi) ∧
          (∀ i, (amplitudePolynomial h n).eval (Real.cos (θ i)) = 0) ∧
          (∀ i, 0 < (n : ℝ) - deriv ψ (θ i)) ∧
          (∀ i, |(amplitudePolynomial h n).derivative.eval (Real.cos (θ i))| =
            ‖(complexPolynomial h).eval (circlePoint (θ i))‖ *
              (n - deriv ψ (θ i)) / Real.sin (θ i)) ∧
          ∀ i, (amplitudePolynomial h n).derivative.eval (Real.cos (θ i)) ≠ 0 := by
  obtain ⟨ψ, hψc, hψ0, hψπ, _, heq⟩ := exists_amplitude_phase h hzero hpos
  have hψ : Differentiable ℝ ψ := hψc.differentiable (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hψc.continuous_deriv (by simp)).continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine ⟨ψ, hψc, hψ0, hψπ, heq, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop h.natDegree] with n hn hdeg
  have hbound : ∀ t ∈ Icc 0 Real.pi, deriv ψ t < n := by
    intro t ht
    exact (hB (mem_image_of_mem _ ht)).trans_lt
      (hN.trans_le (by exact_mod_cast hn))
  obtain ⟨θ, hθ, hinj, hphase⟩ := exists_phase_angles hψ hψ0 hψπ hbound
  have hc (i : Fin n) : Real.cos (n * θ i - ψ (θ i)) = 0 := by
    rw [hphase, add_mul]
    rw [show (i : ℝ) * Real.pi + (1 / 2 : ℝ) * Real.pi =
      Real.pi / 2 + i.val * Real.pi by ring, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero]
  have hroot (i : Fin n) : (amplitudePolynomial h n).eval (Real.cos (θ i)) = 0 := by
    rw [heq n hdeg, hc, mul_zero]
  have hp (i : Fin n) : 0 < (n : ℝ) - deriv ψ (θ i) :=
    sub_pos.mpr (hbound _ ⟨(hθ i).1.le, (hθ i).2.le⟩)
  have hs (i : Fin n) : 0 < Real.sin (θ i) := Real.sin_pos_of_mem_Ioo (hθ i)
  have hw0 (i : Fin n) : 0 < ‖(complexPolynomial h).eval (circlePoint (θ i))‖ :=
    norm_pos_iff.mpr (hzero _ (by simp))
  have hweight (i : Fin n) := oscillatory_root_derivative
    ((((complexPolynomial h).hasDerivAt _).comp _ (hasDerivAt_circlePoint (θ i))).differentiableAt.norm ℝ
      (hzero _ (by simp))) (hψ _) (heq n hdeg) (hc i) (hw0 i).le (hp i) (hs i)
  refine ⟨hdeg, θ, hθ, ?_, hphase, hroot, hp, hweight, ?_⟩
  · intro i j hij
    exact hinj (Real.strictAntiOn_cos.injOn
      ⟨(hθ i).1.le, (hθ i).2.le⟩ ⟨(hθ j).1.le, (hθ j).2.le⟩ hij)
  · intro i
    exact abs_pos.mp (by rw [hweight]; exact div_pos (mul_pos (hw0 i) (hp i)) (hs i))

end Erdos1132.Counterexample
