import Erdos1132.Counterexample.PhaseInverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform derivative control of the inverse coordinates

Partial derivatives in the second variable retain joint smoothness. Compactness
then gives uniform convergence of every fixed derivative order as `ε → 0`.

Paper: §7.4, the amplitude lemma and polynomial approximation.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

def coordinateDeriv (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (0, 1)

def iteratedCoordinateDeriv (k : ℕ) (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  coordinateDeriv^[k] f

theorem coordinateDeriv_contDiffAt {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ ⊤ f p) : ContDiffAt ℝ ⊤ (coordinateDeriv f) p :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem iteratedCoordinateDeriv_contDiffAt {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ ⊤ f p) (k : ℕ) :
    ContDiffAt ℝ ⊤ (iteratedCoordinateDeriv k f) p := by
  induction k with
  | zero => exact hf
  | succ k hk =>
    simpa only [iteratedCoordinateDeriv, Function.iterate_succ_apply'] using
      coordinateDeriv_contDiffAt hk

theorem coordinateDeriv_eq_deriv {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    coordinateDeriv f p = deriv (fun t => f (p.1, t)) p.2 := by
  exact (hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv.symm

theorem iteratedCoordinateDeriv_eq_iteratedDeriv {f : ℝ × ℝ → ℝ} {ε : ℝ}
    (hf : ∀ t : ℝ, ContDiffAt ℝ ⊤ f (ε, t)) (k : ℕ) (t : ℝ) :
    iteratedCoordinateDeriv k f (ε, t) = iteratedDeriv k (fun s => f (ε, s)) t := by
  induction k generalizing t with
  | zero => simp [iteratedCoordinateDeriv]
  | succ k hk =>
    rw [iteratedCoordinateDeriv, Function.iterate_succ_apply']
    change coordinateDeriv (iteratedCoordinateDeriv k f) (ε, t) = _
    rw [coordinateDeriv_eq_deriv
      ((iteratedCoordinateDeriv_contDiffAt (hf t) k).differentiableAt (by simp))]
    change deriv (fun s => iteratedCoordinateDeriv k f (ε, s)) t = _
    simp_rw [hk, iteratedDeriv_succ]

/-- Uniform convergence of all fixed derivative orders of the inverse
coordinate on the complete angle interval, including its endpoints. -/
theorem phaseCoordinate_derivatives_tendstoUniformlyOn {ψ : ℝ → ℝ} {B : ℝ}
    (hB : 0 < B) (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (k : ℕ) :
    TendstoUniformlyOn
      (fun ε : ℝ => iteratedDeriv k (fun t => phaseCoordinate ψ (ε, t)))
      (iteratedDeriv k Real.cos) (𝓝 0) (Icc 0 Real.pi) := by
  let δ : ℝ := 1 / (2 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ * B < 1 := by
    dsimp [δ]
    have hd : 0 < 2 * (B + 1) := by positivity
    rw [one_div_mul_eq_div, div_lt_iff₀ hd]
    linarith
  have hstrip {ε : ℝ} (hε : ε ∈ Icc (-δ) δ) : |ε| * B < 1 :=
    (mul_le_mul_of_nonneg_right (abs_le.mpr hε) hB.le).trans_lt hsmall
  let F := iteratedCoordinateDeriv k (phaseCoordinate ψ)
  have hc : ContinuousOn F ((Icc (-δ) δ) ×ˢ (Icc 0 Real.pi)) := by
    intro p hp
    exact (iteratedCoordinateDeriv_contDiffAt
      (phaseCoordinate_contDiffAt hψ hval hder (hstrip hp.1)) k).continuousAt.continuousWithinAt
  have hu := ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc)
  have hz : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hlim : TendstoUniformlyOn (fun ε t => F (ε, t)) (fun t => F (0, t))
      (𝓝 0) (Icc 0 Real.pi) := by
    have hnh : Icc (-δ) δ ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hδ
    simpa only [nhdsWithin_eq_nhds.mpr hnh] using
      (hu.tendstoUniformlyOn (F := fun ε t => F (ε, t)) hz)
  have hident (ε : ℝ) (hε : ε ∈ Icc (-δ) δ) (t : ℝ) :
      F (ε, t) = iteratedDeriv k (fun s => phaseCoordinate ψ (ε, s)) t :=
    iteratedCoordinateDeriv_eq_iteratedDeriv
      (fun s => phaseCoordinate_contDiffAt hψ hval hder (hstrip hε)) k t
  have hzero : (fun t => F (0, t)) = iteratedDeriv k Real.cos := by
    ext t
    rw [hident 0 hz]
    simp only [phaseCoordinate_zero]
  rw [hzero] at hlim
  apply hlim.congr
  filter_upwards [Icc_mem_nhds (by linarith : -δ < 0) hδ] with ε hε
  intro t _
  exact hident ε hε t

end Erdos1132.Counterexample
