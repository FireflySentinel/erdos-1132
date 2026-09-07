import Erdos1132.Counterexample.AmplitudePhase
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Smooth inverse phase coordinates

The coordinate change `t - ε ψ(t)` has a jointly smooth inverse for small
`ε`. At `ε = 0` the inverse is the identity.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Erdos1132.Counterexample

def phaseMap (ψ : ℝ → ℝ) (ε t : ℝ) : ℝ := t - ε * ψ t

def phaseInverse (ψ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  Function.invFun (phaseMap ψ ε)

theorem phaseMap_hasDerivAt {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (ε t : ℝ) :
    HasDerivAt (phaseMap ψ ε) (1 - ε * deriv ψ t) t := by
  simpa [phaseMap] using! (hasDerivAt_id t).sub ((hψ t).hasDerivAt.const_mul ε)

theorem phaseMap_strictMono {ψ : ℝ → ℝ} {B ε : ℝ}
    (hψ : Differentiable ℝ ψ) (hB : ∀ t, |deriv ψ t| ≤ B)
    (hε : |ε| * B < 1) : StrictMono (phaseMap ψ ε) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(phaseMap_hasDerivAt hψ ε t).deriv]
  have h := (le_abs_self (ε * deriv ψ t)).trans
      ((abs_mul ε _).trans_le (mul_le_mul_of_nonneg_left (hB t) (abs_nonneg ε)))
  linarith

theorem phaseMap_surjective {ψ : ℝ → ℝ} {B : ℝ}
    (hψ : Continuous ψ) (hB : ∀ t, |ψ t| ≤ B) (ε : ℝ) :
    Function.Surjective (phaseMap ψ ε) := by
  intro s
  have hB0 : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hB 0)
  let a := s - |ε| * B - 1
  let b := s + |ε| * B + 1
  have hab : a ≤ b := by dsimp [a, b]; nlinarith [mul_nonneg (abs_nonneg ε) hB0]
  have hb (t : ℝ) : |ε * ψ t| ≤ |ε| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t) (abs_nonneg ε)
  have hc : Continuous (phaseMap ψ ε) := continuous_id.sub (continuous_const.mul hψ)
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab hc.continuousOn
    (show s ∈ Icc (phaseMap ψ ε a) (phaseMap ψ ε b) by
      have ha' := (abs_le.mp (hb a)).1
      have hb' := (abs_le.mp (hb b)).2
      dsimp [phaseMap, a, b] at *
      constructor <;> linarith)
  exact ⟨t, ht⟩

theorem phaseInverse_right {ψ : ℝ → ℝ} {B : ℝ}
    (hψ : Continuous ψ) (hB : ∀ t, |ψ t| ≤ B) (ε s : ℝ) :
    phaseMap ψ ε (phaseInverse ψ ε s) = s :=
  Function.rightInverse_invFun (phaseMap_surjective hψ hB ε) s

theorem phaseInverse_left {ψ : ℝ → ℝ} {B ε : ℝ}
    (hψ : Differentiable ℝ ψ) (hB : ∀ t, |deriv ψ t| ≤ B)
    (hε : |ε| * B < 1) (t : ℝ) :
    phaseInverse ψ ε (phaseMap ψ ε t) = t :=
  Function.leftInverse_invFun (phaseMap_strictMono hψ hB hε).injective t

@[simp] theorem phaseInverse_zero (ψ : ℝ → ℝ) (s : ℝ) :
    phaseInverse ψ 0 s = s := by
  have h : phaseMap ψ 0 = id := by ext t; simp [phaseMap]
  simpa only [phaseInverse, h, id_eq] using Function.leftInverse_invFun Function.injective_id s

/-- Joint smoothness in the perturbation parameter and the phase coordinate. -/
theorem phaseInverse_contDiffAt {ψ : ℝ → ℝ} {B : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) {p : ℝ × ℝ}
    (hp : |p.1| * B < 1) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × ℝ => phaseInverse ψ q.1 q.2) p := by
  let t := phaseInverse ψ p.1 p.2
  let g : (ℝ × ℝ) × ℝ → ℝ := fun q => q.2 - q.1.1 * ψ q.2 - q.1.2
  have hgc : ContDiff ℝ ⊤ g := by dsimp [g]; fun_prop
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hbase : g (p, t) = 0 := by
    exact sub_eq_zero.mpr (phaseInverse_right hψ.continuous hval p.1 p.2)
  let d := 1 - p.1 * deriv ψ t
  have hd : 0 < d := by
    have h := (le_abs_self (p.1 * deriv ψ t)).trans
      ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hder t) (abs_nonneg _)))
    dsimp [d]
    linarith
  let D := fderiv ℝ g (p, t) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
  have hD1 : D 1 = d := by
    have hc := (hgc.differentiable (by simp) (p, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t p).prodMk (hasDerivAt_id t))
    have he := ((phaseMap_hasDerivAt hψd p.1 t).sub_const p.2)
    exact hc.unique he
  have hDx (x : ℝ) : D x = d * x := by
    calc
      D x = D (x • (1 : ℝ)) := by simp
      _ = x • D 1 := D.map_smul x 1
      _ = d * x := by rw [hD1]; simp [smul_eq_mul, mul_comm]
  have hinv : D.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hDx, hd.ne']
    · ext
      simp [hDx, hd.ne']
  let φ := hgc.contDiffAt.implicitFunction (by simp : (⊤ : ℕ∞ω) ≠ 0) hinv
  have hφ : ContDiffAt ℝ ⊤ φ p := hgc.contDiffAt.contDiffAt_implicitFunction _ hinv
  have heq : (fun q : ℝ × ℝ => phaseInverse ψ q.1 q.2) =ᶠ[𝓝 p] φ := by
    have hopen : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |q.1| * B < 1 :=
      (continuous_fst.abs.mul continuous_const).continuousAt.eventually_lt_const hp
    filter_upwards [hopen, hgc.contDiffAt.eventually_apply_implicitFunction
      (by simp : (⊤ : ℕ∞ω) ≠ 0) hinv] with q hq hqφ
    have hqeq : phaseMap ψ q.1 (φ q) = q.2 := by
      change g (q, φ q) = g (p, t) at hqφ
      rw [hbase] at hqφ
      exact sub_eq_zero.mp hqφ
    apply (phaseMap_strictMono hψd hder hq).injective
    rw [phaseInverse_right hψ.continuous hval, hqeq]
  exact hφ.congr_of_eventuallyEq heq

theorem phaseInverse_hasDerivAt {ψ : ℝ → ℝ} {B ε : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |ε| * B < 1) (s : ℝ) :
    HasDerivAt (phaseInverse ψ ε)
      (1 - ε * deriv ψ (phaseInverse ψ ε s))⁻¹ s := by
  let t := phaseInverse ψ ε s
  have hψd := hψ.differentiable (by simp)
  have hmap : ContDiff ℝ ⊤ (phaseMap ψ ε) := contDiff_id.sub (contDiff_const.mul hψ)
  have hd : HasStrictDerivAt (phaseMap ψ ε) (1 - ε * deriv ψ t) t :=
    hmap.contDiffAt.hasStrictDerivAt' (phaseMap_hasDerivAt hψd ε t) (by simp)
  have hne : 1 - ε * deriv ψ t ≠ 0 := by
    have h := (le_abs_self (ε * deriv ψ t)).trans
      ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hder t) (abs_nonneg _)))
    linarith
  have hi := hd.to_local_left_inverse hne
    (Filter.Eventually.of_forall (phaseInverse_left hψd hder hε))
  simpa only [t, phaseInverse_right hψ.continuous hval] using hi.hasDerivAt

theorem phaseInverse_strictMono {ψ : ℝ → ℝ} {B ε : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |ε| * B < 1) :
    StrictMono (phaseInverse ψ ε) := by
  intro s t hst
  apply (phaseMap_strictMono (hψ.differentiable (by simp)) hder hε).lt_iff_lt.mp
  simpa only [phaseInverse_right hψ.continuous hval] using hst

theorem phaseInverse_endpoint {ψ : ℝ → ℝ} {B ε t : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hder : ∀ u, |deriv ψ u| ≤ B)
    (hε : |ε| * B < 1) (ht : ψ t = 0) : phaseInverse ψ ε t = t := by
  simpa [phaseMap, ht] using
    phaseInverse_left (hψ.differentiable (by simp)) hder hε t

theorem phaseInverse_mem_Icc {ψ : ℝ → ℝ} {B ε s : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |ε| * B < 1)
    (h0 : ψ 0 = 0) (hπ : ψ Real.pi = 0) (hs : s ∈ Icc 0 Real.pi) :
    phaseInverse ψ ε s ∈ Icc 0 Real.pi := by
  have hm := (phaseInverse_strictMono hψ hval hder hε).monotone
  constructor
  · simpa only [phaseInverse_endpoint hψ hder hε h0] using hm hs.1
  · simpa only [phaseInverse_endpoint hψ hder hε hπ] using hm hs.2

def phaseCoordinate (ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.cos (phaseInverse ψ p.1 p.2)

@[simp] theorem phaseCoordinate_zero (ψ : ℝ → ℝ) (s : ℝ) :
    phaseCoordinate ψ (0, s) = Real.cos s := by simp [phaseCoordinate]

theorem phaseCoordinate_contDiffAt {ψ : ℝ → ℝ} {B : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) {p : ℝ × ℝ}
    (hp : |p.1| * B < 1) : ContDiffAt ℝ ⊤ (phaseCoordinate ψ) p :=
  (phaseInverse_contDiffAt hψ hval hder hp).cos

theorem phaseCoordinate_hasDerivAt {ψ : ℝ → ℝ} {B ε : ℝ}
    (hψ : ContDiff ℝ ⊤ ψ) (hval : ∀ t, |ψ t| ≤ B)
    (hder : ∀ t, |deriv ψ t| ≤ B) (hε : |ε| * B < 1) (s : ℝ) :
    HasDerivAt (fun t => phaseCoordinate ψ (ε, t))
      (-Real.sin (phaseInverse ψ ε s) / (1 - ε * deriv ψ (phaseInverse ψ ε s))) s := by
  simpa only [phaseCoordinate, div_eq_mul_inv] using
    (phaseInverse_hasDerivAt hψ hval hder hε s).cos

end Erdos1132.Counterexample
