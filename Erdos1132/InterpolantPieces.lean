import Erdos1132.ComplexInterpolant
import Erdos1132.DerivativeJumps
import Mathlib.Topology.Order.IntermediateValue

/-! # Polynomial pieces of the Lebesgue function between interpolation nodes -/

noncomputable section
open Set Filter Polynomial Finset
open scoped Topology BigOperators
namespace Erdos1132

theorem continuous_nonzero_sign_on_interval {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a < b) (hnz : ∀ x ∈ Ioo a b, f x ≠ 0) :
    ∃ s : ℝ, |s| ≤ 1 ∧ ∀ x ∈ Icc a b, s*f x = |f x| := by
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := by constructor <;> dsimp [m] <;> linarith
  have hsign : ∃ s : ℝ, |s| ≤ 1 ∧ ∀ x ∈ Ioo a b, s*f x = |f x| := by
    rcases lt_or_gt_of_ne (hnz m hm) with hneg | hpos
    · refine ⟨-1, by norm_num, ?_⟩
      intro x hx
      have hfx : f x < 0 := by
        by_contra hh
        have hh' := le_of_not_gt hh
        obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value hm hx hf.continuousOn
          (show (0:ℝ) ∈ Icc (f m) (f x) from ⟨hneg.le, hh'⟩)
        exact hnz z hz hzero
      rw [abs_of_neg hfx]
      ring
    · refine ⟨1, by norm_num, ?_⟩
      intro x hx
      have hfx : 0 < f x := by
        by_contra hh
        have hh' := le_of_not_gt hh
        obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value hx hm hf.continuousOn
          (show (0:ℝ) ∈ Icc (f x) (f m) from ⟨hh', hpos.le⟩)
        exact hnz z hz hzero
      rw [abs_of_pos hfx]
      ring
  obtain ⟨s, hs, hsi⟩ := hsign
  refine ⟨s, hs, ?_⟩
  have hh : closure (Ioo a b) ⊆ {x | s*f x = |f x|} :=
    closure_minimal hsi (isClosed_eq (continuous_const.mul hf) hf.abs)
  rw [closure_Ioo hab.ne] at hh
  exact hh

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem cardinal_ne_zero_off_nodes {x : ℝ} (hx : ∀ i, x ≠ X.point i) (i : Fin n) :
    (X.cardinal i).eval x ≠ 0 := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (X.cardinal_mul_linear i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  have hPn : X.nodePolynomial.eval x ≠ 0 := Lagrange.eval_nodal_not_at_node (fun j _ => hx j)
  have hr := mul_ne_zero (X.weight_ne_zero i) hPn
  rw [← h] at hr
  exact (mul_ne_zero_iff.mp hr).2

/-- On each closed gap without an interior interpolation node, the Lebesgue
function is one bounded-data interpolation polynomial. -/
theorem exists_interpolant_piece {a b : ℝ} (hab : a < b)
    (hgap : ∀ i, X.point i ∉ Ioo a b) :
    ∃ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) ∧
      ∀ x ∈ Icc a b, (X.interpolant v).eval x = X.lebesgue x := by
  have h (i : Fin n) := continuous_nonzero_sign_on_interval (X.cardinal i).continuous hab
    (fun x hx => X.cardinal_ne_zero_off_nodes (fun j hj => hgap j (hj ▸ hx)) i)
  choose v hv he using h
  refine ⟨v, hv, ?_⟩
  intro x hx
  simp only [interpolant, lebesgue, eval_finsetSum, eval_mul, eval_C]
  exact sum_congr rfl (fun i _ => he i x hx)

theorem piece_derivative_right {a b : ℝ} (hab : a < b) {v : Fin n → ℝ}
    (he : ∀ x ∈ Icc a b, (X.interpolant v).eval x = X.lebesgue x) :
    ((X.interpolant v).derivative).eval a = derivWithin X.lebesgue (Ioi a) a := by
  have hh : X.lebesgue =ᶠ[𝓝[>] a] (fun x => (X.interpolant v).eval x) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)]
      with x hxa hxb
    exact (he x ⟨hxa.le, hxb.le⟩).symm
  have hd := ((X.interpolant v).hasDerivAt a).hasDerivWithinAt.congr_of_eventuallyEq hh
    (he a ⟨le_rfl, hab.le⟩).symm
  exact (hd.derivWithin (uniqueDiffWithinAt_Ioi a)).symm

theorem piece_derivative_left {a b : ℝ} (hab : a < b) {v : Fin n → ℝ}
    (he : ∀ x ∈ Icc a b, (X.interpolant v).eval x = X.lebesgue x) :
    ((X.interpolant v).derivative).eval b = derivWithin X.lebesgue (Iio b) b := by
  have hh : X.lebesgue =ᶠ[𝓝[<] b] (fun x => (X.interpolant v).eval x) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)]
      with x hxb hxa
    exact (he x ⟨hxa.le, hxb.le⟩).symm
  have hd := ((X.interpolant v).hasDerivAt b).hasDerivWithinAt.congr_of_eventuallyEq hh
    (he b ⟨hab.le, le_rfl⟩).symm
  exact (hd.derivWithin (uniqueDiffWithinAt_Iio b)).symm

end Nodes
end Erdos1132
