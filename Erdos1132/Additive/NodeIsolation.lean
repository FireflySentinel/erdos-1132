import Erdos1132.Additive.LebesgueLipschitz
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! # A large one-sided derivative forces an adjacent empty interval

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Finset
open scoped Topology BigOperators
namespace Erdos1132

theorem polynomial_endpoint_derivative_bound (p : ℝ[X]) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (he : p.eval a = p.eval b)
    (hsecond : ∀ t ∈ Icc a b, |p.derivative.derivative.eval t| ≤ B) :
    |p.derivative.eval a| ≤ B*(b-a) ∧ |p.derivative.eval b| ≤ B*(b-a) := by
  obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hab p.continuous.continuousOn he
    (fun t ht => p.hasDerivAt t)
  have hbound (z : ℝ) (hz : z ∈ Icc a b) : |p.derivative.eval z| ≤ B*|z-c| := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t ht => p.derivative.differentiableAt)
      (fun t ht => by simpa only [Polynomial.deriv, Real.norm_eq_abs] using hsecond t ht)
      (convex_Icc a b) ⟨hc.1.le, hc.2.le⟩ hz
    simpa only [Real.norm_eq_abs, hcz, sub_zero] using hh
  constructor
  · have hh := hbound a ⟨le_rfl, hab.le⟩
    rw [abs_of_neg (sub_neg.mpr hc.1)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hc.2]) hB)
  · have hh := hbound b ⟨hab.le, le_rfl⟩
    rw [abs_of_pos (sub_pos.mpr hc.2)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hc.1]) hB)

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem exists_next_node (k : Fin n) (hne : ∃ j, X.point k < X.point j) :
    ∃ j, X.point k < X.point j ∧
      (∀ i, X.point k < X.point i → X.point j ≤ X.point i) ∧
      (∀ i, X.point i ∉ Ioo (X.point k) (X.point j)) := by
  classical
  let S := univ.filter (fun i => X.point k < X.point i)
  have hS : S.Nonempty := by obtain ⟨j, hj⟩ := hne; exact ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image X.point hS
  have hjk : X.point k < X.point j := (mem_filter.mp hj).2
  have hnext (i : Fin n) (hi : X.point k < X.point i) : X.point j ≤ X.point i :=
    hmin i (mem_filter.mpr ⟨mem_univ i, hi⟩)
  exact ⟨j, hjk, hnext, fun i hi => (hnext i hi.1).not_gt hi.2⟩

theorem exists_previous_node (k : Fin n) (hne : ∃ j, X.point j < X.point k) :
    ∃ j, X.point j < X.point k ∧
      (∀ i, X.point i < X.point k → X.point i ≤ X.point j) ∧
      (∀ i, X.point i ∉ Ioo (X.point j) (X.point k)) := by
  classical
  let S := univ.filter (fun i => X.point i < X.point k)
  have hS : S.Nonempty := by obtain ⟨j, hj⟩ := hne; exact ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image X.point hS
  have hjk : X.point j < X.point k := (mem_filter.mp hj).2
  have hprev (i : Fin n) (hi : X.point i < X.point k) : X.point i ≤ X.point j :=
    hmax i (mem_filter.mpr ⟨mem_univ i, hi⟩)
  exact ⟨j, hjk, hprev, fun i hi => (hprev i hi.2).not_gt hi.1⟩

theorem right_isolation_of_large_derivative (k : Fin n) {a b δ H B : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hmargin : Icc (X.point k-δ) (X.point k+δ) ⊆ Icc a b)
    (hδB : B*δ ≤ H)
    (hder : H ≤ |derivWithin X.lebesgue (Ioi (X.point k)) (X.point k)|)
    (hsecond : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      ∀ t ∈ Icc a b, |(X.interpolant v).derivative.derivative.eval t| ≤ B) :
    ∀ j, X.point k < X.point j → X.point k+δ ≤ X.point j := by
  intro j hj
  by_contra hclose
  have hjclose := lt_of_not_ge hclose
  obtain ⟨i, hi, hmin, hgap⟩ := X.exists_next_node k ⟨j, hj⟩
  obtain ⟨v, hv, he⟩ := X.exists_interpolant_piece hi hgap
  have hend : (X.interpolant v).eval (X.point k) = (X.interpolant v).eval (X.point i) := by
    rw [he _ ⟨le_rfl, hi.le⟩, he _ ⟨hi.le, le_rfl⟩, X.lebesgue_at_node, X.lebesgue_at_node]
  have hh := (polynomial_endpoint_derivative_bound (X.interpolant v) hi hB.le hend
    (fun t ht => hsecond v hv t (hmargin ⟨by linarith [ht.1], by linarith [ht.2, hmin j hj]⟩))).1
  rw [X.piece_derivative_right hi he] at hh
  have hlen : X.point i-X.point k < δ := by linarith [hmin j hj]
  have hh' := mul_lt_mul_of_pos_left hlen hB
  linarith

theorem left_isolation_of_large_derivative (k : Fin n) {a b δ H B : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hmargin : Icc (X.point k-δ) (X.point k+δ) ⊆ Icc a b)
    (hδB : B*δ ≤ H)
    (hder : H ≤ |derivWithin X.lebesgue (Iio (X.point k)) (X.point k)|)
    (hsecond : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      ∀ t ∈ Icc a b, |(X.interpolant v).derivative.derivative.eval t| ≤ B) :
    ∀ j, X.point j < X.point k → X.point j+δ ≤ X.point k := by
  intro j hj
  by_contra hclose
  have hjclose := lt_of_not_ge hclose
  obtain ⟨i, hi, hmax, hgap⟩ := X.exists_previous_node k ⟨j, hj⟩
  obtain ⟨v, hv, he⟩ := X.exists_interpolant_piece hi hgap
  have hend : (X.interpolant v).eval (X.point i) = (X.interpolant v).eval (X.point k) := by
    rw [he _ ⟨le_rfl, hi.le⟩, he _ ⟨hi.le, le_rfl⟩, X.lebesgue_at_node, X.lebesgue_at_node]
  have hh := (polynomial_endpoint_derivative_bound (X.interpolant v) hi hB.le hend
    (fun t ht => hsecond v hv t (hmargin ⟨by linarith [ht.1, hmax j hj], by linarith [ht.2]⟩))).2
  rw [X.piece_derivative_left hi he] at hh
  have hlen : X.point k-X.point i < δ := by linarith [hmax j hj]
  have hh' := mul_lt_mul_of_pos_left hlen hB
  linarith

def OneSidedIsolated (k : Fin n) (δ : ℝ) : Prop :=
  (∀ j, X.point k < X.point j → X.point k+δ ≤ X.point j) ∨
  (∀ j, X.point j < X.point k → X.point j+δ ≤ X.point k)

theorem oneSidedIsolated_of_large_jump (k : Fin n) {a b δ H B : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hmargin : Icc (X.point k-δ) (X.point k+δ) ⊆ Icc a b)
    (hδB : B*δ ≤ H) (hjump : 2*H ≤ X.derivativeJump k)
    (hsecond : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      ∀ t ∈ Icc a b, |(X.interpolant v).derivative.derivative.eval t| ≤ B) :
    X.OneSidedIsolated k δ := by
  have hr := le_abs_self (derivWithin X.lebesgue (Ioi (X.point k)) (X.point k))
  have hl := neg_abs_le (derivWithin X.lebesgue (Iio (X.point k)) (X.point k))
  rw [derivativeJump] at hjump
  by_cases hright : H ≤ |derivWithin X.lebesgue (Ioi (X.point k)) (X.point k)|
  · exact Or.inl (X.right_isolation_of_large_derivative k hB hδ hmargin hδB hright hsecond)
  · exact Or.inr (X.left_isolation_of_large_derivative k hB hδ hmargin hδB (by linarith) hsecond)

end Nodes
end Erdos1132
