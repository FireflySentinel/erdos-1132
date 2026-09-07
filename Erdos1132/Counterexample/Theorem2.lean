import Erdos1132.Counterexample.Theorem2Shifted

/-! # Theorem 2 in the paper's original degree convention

Paper: §7.5, assembly of the array in Theorem 2.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace Erdos1132.Counterexample

def unshiftRows (X : ∀ n : ℕ, Nodes (n+2)) : ∀ n : ℕ, Nodes n
  | 0 => defaultInteriorRows 0
  | 1 => defaultInteriorRows 1
  | n+2 => X n

@[simp] theorem unshiftRows_add_two (X : ∀ n : ℕ, Nodes (n+2)) (n : ℕ) :
    unshiftRows X (n+2) = X n := rfl

theorem unshiftRows_interior (X : ∀ n : ℕ, Nodes (n+2))
    (hX : ∀ n i, (X n).point i ∈ Ioo (-1) 1) (n : ℕ) (i : Fin n) :
    (unshiftRows X n).point i ∈ Ioo (-1) 1 := by
  cases n with
  | zero => exact defaultInteriorRows_interior 0 i
  | succ n =>
    cases n with
    | zero => exact defaultInteriorRows_interior 1 i
    | succ n => exact hX n i

/-- Theorem 2 with exactly `n` nodes in row `n`, including both assertions
for the same array. -/
theorem theorem2 (M : ℝ) (hM : 0 < M) :
    ∃ X : ∀ n : ℕ, Nodes n,
      (∀ n i, (X n).point i ∈ Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1:ℝ) 1, ∀ᶠ n in atTop,
        (X n).lebesgue x ≤ (2/Real.pi)*Real.log (n:ℝ)-M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1:ℝ) 1 |
        ∃ᶠ (n : ℕ) in atTop, (2/Real.pi)*Real.log (n:ℝ)-C < (X n).lebesgue x}) := by
  obtain ⟨Y,hY,hupper,hnd⟩ := theorem2_shifted M hM
  refine ⟨unshiftRows Y,unshiftRows_interior Y hY,?_,?_⟩
  · intro x hx
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hupper x hx)
    apply eventually_atTop.mpr
    refine ⟨N+2,fun n hn => ?_⟩
    have hn2 : 2 ≤ n := by omega
    obtain ⟨m,rfl⟩ : ∃ m : ℕ, n = m+2 := ⟨n-2,(Nat.sub_add_cancel hn2).symm⟩
    rw [unshiftRows_add_two]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hN m (by omega)
  · intro C hd
    apply hnd C
    apply hd.mono
    intro x hx
    refine ⟨x.property,?_⟩
    apply frequently_atTop.mpr
    intro N
    obtain ⟨n,hn,hval⟩ := frequently_atTop.mp hx (N+2)
    have hn2 : 2 ≤ n := by omega
    obtain ⟨m,rfl⟩ : ∃ m : ℕ, n = m+2 := ⟨n-2,(Nat.sub_add_cancel hn2).symm⟩
    refine ⟨m,by omega,?_⟩
    simpa only [unshiftRows_add_two,Nat.cast_add,Nat.cast_ofNat] using hval

end Erdos1132.Counterexample
