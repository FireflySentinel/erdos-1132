import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open Polynomial Finset

namespace Erdos1132

/-- A row of distinct interpolation nodes in `[-1, 1]`. -/
structure Nodes (n : ℕ) where
  point : Fin n → ℝ
  injective : Function.Injective point
  mem_interval : ∀ i, point i ∈ Set.Icc (-1) 1

namespace Nodes

variable {n : ℕ} (X : Nodes n)

def cardinal (i : Fin n) : ℝ[X] := Lagrange.basis univ X.point i

def lebesgue (x : ℝ) : ℝ := ∑ i, |(X.cardinal i).eval x|

def nodePolynomial : ℝ[X] := Lagrange.nodal univ X.point

def weight (i : Fin n) : ℝ := Lagrange.nodalWeight univ X.point i

def totalWeight : ℝ := ∑ i, |X.weight i|

def mass (i : Fin n) : ℝ := |X.weight i| / X.totalWeight

def signedMass (i : Fin n) : ℝ := X.weight i / X.totalWeight

theorem weight_ne_zero (i : Fin n) : X.weight i ≠ 0 :=
  Lagrange.nodalWeight_ne_zero X.injective.injOn (mem_univ i)

theorem weight_eq_derivative (i : Fin n) :
    X.weight i = ((X.nodePolynomial.derivative).eval (X.point i))⁻¹ :=
  Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i)

theorem totalWeight_pos (hn : 0 < n) : 0 < X.totalWeight := by
  apply sum_pos'
  · intro i _
    exact abs_nonneg _
  · exact ⟨⟨0, hn⟩, mem_univ _, abs_pos.mpr (X.weight_ne_zero _)⟩

theorem mass_pos (hn : 0 < n) (i : Fin n) : 0 < X.mass i :=
  div_pos (abs_pos.mpr (X.weight_ne_zero i)) (X.totalWeight_pos hn)

theorem sum_mass (hn : 0 < n) : ∑ i, X.mass i = 1 := by
  simp only [mass, ← sum_div]
  change X.totalWeight / X.totalWeight = 1
  exact div_self (ne_of_gt (X.totalWeight_pos hn))

theorem abs_signedMass (hn : 0 < n) (i : Fin n) :
    |X.signedMass i| = X.mass i := by
  rw [signedMass, mass, abs_div, abs_of_pos (X.totalWeight_pos hn)]

theorem cardinal_at_node (i j : Fin n) :
    (X.cardinal i).eval (X.point j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [cardinal, Lagrange.eval_basis_self X.injective.injOn]
  · simp [cardinal, h, Lagrange.eval_basis_of_ne h]

theorem lebesgue_at_node (j : Fin n) : X.lebesgue (X.point j) = 1 := by
  simp only [lebesgue, X.cardinal_at_node, apply_ite abs, abs_one, abs_zero]
  simp

theorem lebesgue_nonneg (x : ℝ) : 0 ≤ X.lebesgue x :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_lebesgue : Continuous X.lebesgue := by
  unfold lebesgue
  fun_prop

theorem measurable_lebesgue : Measurable X.lebesgue :=
  X.continuous_lebesgue.measurable

/-- The signed barycentric weights annihilate polynomials of degree below `n - 1`. -/
theorem weight_cancellation {p : ℝ[X]} (hp : p.degree < (n - 1 : ℕ)) :
    ∑ i, X.weight i * p.eval (X.point i) = 0 := by
  have hpn : p.degree < (n : ℕ) :=
    hp.trans_le (by exact_mod_cast Nat.sub_le n 1)
  have h := Lagrange.coeff_eq_sum X.injective.injOn (s := univ) (P := p)
    (by simpa using hpn)
  have hc : p.coeff (n - 1) = 0 := Polynomial.coeff_eq_zero_of_degree_lt hp
  simp only [card_univ, Fintype.card_fin, hc] at h
  apply Eq.trans ?_ h.symm
  apply sum_congr rfl
  intro i _
  simp [weight, Lagrange.nodalWeight, prod_inv_distrib, div_eq_mul_inv, mul_comm]

theorem signedMass_cancellation {p : ℝ[X]} (hp : p.degree < (n - 1 : ℕ)) :
    ∑ i, X.signedMass i * p.eval (X.point i) = 0 := by
  simp only [signedMass, div_mul_eq_mul_div, ← sum_div, X.weight_cancellation hp, zero_div]

theorem sum_signedMass (hn : 2 ≤ n) : ∑ i, X.signedMass i = 0 := by
  simpa using X.signedMass_cancellation (p := 1)
    (by simp only [degree_one]; exact_mod_cast (show 0 < n - 1 by omega))

theorem split_mass_nonneg (hn : 0 < n) (i : Fin n) :
    0 ≤ X.mass i + X.signedMass i ∧ 0 ≤ X.mass i - X.signedMass i := by
  have h := abs_le.mp (le_of_eq (X.abs_signedMass hn i))
  constructor <;> linarith

theorem sum_split_mass (hn : 2 ≤ n) :
    (∑ i, (X.mass i + X.signedMass i)) = 1 ∧
    (∑ i, (X.mass i - X.signedMass i)) = 1 := by
  simp [sum_add_distrib, sum_sub_distrib, X.sum_mass (by omega), X.sum_signedMass hn]

end Nodes

end Erdos1132
