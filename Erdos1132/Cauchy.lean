import Erdos1132.Interpolation
import Mathlib.Analysis.Complex.Basic

noncomputable section

open scoped BigOperators
open Finset

namespace Erdos1132

/-- A finite positive measure of total mass one. -/
structure AtomicProbability (n : ℕ) where
  point : Fin n → ℝ
  mass : Fin n → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  sum_mass : ∑ i, mass i = 1

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

def cauchy (z : ℂ) : ℂ := ∑ i, (μ.mass i : ℂ) / (z - μ.point i)

def boundary (x : ℝ) : ℝ := ∑ i, μ.mass i / (x - μ.point i)

def gamma (h x : ℝ) : ℝ := ∑ i, μ.mass i * h / ((x - μ.point i) ^ 2 + h ^ 2)

theorem exists_mass_pos : ∃ i, 0 < μ.mass i := by
  by_contra! h
  have hs := sum_nonpos (s := univ) (fun i _ => h i)
  rw [μ.sum_mass] at hs
  norm_num at hs

theorem gamma_pos {h : ℝ} (hh : 0 < h) (x : ℝ) : 0 < μ.gamma h x := by
  obtain ⟨i, hi⟩ := μ.exists_mass_pos
  refine sum_pos' (fun j _ => div_nonneg (mul_nonneg (μ.mass_nonneg j) hh.le)
    (by positivity)) ⟨i, mem_univ _, ?_⟩
  exact div_pos (mul_pos hi hh) (by positivity)

theorem cauchy_ofReal (x : ℝ) : μ.cauchy x = (μ.boundary x : ℂ) := by
  simp [cauchy, boundary]

theorem neg_im_cauchy (h x : ℝ) :
    -(μ.cauchy ((x : ℂ) + h * Complex.I)).im = μ.gamma h x := by
  simp only [cauchy, Complex.im_sum, ← sum_neg_distrib, gamma]
  apply sum_congr rfl
  intro i _
  simp [Complex.div_im, Complex.normSq_apply, pow_two]

theorem gamma_lower {h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Icc (-1) 1) (hs : ∀ i, μ.point i ∈ Set.Icc (-1) 1) :
    h / (4 + h ^ 2) ≤ μ.gamma h x := by
  calc
    h / (4 + h ^ 2) = ∑ i, μ.mass i * (h / (4 + h ^ 2)) := by
      rw [← sum_mul, μ.sum_mass, one_mul]
    _ ≤ μ.gamma h x := by
      apply sum_le_sum
      intro i _
      have hi := hs i
      have hsq : (x - μ.point i) ^ 2 ≤ 4 := by
        have h₁ : 0 ≤ 2 - (x - μ.point i) := by linarith [hx.2, hi.1]
        have h₂ : 0 ≤ 2 + (x - μ.point i) := by linarith [hx.1, hi.2]
        nlinarith [mul_nonneg h₁ h₂]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_left (mul_nonneg (μ.mass_nonneg i) hh.le)
        (by positivity) (by linarith)

end AtomicProbability

namespace Nodes

variable {n : ℕ} (X : Nodes n)

def probability (hn : 0 < n) : AtomicProbability n where
  point := X.point
  mass := X.mass
  mass_nonneg i := (X.mass_pos hn i).le
  sum_mass := X.sum_mass hn

def plusProbability (hn : 2 ≤ n) : AtomicProbability n where
  point := X.point
  mass i := X.mass i + X.signedMass i
  mass_nonneg i := (X.split_mass_nonneg (by omega) i).1
  sum_mass := (X.sum_split_mass hn).1

def minusProbability (hn : 2 ≤ n) : AtomicProbability n where
  point := X.point
  mass i := X.mass i - X.signedMass i
  mass_nonneg i := (X.split_mass_nonneg (by omega) i).2
  sum_mass := (X.sum_split_mass hn).2

def signedCauchy (z : ℂ) : ℂ := ∑ i, (X.signedMass i : ℂ) / (z - X.point i)

def signedBoundary (x : ℝ) : ℝ := ∑ i, X.signedMass i / (x - X.point i)

def absoluteTransform (x : ℝ) : ℝ := ∑ i, X.mass i / |x - X.point i|

theorem cauchy_plus (hn : 2 ≤ n) (z : ℂ) :
    (X.plusProbability hn).cauchy z =
      (X.probability (by omega)).cauchy z + X.signedCauchy z := by
  simp [AtomicProbability.cauchy, plusProbability, probability, signedCauchy,
    add_div, sum_add_distrib]

theorem cauchy_minus (hn : 2 ≤ n) (z : ℂ) :
    (X.minusProbability hn).cauchy z =
      (X.probability (by omega)).cauchy z - X.signedCauchy z := by
  simp [AtomicProbability.cauchy, minusProbability, probability, signedCauchy,
    sub_div, sum_sub_distrib]

theorem nodePolynomial_ne_zero {x : ℝ} (hx : ∀ i, x ≠ X.point i) :
    X.nodePolynomial.eval x ≠ 0 :=
  Lagrange.eval_nodal_not_at_node (fun i _ => hx i)

theorem signedBoundary_eq (hn : 0 < n) {x : ℝ} (hx : ∀ i, x ≠ X.point i) :
    X.signedBoundary x = 1 / (X.totalWeight * X.nodePolynomial.eval x) := by
  have hs : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  have h := Lagrange.eval_interpolate_not_at_node (1 : Fin n → ℝ)
    (s := univ) (v := X.point) (fun i _ => hx i)
  simp only [Lagrange.interpolate_one X.injective.injOn hs, Polynomial.eval_one,
    Pi.one_apply, mul_one] at h
  have hp := X.nodePolynomial_ne_zero hx
  have hw := ne_of_gt (X.totalWeight_pos hn)
  have hg : ∑ i, X.weight i / (x - X.point i) = (X.nodePolynomial.eval x)⁻¹ := by
    rw [← one_div, eq_div_iff hp]
    simpa [nodePolynomial, weight, div_eq_mul_inv, mul_comm] using h.symm
  simp only [signedBoundary, signedMass, div_right_comm (X.weight _) X.totalWeight,
    ← sum_div, hg]
  field_simp

theorem lebesgue_transform (hn : 0 < n) {x : ℝ} (hx : ∀ i, x ≠ X.point i) :
    X.lebesgue x = X.absoluteTransform x / |X.signedBoundary x| := by
  have hp := X.nodePolynomial_ne_zero hx
  have hw := ne_of_gt (X.totalWeight_pos hn)
  have hb : X.lebesgue x = |X.nodePolynomial.eval x| * X.totalWeight *
      X.absoluteTransform x := by
    simp only [lebesgue, absoluteTransform, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [cardinal, Lagrange.eval_basis_not_at_node (mem_univ _) (hx i)]
    simp only [abs_mul, abs_inv, mass, nodePolynomial, weight]
    field_simp
  rw [hb, X.signedBoundary_eq hn hx, abs_div, abs_one, abs_mul,
    abs_of_pos (X.totalWeight_pos hn)]
  field_simp

end Nodes

end Erdos1132
