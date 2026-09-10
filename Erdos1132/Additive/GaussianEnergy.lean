import Erdos1132.Additive.RieszKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Positivity of Gaussian energy for bounded signed densities

The exponential series expresses each finite approximation as a sum of
squares of moments. Dominated convergence then proves positivity of the
actual Gaussian kernel.

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Real MeasureTheory Filter Finset
open scoped Topology BigOperators
namespace Erdos1132

theorem abs_exp_partial_sum_le (z : ℝ) (N : ℕ) :
    |∑ k ∈ range N, z^k/(k.factorial : ℝ)| ≤ Real.exp |z| := by
  calc
    _ ≤ ∑ k ∈ range N, |z^k/(k.factorial : ℝ)| := abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ range N, |z|^k/(k.factorial : ℝ) := by simp only [abs_div, abs_pow, Nat.abs_cast]
    _ ≤ _ := Real.sum_le_exp_of_nonneg (abs_nonneg _) _

theorem tendsto_exp_partial_sum (z : ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, z^k/(k.factorial : ℝ))
      atTop (𝓝 (Real.exp z)) := by
  simpa only [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat

theorem gaussian_energy_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {x w : α → ℝ}
    (hx : Measurable x) (hw : Measurable w) {B s : ℝ}
    (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hxb : ∀ u, |x u| ≤ 1) (hwb : ∀ u, |w u| ≤ B) :
    0 ≤ ∫ p : α × α,
      w p.1*w p.2*Real.exp (-s*(x p.1-x p.2)^2) ∂μ.prod μ := by
  let φ (k : ℕ) (u : α) := w u*Real.exp (-s*(x u)^2)*(x u)^k
  have hφm (k : ℕ) : Measurable (φ k) := by dsimp [φ]; fun_prop
  have hφb (k : ℕ) (u : α) : |φ k u| ≤ B := by
    have he : Real.exp (-s*(x u)^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x u)])
    have hp : |x u|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) (hxb u)
    dsimp [φ]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    calc
      _ ≤ B*1*1 := mul_le_mul (mul_le_mul (hwb u) he (Real.exp_pos _).le hB)
        hp (by positivity) (by positivity)
      _ = B := by ring
  have hφi (k : ℕ) : Integrable (φ k) μ :=
    (integrable_const B).mono' (hφm k).aestronglyMeasurable
      (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using hφb k u))
  let F (N : ℕ) (p : α × α) := ∑ k ∈ range N,
    ((2*s)^k/(k.factorial : ℝ))*(φ k p.1*φ k p.2)
  have hFm (N : ℕ) : Measurable (F N) := by dsimp [F]; fun_prop
  have hFi (N : ℕ) : Integrable (F N) (μ.prod μ) := by
    apply integrable_finsetSum
    intro k hk
    exact ((hφi k).mul_prod (hφi k)).const_mul _
  have hpos (N : ℕ) : 0 ≤ ∫ p, F N p ∂μ.prod μ := by
    rw [show F N = (fun p => ∑ k ∈ range N,
      ((2*s)^k/(k.factorial : ℝ))*(φ k p.1*φ k p.2)) from rfl,
      integral_finsetSum _ (fun k hk => ((hφi k).mul_prod (hφi k)).const_mul _)]
    apply sum_nonneg
    intro k hk
    rw [integral_const_mul, integral_prod_mul]
    exact mul_nonneg (by positivity) (mul_self_nonneg _)
  have hFb (N : ℕ) (p : α × α) : |F N p| ≤ B^2*Real.exp (2*s) := by
    calc
      _ ≤ ∑ k ∈ range N, |((2*s)^k/(k.factorial : ℝ))*(φ k p.1*φ k p.2)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range N, ((2*s)^k/(k.factorial : ℝ))*B^2 := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2*s)^k/(k.factorial : ℝ)), abs_mul]
        gcongr
        simpa only [pow_two] using mul_le_mul (hφb k p.1) (hφb k p.2) (abs_nonneg _) hB
      _ = B^2*(∑ k ∈ range N, (2*s)^k/(k.factorial : ℝ)) := by rw [mul_sum]; congr 1; funext k; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) N) (sq_nonneg B)
  have hFform (N : ℕ) (p : α × α) : F N p =
      (w p.1*w p.2*Real.exp (-s*(x p.1)^2)*Real.exp (-s*(x p.2)^2))*
        (∑ k ∈ range N, (2*s*x p.1*x p.2)^k/(k.factorial : ℝ)) := by
    dsimp only [F]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    dsimp [φ]
    simp only [mul_pow]
    ring
  have hlim (p : α × α) : Tendsto (fun N => F N p) atTop
      (𝓝 (w p.1*w p.2*Real.exp (-s*(x p.1-x p.2)^2))) := by
    simp_rw [hFform]
    have h := (tendsto_exp_partial_sum (2*s*x p.1*x p.2)).const_mul
      (w p.1*w p.2*Real.exp (-s*(x p.1)^2)*Real.exp (-s*(x p.2)^2))
    convert h using 1
    congr 1
    rw [mul_assoc (w p.1*w p.2), mul_assoc (w p.1*w p.2), ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hconv := tendsto_integral_of_dominated_convergence (μ := μ.prod μ)
    (fun _ : α × α => B^2*Real.exp (2*s))
    (fun N => (hFm N).aestronglyMeasurable) (integrable_const _)
    (fun N => ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hFb N p))
    (ae_of_all _ hlim)
  exact ge_of_tendsto hconv (Eventually.of_forall hpos)

end Erdos1132
