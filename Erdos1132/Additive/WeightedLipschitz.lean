import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! # Uniform Lipschitz bounds for a squared weight divided by a positive density

Paper: §3, derivative-jump energy.
-/

noncomputable section
open Set Real
namespace Erdos1132

theorem square_div_bound {u r M c : ℝ} (hc : 0 < c) (hr : c ≤ r)
    (hM : 0 ≤ M) (hu : |u| ≤ M) : |u^2/r| ≤ M^2/c := by
  have hr0 := hc.trans_le hr
  rw [abs_of_nonneg (by positivity : 0 ≤ u^2/r)]
  exact div_le_div₀ (sq_nonneg _) (by nlinarith [abs_le.mp hu]) hc hr

theorem inverse_lipschitz_bound {r : ℝ → ℝ} {c D : ℝ} (hc : 0 < c)
    (hr : ∀ x, c ≤ r x) (hD : 0 ≤ D)
    (hlip : ∀ x y, |r x-r y| ≤ D*|x-y|) (x y : ℝ) :
    |(r x)⁻¹-(r y)⁻¹| ≤ (D/c^2)*|x-y| := by
  have hx := hc.trans_le (hr x)
  have hy := hc.trans_le (hr y)
  have he : (r x)⁻¹-(r y)⁻¹ = (r y-r x)/(r x*r y) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hx, abs_of_pos hy, abs_sub_comm]
  calc
    _ ≤ (D*|x-y|)/(c^2) := div_le_div₀ (by positivity) (hlip x y) (sq_pos_of_pos hc)
      (by simpa only [pow_two] using mul_le_mul (hr x) (hr y) hc.le hx.le)
    _ = _ := by ring

theorem square_div_lipschitz {f r : ℝ → ℝ} {M L c D : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hc : 0 < c) (hD : 0 ≤ D)
    (hf : ∀ x, |f x| ≤ M) (hr : ∀ x, c ≤ r x)
    (hfl : ∀ x y, |f x-f y| ≤ L*|x-y|)
    (hrl : ∀ x y, |r x-r y| ≤ D*|x-y|) (x y : ℝ) :
    |(f x)^2/r x-(f y)^2/r y| ≤ (2*M*L/c+M^2*D/c^2)*|x-y| := by
  have hx := hc.trans_le (hr x)
  have hy := hc.trans_le (hr y)
  have hsq : |(f x)^2-(f y)^2| ≤ 2*M*L*|x-y| := by
    rw [show (f x)^2-(f y)^2 = (f x-f y)*(f x+f y) by ring, abs_mul]
    have hsum : |f x+f y| ≤ 2*M := (abs_add_le _ _).trans (by linarith [hf x, hf y])
    have hh := mul_le_mul (hfl x y) hsum (abs_nonneg _) (by positivity : 0 ≤ L*|x-y|)
    exact hh.trans_eq (by ring)
  have hi : |(r x)⁻¹| ≤ 1/c := by
    rw [abs_of_pos (inv_pos.mpr hx)]
    simpa only [one_div] using one_div_le_one_div_of_le hc (hr x)
  have hfy : |(f y)^2| ≤ M^2 := by rw [abs_pow]; gcongr; exact hf y
  have he : (f x)^2/r x-(f y)^2/r y =
      ((f x)^2-(f y)^2)*(r x)⁻¹+(f y)^2*((r x)⁻¹-(r y)⁻¹) := by ring
  rw [he]
  calc
    _ ≤ |((f x)^2-(f y)^2)*(r x)⁻¹|+|(f y)^2*((r x)⁻¹-(r y)⁻¹)| := abs_add_le _ _
    _ = |(f x)^2-(f y)^2| * |(r x)⁻¹|+|(f y)^2| * |(r x)⁻¹-(r y)⁻¹| := by rw [abs_mul, abs_mul]
    _ ≤ (2*M*L*|x-y|)*(1/c)+M^2*((D/c^2)*|x-y|) := add_le_add
      (mul_le_mul hsq hi (abs_nonneg _) (by positivity))
      (mul_le_mul hfy (inverse_lipschitz_bound hc hr hD hrl x y) (abs_nonneg _) (sq_nonneg M))
    _ = _ := by ring

theorem abs_projIcc_sub_le {l r : ℝ} (hlr : l ≤ r) (x y : ℝ) :
    |(projIcc l r hlr x : ℝ)-(projIcc l r hlr y : ℝ)| ≤ |x-y| := by
  simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using
    (LipschitzWith.projIcc hlr).dist_le_mul x y

end Erdos1132
