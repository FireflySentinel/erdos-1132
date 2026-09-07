import Erdos1132.Additive.CenteredCover

/-! # Measure bounds at the high-value interval scale

Paper: §4, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Finset MeasureTheory Real
open scoped BigOperators
namespace Erdos1132

def coverMultiplicity (d K β : ℝ) : ℝ := (4*β+4*K+2*d)/d

theorem coverMultiplicity_pos {d K β : ℝ} (hd : 0 < d) (hK : 0 ≤ K) (hβ : 0 < β) :
    0 < coverMultiplicity d K β := by unfold coverMultiplicity; positivity

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem scaled_cover_bounds (s : Finset (Fin n)) (y : Fin n → ℝ)
    {d K β κ : ℝ} (hn : 0 < n) (hln : 1 ≤ Real.log (n:ℝ))
    (hd : 0 < d) (hK : 0 ≤ K) (hβ : 0 < β) (hκ : 0 < κ)
    (hcard : κ*(n:ℝ) ≤ (s.card:ℝ))
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i (d/(n:ℝ)))
    (hmove : ∀ i ∈ s, |y i-X.point i| ≤ K/(n:ℝ)) :
    let A := centeredCover s y (β/((n:ℝ)*Real.log n))
    volume.real A ≤ 2*β/Real.log n ∧
    (2*β*κ/coverMultiplicity d K β)/Real.log n ≤ volume.real A ∧
    ∀ a b : ℝ, a ≤ b → volume.real (A ∩ Icc a b) ≤
      (4*β/d+2*β*coverMultiplicity d K β+1)*
        ((b-a)/Real.log n+1/((n:ℝ)*Real.log n)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hl : 0 < Real.log (n:ℝ) := by linarith
  let r := β/((n:ℝ)*Real.log n)
  let B := coverMultiplicity d K β
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 < B := coverMultiplicity_pos hd hK hβ
  have hsmall : r ≤ β/(n:ℝ) := by
    dsimp [r]
    exact div_le_div_of_nonneg_left hβ.le hnR (by nlinarith)
  have hmultiplicity : (4*r+4*(K/(n:ℝ))+2*(d/(n:ℝ)))/(d/(n:ℝ)) ≤ B := by
    apply (div_le_iff₀ (by positivity : 0 < d/(n:ℝ))).mpr
    have he : B*(d/(n:ℝ)) = (4*β+4*K+2*d)/(n:ℝ) := by dsimp [B, coverMultiplicity]; field_simp
    rw [he]
    have he' : (4*β+4*K+2*d)/(n:ℝ) = 4*(β/(n:ℝ))+4*(K/(n:ℝ))+2*(d/(n:ℝ)) := by ring
    rw [he']; linarith
  have hcount (x : ℝ) : ((s.filter (fun i => x ∈ Icc (y i-r) (y i+r))).card:ℝ) ≤ B :=
    (X.displaced_cover_multiplicity s y (by positivity) (by positivity) hr.le hiso hmove x).trans hmultiplicity
  have hupper := measure_centeredCover_le s y hr.le
  have hsn : (s.card:ℝ) ≤ n := by
    exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_univ (s := s))
  have hlow := measure_centeredCover_lower s y hr.le hcount
  constructor
  · have hh := mul_le_mul_of_nonneg_left hsn (by positivity : 0 ≤ 2*r)
    have he : 2*r*(n:ℝ) = 2*β/Real.log n := by dsimp [r]; field_simp
    exact hupper.trans (hh.trans_eq he)
  constructor
  · have hh := mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ 2*r)
    have he : 2*r*(κ*(n:ℝ)) = (2*β*κ/Real.log n) := by dsimp [r]; field_simp
    rw [he] at hh
    have h := (div_le_iff₀ hB).mpr (show (2*β*κ/Real.log n) ≤
      volume.real (centeredCover s y r)*B by nlinarith)
    convert! h using 1 <;> ring
  · intro a b hab
    have hh := X.displaced_cover_intersection_bound s y (by positivity) (by positivity) hr.le hab hiso hmove
    have he : 2*r/(d/(n:ℝ)) = 2*β/(d*Real.log n) := by dsimp [r]; field_simp
    rw [he] at hh
    have hsmall' : 2*(b-a)+4*r+4*(K/(n:ℝ))+2*(d/(n:ℝ)) ≤
        2*(b-a)+(4*β+4*K+2*d)/(n:ℝ) := by
      have he' : (4*β+4*K+2*d)/(n:ℝ) = 4*(β/(n:ℝ))+4*(K/(n:ℝ))+2*(d/(n:ℝ)) := by ring
      rw [he']; linarith
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hsmall' (by positivity))
    have he' : (2*β/(d*Real.log n))*(2*(b-a)+(4*β+4*K+2*d)/(n:ℝ)) =
        (4*β/d)*((b-a)/Real.log n)+(2*β*B)*(1/((n:ℝ)*Real.log n)) := by
      dsimp [B, coverMultiplicity]
      ring
    rw [he'] at hh'
    have h1 : 0 ≤ (b-a)/Real.log n := div_nonneg (sub_nonneg.mpr hab) hl.le
    have h2 : 0 ≤ 1/((n:ℝ)*Real.log n) := by positivity
    have h3 : 0 ≤ 4*β/d := by positivity
    have h4 : 0 ≤ 2*β*B := by positivity
    have hleft := mul_le_mul_of_nonneg_right (by linarith : 4*β/d ≤ 4*β/d+2*β*B+1) h1
    have hright := mul_le_mul_of_nonneg_right (by linarith : 2*β*B ≤ 4*β/d+2*β*B+1) h2
    dsimp only [B] at *
    nlinarith

end Nodes
end Erdos1132
