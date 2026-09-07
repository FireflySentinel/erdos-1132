import Erdos1132.Counterexample.AmplitudeLemma
import Erdos1132.Counterexample.Assembly

/-! # Interior rows in every degree and compact interval exhaustion

Paper: §7.5, assembly of the array in Theorem 2.
-/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace Erdos1132.Counterexample

def defaultInteriorRows (n : ℕ) : Nodes n where
  point i := -1+2*((i:ℝ)+1)/((n:ℝ)+1)
  injective := by
    intro i j he
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    have hh : (i:ℝ) = (j:ℝ) := by
      have he' : 2*((i:ℝ)+1)/((n:ℝ)+1) = 2*((j:ℝ)+1)/((n:ℝ)+1) := by linarith
      have hh := (div_left_inj' hn).mp he'
      linarith
    exact Fin.ext (by exact_mod_cast hh)
  mem_interval := by
    intro i
    have hi : (i:ℝ) < n := by exact_mod_cast i.isLt
    have hn : 0 < (n:ℝ)+1 := by positivity
    constructor
    · have hh : 0 ≤ 2*((i:ℝ)+1)/((n:ℝ)+1) := by positivity
      linarith
    · have hh : 2*((i:ℝ)+1)/((n:ℝ)+1) ≤ 2 := (div_le_iff₀ hn).mpr (by linarith)
      linarith

theorem defaultInteriorRows_interior (n : ℕ) (i : Fin n) :
    (defaultInteriorRows n).point i ∈ Ioo (-1) 1 := by
  have hi : (i:ℝ) < n := by exact_mod_cast i.isLt
  have hn : 0 < (n:ℝ)+1 := by positivity
  change -1 < -1+2*((i:ℝ)+1)/((n:ℝ)+1) ∧ -1+2*((i:ℝ)+1)/((n:ℝ)+1) < 1
  constructor
  · have hh : 0 < 2*((i:ℝ)+1)/((n:ℝ)+1) := by positivity
    linarith
  · have hh : 2*((i:ℝ)+1)/((n:ℝ)+1) < 2 := (div_lt_iff₀ hn).mpr (by linarith)
    linarith

def compactInteriorLeft (j : ℕ) : ℝ := -1+1/((j:ℝ)+2)
def compactInteriorRight (j : ℕ) : ℝ := 1-1/((j:ℝ)+2)
def compactInterior (j : ℕ) : Set ℝ := Icc (compactInteriorLeft j) (compactInteriorRight j)

theorem compactInterior_bounds (j : ℕ) :
    -1 < compactInteriorLeft j ∧ compactInteriorLeft j ≤ compactInteriorRight j ∧ compactInteriorRight j < 1 := by
  have hd : 0 < 1/((j:ℝ)+2) := by positivity
  have hhalf : 1/((j:ℝ)+2) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  dsimp [compactInteriorLeft,compactInteriorRight]
  exact ⟨by linarith,by linarith,by linarith⟩

theorem eventually_mem_compactInterior {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    ∀ᶠ j in atTop, x ∈ compactInterior j := by
  have ht : Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun j : ℕ => 1/(((j+1:ℕ):ℝ)+1)) atTop (𝓝 0) at hh
    simpa only [Nat.cast_add,Nat.cast_one,show ∀ a : ℝ, a+1+1 = a+2 by intro a; ring] using hh
  have hmin : 0 < min (x+1) (1-x) := lt_min (by linarith [hx.1]) (by linarith [hx.2])
  filter_upwards [ht.eventually (Iio_mem_nhds hmin)] with j hj
  have h1 := hj.trans_le (min_le_left _ _)
  have h2 := hj.trans_le (min_le_right _ _)
  constructor <;> dsimp [compactInteriorLeft,compactInteriorRight] <;> linarith

/-- The amplitude lemma extends to an entire row family using a finite
prefix of equally spaced interior nodes. -/
theorem exists_amplitude_row_family (h : ℝ[X])
    (hzero : ∀ z : ℂ, ‖z‖ ≤ 1 → (complexPolynomial h).eval z ≠ 0)
    (hpos : 0 < h.coeff 0) (j : ℕ) :
    ∃ B : ∀ n : ℕ, Nodes (n+2), (∀ n i, (B n).point i ∈ Ioo (-1) 1) ∧
      ∃ T : ℕ, ∀ n ≥ T, ∀ x ∈ compactInterior j,
        (B n).lebesgue x ≤ 2/Real.pi*Real.log (n+2:ℝ)+3-
          (logarithmicOperator (amplitudeWeight h) x/amplitudeWeight h x)/Real.pi := by
  classical
  have hb := compactInterior_bounds j
  have hrow := (tendsto_add_atTop_nat 2).eventually
    (eventually_exists_amplitude_upper_rows h hzero hpos hb.1 hb.2.1 hb.2.2)
  change ∀ᶠ n : ℕ in atTop, ∃ Y : Nodes (n+2), _ at hrow
  obtain ⟨T,hT⟩ := eventually_atTop.mp hrow
  let B : ∀ n : ℕ, Nodes (n+2) := fun n =>
    if hn : T ≤ n then Classical.choose (hT n hn) else defaultInteriorRows (n+2)
  refine ⟨B,?_,T,?_⟩
  · intro n i
    dsimp only [B]
    split_ifs with hn
    · exact (Classical.choose_spec (hT n hn)).1 i
    · exact defaultInteriorRows_interior _ _
  · intro n hn x hx
    have hh := (Classical.choose_spec (hT n hn)).2 x hx
    dsimp only [B]
    rw [dif_pos hn]
    convert hh using 1 <;> push_cast <;> ring

end Erdos1132.Counterexample
