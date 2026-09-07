import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Equal children separated by equal gaps

The interval subdivision used in the Cantor construction retains both
parent endpoints and specifies every child and gap explicitly.

Paper: §7.1, the compact set and its gaps.
-/

noncomputable section

open Set

namespace Erdos1132.Counterexample

def childLeft (L a b : ℝ) (i : ℕ) : ℝ := L + i*(a+b)

def childInterval (L a b : ℝ) (i : ℕ) : Set ℝ :=
  Icc (childLeft L a b i) (childLeft L a b i+a)

def subdivisionGap (L a b : ℝ) (i : ℕ) : Set ℝ :=
  Ioo (childLeft L a b i+a) (childLeft L a b (i+1))

theorem childLeft_strictMono {L a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    StrictMono (childLeft L a b) := by
  intro i j hij
  have hh : (i : ℝ) < j := by exact_mod_cast hij
  unfold childLeft
  exact add_lt_add_of_le_of_lt le_rfl
    (mul_lt_mul_of_pos_right hh (add_pos_of_pos_of_nonneg ha hb))

theorem childInterval_pairwise_disjoint {L a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Pairwise (fun i j : ℕ => Disjoint (childInterval L a b i) (childInterval L a b j)) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (by omega)).symm
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hij' : (i : ℝ)+1 ≤ j := by exact_mod_cast hlt
  have hsep : childLeft L a b i+a < childLeft L a b j := by
    unfold childLeft
    nlinarith
  exact (not_lt_of_ge hxj.1) (hxi.2.trans_lt hsep)

theorem subdivisionGap_length (L a b : ℝ) (i : ℕ) :
    childLeft L a b (i+1) - (childLeft L a b i+a) = b := by
  unfold childLeft
  push_cast
  ring

theorem childInterval_subset_parent {L a b : ℝ} {m i : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hi : i < m) :
    childInterval L a b i ⊆ Icc L (L + m*a + (m-1 : ℕ)*b) := by
  have hm : 1 ≤ m := by omega
  have hi' : (i : ℝ) ≤ m-1 := by exact_mod_cast (Nat.le_sub_one_of_lt hi)
  intro x hx
  change childLeft L a b i ≤ x ∧ x ≤ childLeft L a b i+a at hx
  constructor
  · dsimp [childLeft] at hx
    have hprod : 0 ≤ (i : ℝ)*(a+b) := mul_nonneg (Nat.cast_nonneg _) (add_nonneg ha hb)
    linarith
  · rw [Nat.cast_sub hm, Nat.cast_one]
    have hprod := mul_le_mul_of_nonneg_right hi' (add_nonneg ha hb)
    dsimp [childLeft] at hx
    nlinarith

theorem gap_disjoint_children {L a b : ℝ} {i j : ℕ}
    (ha : 0 < a) (hb : 0 < b) : Disjoint (subdivisionGap L a b i) (childInterval L a b j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases hji : j ≤ i
  · have hh := (childLeft_strictMono (L := L) ha hb.le).monotone hji
    exact (not_lt_of_ge (hy.2.trans (add_le_add hh le_rfl))) hx.1
  · have hh := (childLeft_strictMono (L := L) ha hb.le).monotone (show i+1 ≤ j by omega)
    exact (not_lt_of_ge (hh.trans hy.1)) hx.2

theorem parent_covered_by_children_and_gaps {L a b x : ℝ} {m : ℕ}
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Icc L (L+m*a+(m-1 : ℕ)*b)) :
    (∃ i < m, x ∈ childInterval L a b i) ∨
      ∃ i, i+1 < m ∧ x ∈ subdivisionGap L a b i := by
  have hstep : 0 < a+b := add_pos ha hb
  let i := Nat.floor ((x-L)/(a+b))
  have hx0 : 0 ≤ (x-L)/(a+b) := div_nonneg (sub_nonneg.mpr hx.1) hstep.le
  have hlow : (i : ℝ)*(a+b) ≤ x-L := (le_div_iff₀ hstep).mp (Nat.floor_le hx0)
  have hupp : x-L < ((i : ℝ)+1)*(a+b) := (div_lt_iff₀ hstep).mp (Nat.lt_floor_add_one _)
  have hi : i < m := by
    apply (Nat.floor_lt hx0).mpr
    apply (div_lt_iff₀ hstep).mpr
    have hm1 : 1 ≤ m := hm
    rw [Nat.cast_sub hm1, Nat.cast_one] at hx
    nlinarith [hx.2]
  by_cases hchild : x ≤ childLeft L a b i+a
  · exact Or.inl ⟨i, hi, ⟨by dsimp [childLeft]; linarith, hchild⟩⟩
  · refine Or.inr ⟨i, ?_, ⟨lt_of_not_ge hchild, ?_⟩⟩
    · by_contra hn
      have he : i = m-1 := by omega
      rw [he] at hchild
      have hm1 : 1 ≤ m := hm
      simp only [childLeft, Nat.cast_sub hm1, Nat.cast_one] at hchild
      rw [Nat.cast_sub hm1, Nat.cast_one] at hx
      linarith [hx.2]
    · dsimp [childLeft]
      push_cast
      linarith


theorem subdivisionGap_subset_parent {L a b : ℝ} {m i : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hi : i+1 < m) :
    subdivisionGap L a b i ⊆ Icc L (L+m*a+(m-1 : ℕ)*b) := by
  have hl := childInterval_subset_parent (L := L) ha hb (show i < m by omega)
    (show childLeft L a b i+a ∈ childInterval L a b i by exact ⟨by linarith, le_rfl⟩)
  have hr := childInterval_subset_parent (L := L) ha hb hi
    (show childLeft L a b (i+1) ∈ childInterval L a b (i+1) by exact ⟨le_rfl, by linarith⟩)
  intro x hx
  exact ⟨hl.1.trans hx.1.le, hx.2.le.trans hr.2⟩

theorem subdivisionGap_pairwise_disjoint {L a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Pairwise (fun i j : ℕ => Disjoint (subdivisionGap L a b i) (subdivisionGap L a b j)) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (by omega)).symm
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := (childLeft_strictMono (L := L) ha hb.le).monotone (show i+1 ≤ j by omega)
  have hl : childLeft L a b j < x := by linarith [hy.1]
  exact (not_lt_of_ge (hx.2.le.trans hh)) hl


/-- A subinterval contains a consecutive block of full children whose total
length loses at most two child lengths beyond the factor one half. -/
theorem exists_full_children_block {L a b A B : ℝ} {m : ℕ}
    (hm : 0 < m) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hA : L ≤ A) (hB : B ≤ L+m*a+(m-1 : ℕ)*b) (hlen : 4*a ≤ B-A) :
    ∃ p q : ℕ, p ≤ q ∧ q ≤ m ∧
      (∀ i ∈ Finset.Ico p q, childInterval L a b i ⊆ Icc A B) ∧
      (B-A)/2-2*a ≤ ((q-p : ℕ) : ℝ)*a := by
  let p := Nat.ceil ((A-L)/(a+b))
  let q := Nat.floor ((B-L)/(a+b))
  have hstep : 0 < a+b := add_pos_of_pos_of_nonneg ha hb
  have hA0 : 0 ≤ (A-L)/(a+b) := div_nonneg (sub_nonneg.mpr hA) hstep.le
  have hB0 : 0 ≤ (B-L)/(a+b) := div_nonneg (by linarith) hstep.le
  have hpLo : A-L ≤ (p : ℝ)*(a+b) := (div_le_iff₀ hstep).mp (Nat.le_ceil _)
  have hpHi : (p : ℝ)*(a+b) < A-L+(a+b) := by
    have hh := Nat.ceil_lt_add_one hA0
    have hid : (A-L)/(a+b)+1 = (A-L+(a+b))/(a+b) := by field_simp
    rw [hid] at hh
    exact (lt_div_iff₀ hstep).mp hh
  have hqLo : B-L-(a+b) < (q : ℝ)*(a+b) := by
    have hh := (div_lt_iff₀ hstep).mp (Nat.lt_floor_add_one ((B-L)/(a+b)))
    linarith
  have hqHi : (q : ℝ)*(a+b) ≤ B-L := (le_div_iff₀ hstep).mp (Nat.floor_le hB0)
  have hpq : p ≤ q := by
    by_contra hh
    have hqp : (q : ℝ) ≤ p := by exact_mod_cast (show q ≤ p by omega)
    have hpq' := mul_le_mul_of_nonneg_right hqp hstep.le
    nlinarith
  have hqm : q ≤ m := by
    apply Nat.floor_le_of_le
    apply (div_le_iff₀ hstep).mpr
    have hm1 : 1 ≤ m := hm
    rw [Nat.cast_sub hm1, Nat.cast_one] at hB
    nlinarith
  refine ⟨p, q, hpq, hqm, ?_, ?_⟩
  · intro i hi x hx
    have hpi : (p : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
    have hiq : (i : ℝ)+1 ≤ q := by exact_mod_cast (Finset.mem_Ico.mp hi).2
    have hlo := mul_le_mul_of_nonneg_right hpi hstep.le
    have hhi := mul_le_mul_of_nonneg_right hiq hstep.le
    change childLeft L a b i ≤ x ∧ x ≤ childLeft L a b i+a at hx
    dsimp [childLeft] at hx
    constructor <;> nlinarith
  · rw [Nat.cast_sub hpq]
    have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
    have hh := mul_nonneg (show 0 ≤ (q : ℝ)-p+2 by linarith) (sub_nonneg.mpr hba)
    nlinarith

end Erdos1132.Counterexample
