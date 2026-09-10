import Erdos1132.Interpolation
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.IsBounded

/-! # Interval lower bounds and dense sets of recurrent points

Main paper, §6, and companion note, §5: the Baire arguments for density and interval constants.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Erdos1132

/-- Every nonempty relatively open subset of `(-1,1)` contains a
nondegenerate compact real interval. -/
theorem exists_Icc_in_relative_open
    {V : Set (Ioo (-1 : ℝ) 1)} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ l r : ℝ, l < r ∧ ∃ hI : Icc l r ⊆ Ioo (-1 : ℝ) 1,
      ∀ x (hx : x ∈ Icc l r), (⟨x, hI hx⟩ :
        Ioo (-1 : ℝ) 1) ∈ V := by
  have ho : IsOpen (Subtype.val '' V : Set ℝ) :=
    isOpen_Ioo.isOpenMap_subtype_val _ hV
  obtain ⟨x, hx⟩ := hne
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds (mem_image_of_mem _ hx))
  let l := (a + (x : ℝ)) / 2
  let r := ((x : ℝ) + b) / 2
  have hsub : Icc l r ⊆ Subtype.val '' V := by
    intro y hy
    apply hab
    dsimp [l, r] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hI : Icc l r ⊆ Ioo (-1 : ℝ) 1 := by
    rintro y hy
    obtain ⟨z, _, rfl⟩ := hsub hy
    exact z.property
  refine ⟨l, r, by dsimp [l, r]; linarith, hI, ?_⟩
  intro y hy
  obtain ⟨z, hz, heq⟩ := hsub hy
  have heq' : z = (⟨y, hI hy⟩ : Ioo (-1 : ℝ) 1) := Subtype.ext heq
  exact heq' ▸ hz

/-- Continuous functions whose high-value tail sets are dense exceed the
prescribed thresholds infinitely often on a dense set. -/
theorem dense_frequently_of_dense_tails
    {α : Type*} [TopologicalSpace α] [BaireSpace α]
    (f : ℕ → α → ℝ) (hf : ∀ n, Continuous (f n)) (a : ℕ → ℝ)
    (htail : ∀ N, Dense {x | ∃ n ≥ N, a n < f n x}) :
    Dense {x | ∃ᶠ n in atTop, a n < f n x} := by
  have hopen (N : ℕ) : IsOpen {x | ∃ n ≥ N, a n < f n x} := by
    have heq : {x | ∃ n ≥ N, a n < f n x} =
        ⋃ n ≥ N, {x | a n < f n x} := by ext; simp
    rw [heq]
    exact isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const (hf n)
  have hd := dense_iInter_of_isOpen hopen htail
  apply hd.mono
  intro x hx
  exact frequently_atTop.mpr (fun N => mem_iInter.mp hx N)

/-- An eventual lower bound for the supremum on every compact interior
interval gives a dense set of infinitely many strict occurrences, with any
fixed positive slack. The starting index can depend on the interval. -/
theorem dense_frequently_of_interval_sup
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, Continuous (f n)) (a : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 →
      ∀ᶠ n in atTop, a n ≤ sSup (f n '' Icc l r)) :
    Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ n in atTop, a n - ε < f n x} := by
  let : BaireSpace (Ioo (-1 : ℝ) 1) := isOpen_Ioo.baireSpace
  apply dense_frequently_of_dense_tails (fun n (x : Ioo (-1 : ℝ) 1) => f n x)
    (fun n => (hf n).comp continuous_subtype_val) (fun n => a n - ε)
  intro N
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨l, r, hlr, hI, hVlr⟩ := exists_Icc_in_relative_open hV hne
  obtain ⟨n, hn, hsup⟩ := ((eventually_ge_atTop N).and (hlower l r hlr hI)).exists
  obtain ⟨_, ⟨x, hx, rfl⟩, hfx⟩ :=
    exists_lt_of_lt_csSup ((nonempty_Icc.mpr hlr.le).image (f n))
      (show a n - ε < sSup (f n '' Icc l r) by linarith)
  exact ⟨⟨x, hI hx⟩, hVlr x hx, n, hn, hfx⟩

/-- Pointwise eventual upper bounds on a sequence have finite upper bounds
including the initial rows. A natural number can be used for the bound. -/
theorem exists_nat_bound_of_eventually_le {f a : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, f n ≤ a n) :
    ∃ M : ℕ, ∀ n, f n ≤ a n + M := by
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n => f n - a n) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, f n - a n ≤ 0
    filter_upwards [hf] with n hn
    exact sub_nonpos.mpr hn
  obtain ⟨C, hC⟩ := hb.bddAbove_range
  obtain ⟨M, hM⟩ := exists_nat_ge C
  refine ⟨M, fun n => ?_⟩
  have hn := hC (mem_range_self n)
  linarith

/-- Baire category turns local recurrence under a uniform upper estimate into
density of the points having some finite additive loss. -/
theorem dense_additive_good_of_local_recurrence
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, Continuous (f n)) (a : ℕ → ℝ)
    (hrec : ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 → ∀ C : ℝ,
      (∀ᶠ n in atTop, ∀ x ∈ Icc l r, f n x ≤ a n + C) →
      ∃ x ∈ Icc l r, ∃ D : ℝ, ∃ᶠ n in atTop, a n - D < f n x) :
    Dense {x : Ioo (-1 : ℝ) 1 | ∃ C : ℝ, ∃ᶠ n in atTop, a n - C < f n x} := by
  let : BaireSpace (Ioo (-1 : ℝ) 1) := isOpen_Ioo.baireSpace
  rw [dense_iff_inter_open]
  intro V hV hne
  by_contra hempty
  have hbad (x : Ioo (-1 : ℝ) 1) (hx : x ∈ V) :
      ¬∃ C : ℝ, ∃ᶠ n in atTop, a n - C < f n x := by
    intro h
    exact hempty ⟨x, hx, h⟩
  have hbound (x : V) : ∃ M : ℕ, ∀ n, f n x.val ≤ a n + M := by
    apply exists_nat_bound_of_eventually_le
    have hnot : ¬∃ᶠ n in atTop, a n < f n x.val := by
      intro hh
      exact hbad x.val x.property ⟨0, by simpa using hh⟩
    simpa only [not_frequently, not_lt] using hnot
  let F (M : ℕ) : Set V := {x | ∀ n, f n x.val ≤ a n + M}
  have hclosed (M : ℕ) : IsClosed (F M) := by
    have heq : F M = ⋂ n : ℕ, {x : V | f n x.val ≤ a n + M} := by ext; simp [F]
    rw [heq]
    exact isClosed_iInter fun n => isClosed_le
      ((hf n).comp (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
  have hcover : ⋃ M, F M = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨M, hM⟩ := hbound x
    exact mem_iUnion.mpr ⟨M, hM⟩
  let : BaireSpace V := hV.baireSpace
  let : Nonempty V := hne.to_subtype
  obtain ⟨M, hM⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  let W : Set (Ioo (-1 : ℝ) 1) := Subtype.val '' interior (F M)
  have hW : IsOpen W := hV.isOpenMap_subtype_val _ isOpen_interior
  obtain ⟨l, r, hlr, hI, hWI⟩ := exists_Icc_in_relative_open hW (hM.image Subtype.val)
  have hupper : ∀ n, ∀ x ∈ Icc l r, f n x ≤ a n + M := by
    intro n x hx
    obtain ⟨z, hz, heq⟩ := hWI x hx
    have hz' := (interior_subset hz : z ∈ F M) n
    have heq' : (z.val : ℝ) = x := congrArg Subtype.val heq
    simpa only [heq'] using hz'
  obtain ⟨x, hx, D, hD⟩ := hrec l r hlr hI M (Eventually.of_forall hupper)
  obtain ⟨z, _, heq⟩ := hWI x hx
  exact hbad ⟨x, hI hx⟩ (heq ▸ z.property) ⟨D, hD⟩

end Erdos1132
