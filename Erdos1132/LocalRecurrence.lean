import Erdos1132.HighCovers
import Erdos1132.LogarithmicRecurrence

/-! # Positive-measure recurrence of the sharp additive lower bound -/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace Erdos1132

theorem local_additive_recurrence (X : ∀ n, Nodes n) {a b c : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc a b,
      (X n).lebesgue x ≤ logarithmicLevel (2/Real.pi) c n) :
    ∃ D > 0, 0 < volume {x | x ∈ Icc a b ∧
      ∃ᶠ n : ℕ in atTop, (2/Real.pi)*Real.log n-D < (X n).lebesgue x} := by
  obtain ⟨A, D, hD, c₁, hc₁, C, hC, N, hAm, hrow, hpair⟩ := exists_high_covers X hab hI hupper
  let μ := volume.restrict (Icc a b)
  have hμ (n : ℕ) (hn : N ≤ n) : μ.real (A n) = volume.real (A n) := by
    rw [measureReal_restrict_apply (hAm n), inter_eq_left.mpr (hrow n hn).2.2.1]
  have hμpair (n m : ℕ) (hn : N ≤ n) : μ.real (A n ∩ A m) = volume.real (A n ∩ A m) := by
    rw [measureReal_restrict_apply ((hAm n).inter (hAm m)),
      inter_eq_left.mpr (Set.inter_subset_left.trans (hrow n hn).2.2.1)]
  have hfreq := measure_frequently_pos_of_logarithmic_bounds μ A hAm hc₁ hC N
    (fun n hn => by rw [hμ n hn]; exact (hrow n hn).2.2.2.2.1)
    (fun n hn => by rw [hμ n hn]; exact (hrow n hn).2.2.2.2.2)
    (fun n m hn hm hnm => by rw [hμpair n m hn]; exact hpair n m hn hm hnm)
  refine ⟨D+1, by positivity, ?_⟩
  have hle : μ {x | ∃ᶠ n : ℕ in atTop, x ∈ A n} ≤
      volume {x | ∃ᶠ n : ℕ in atTop, x ∈ A n} := Measure.restrict_apply_le (Icc a b) _
  apply (hfreq.trans_le hle).trans_le
  apply measure_mono
  intro x hx
  have htail : ∃ᶠ n : ℕ in atTop, x ∈ A n ∧ N ≤ n := hx.and_eventually (eventually_ge_atTop N)
  obtain ⟨n, hxn, hn⟩ := htail.exists
  refine ⟨(hrow n hn).2.2.1 hxn, ?_⟩
  apply htail.mono
  intro m hm
  have hh := (hrow m hm.2).2.2.2.1 x hm.1
  linarith

end Erdos1132
