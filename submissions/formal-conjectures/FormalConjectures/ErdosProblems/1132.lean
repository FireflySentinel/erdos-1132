/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1132

*References:*
- [erdosproblems.com/1132](https://www.erdosproblems.com/1132)
- [Be31] Bernstein, S., Sur la limitation des valeurs d'un polynome $P_n(x)$ de degré $n$
  sur tout un segment par ses valeurs en $(n+1)$ points du segment.
  Izv. Akad. Nauk. SSSR (1931), 1025–1050.
- [Er61c] Erdős, P., Problems and results on the theory of interpolation. II.
  Acta Math. Acad. Sci. Hungar. (1961), 235–244.
- [Ta26b] Tao, T., Local Bernstein theory, and lower bounds for Lebesgue constants.
  arXiv:2603.21453 (2026).
- [Gu26] Gu, Q., Sharp pointwise bounds for Lebesgue functions.
  https://github.com/FireflySentinel/erdos-1132
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos1132

/-- The Lebesgue function of one row of interpolation nodes. -/
noncomputable def rowLebesgue {n : ℕ} (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, (x - X j) / (X i - X j)|

/--
For $x_1,\ldots,x_n\in [-1,1]$ let
$$
l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},
$$
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.
Let $x_1,x_2,\ldots\in [-1,1]$ be an infinite sequence, and let
$$
L_n(x) = \sum_{1\leq k\leq n}\lvert l_k(x)\rvert,
$$
where each $l_k(x)$ is defined above with respect to $x_1,\ldots,x_n$.
Must there exist $x\in (-1,1)$ such that
$$
L_n(x) >\frac{2}{\pi}\log n-O(1)
$$
for infinitely many $n$?

The nodes are distinct. Here the additive constant may depend on the sequence
and the chosen point. Gu [Gu26] proves this form of the assertion.
-/
@[category research solved, AMS 26 41, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-1132/blob/0a245ce8833d4ee1d3edaffb79510cedbaf365cc/checks/FormalConjecturesBridge.lean#L50"]
theorem erdos_1132.parts.i :
    answer(True) ↔ ∀ X : ℕ → ℝ, Function.Injective X →
      (∀ i, X i ∈ Icc (-1 : ℝ) 1) → ∃ x ∈ Ioo (-1 : ℝ) 1, ∃ C : ℝ,
        ∃ᶠ n : ℕ in atTop,
          (2 / Real.pi) * Real.log (n : ℝ) - C < rowLebesgue (fun i : Fin n => X i) x := by
  sorry

/--
Is it true that
$$
\limsup_{n\to \infty}\frac{L_n(x)}{\log n}\geq \frac{2}{\pi}
$$
for almost all $x\in (-1,1)$?

Gu [Gu26] proves the affirmative answer. The limsup is taken in the extended reals.
Lean sets $\log 0=\log 1=0$ and division by zero to zero; the terms at $n=0,1$
do not affect the limsup.
-/
@[category research solved, AMS 26 41, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-1132/blob/0a245ce8833d4ee1d3edaffb79510cedbaf365cc/checks/FormalConjecturesBridge.lean#L70"]
theorem erdos_1132.parts.ii :
    answer(True) ↔ ∀ X : ℕ → ℝ, Function.Injective X →
      (∀ i, X i ∈ Icc (-1 : ℝ) 1) →
      ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
        ((2 / Real.pi : ℝ) : EReal) ≤
          limsup (fun n : ℕ =>
            ((rowLebesgue (fun i : Fin n => X i) x / Real.log (n : ℝ) : ℝ) : EReal)) atTop := by
  sorry

/--
For every triangular array of distinct nodes, the points with a finite additive
loss infinitely often form a dense set, and the normalized limsup is at least
$2/\pi$ almost everywhere [Gu26, Theorem 1].
-/
@[category research solved, AMS 26 41, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-1132/blob/0a245ce8833d4ee1d3edaffb79510cedbaf365cc/checks/FormalConjecturesBridge.lean#L33"]
theorem erdos_1132.variants.triangular_arrays :
    ∀ X : ∀ n : ℕ, Fin n → ℝ, (∀ n, Function.Injective (X n)) →
      (∀ n i, X n i ∈ Icc (-1 : ℝ) 1) →
      Dense {x : Ioo (-1 : ℝ) 1 | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < rowLebesgue (X n) x} ∧
      (∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
        ((2 / Real.pi : ℝ) : EReal) ≤
          limsup (fun n => ((rowLebesgue (X n) x / Real.log (n : ℝ) : ℝ) : EReal)) atTop) := by
  sorry

/--
For every $M>0$, one triangular array has eventual deficit at least $M$ at every
fixed interior point; for the same array, each finite-constant recurrent lower-bound
set is non-dense [Gu26, Theorem 2].
-/
@[category research solved, AMS 26 41, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-1132/blob/0a245ce8833d4ee1d3edaffb79510cedbaf365cc/checks/FormalConjecturesBridge.lean#L89"]
theorem erdos_1132.variants.nonuniform_arrays :
    ∀ M : ℝ, 0 < M → ∃ X : ∀ n : ℕ, Fin n → ℝ,
      (∀ n, Function.Injective (X n)) ∧ (∀ n i, X n i ∈ Ioo (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, ∀ᶠ n : ℕ in atTop,
        rowLebesgue (X n) x ≤ (2 / Real.pi) * Real.log (n : ℝ) - M) ∧
      (∀ C : ℝ, ¬Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ n : ℕ in atTop,
        (2 / Real.pi) * Real.log (n : ℝ) - C < rowLebesgue (X n) x}) := by
  sorry

/--
Does one absolute additive constant work for every infinite sequence of distinct
nodes? This is the uniform interpretation discussed in [Ta26b, Remark 1.12].
-/
@[category research open, AMS 26 41]
theorem erdos_1132.variants.absolute_constant_nested :
    answer(sorry) ↔ ∃ C : ℝ, ∀ X : ℕ → ℝ, Function.Injective X →
      (∀ i, X i ∈ Icc (-1 : ℝ) 1) → ∃ x ∈ Ioo (-1 : ℝ) 1,
        ∃ᶠ n : ℕ in atTop,
          (2 / Real.pi) * Real.log (n : ℝ) - C < rowLebesgue (fun i : Fin n => X i) x := by
  sorry

@[category test, AMS 26 41]
example (X : Fin 0 → ℝ) (x : ℝ) : rowLebesgue X x = 0 := by
  simp [rowLebesgue]

@[category test, AMS 26 41]
example (X : Fin 1 → ℝ) (x : ℝ) : rowLebesgue X x = 1 := by
  simp [rowLebesgue]

end Erdos1132
