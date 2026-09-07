# Erdős Problem #1132: sharp pointwise bounds for Lebesgue functions

Preprint on [Erdős Problem #1132](https://www.erdosproblems.com/1132): for arbitrary
triangular interpolation arrays, a bounded additive loss on a dense set of points with
point-dependent constants, and the sharp normalized lower bound almost everywhere.
A counterexample shows that no uniform additive constant works for every array.
The logarithmic order was already known from
[Erdős–Vértesi (1981), Theorem 2.1](https://www.renyi.hu/~p_erdos/1981-18.pdf).

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1132
```

## Exact statement

[`ae_frequently_lower_bound`](Erdos1132/Main.lean) proves that, for every triangular
array of distinct nodes in $[-1,1]$, for almost every $x\in(-1,1)$ and every
$c<2/\pi$,

$$c\log n<\lambda_n(x)\qquad\text{for infinitely many }n.$$

Theorem 1(ii), $\limsup_{n\to\infty}\lambda_n(x)/\log n\ge 2/\pi$ almost everywhere,
follows as `ae_lebesgue_limsup_shifted`. Lean indexes these rows by `n` with
`rowSize n = n + 2`, so their logarithms are positive. Its conventions `log 0 = 0`
and `x / 0 = 0` do not affect the statements; the unshifted limsup theorem discards
the first two rows.

The set corollary is `eventually_exists_lower_bound`: for every measurable
$E\subset(-1,1)$ of positive measure and every $0<c<2/\pi$, every sufficiently
large row has some $x\in E$ with $c\log n<\lambda_n(x)$.

The complete **Theorem 2** is
[`theorem2_unshifted`](Erdos1132/Counterexample/Theorem2Unshifted.lean).
For every $M>0$, it constructs one array of distinct interior nodes such that

- every fixed $x\in(-1,1)$ eventually satisfies $\lambda_n(x)\le(2/\pi)\log n-M$;
- for every finite $C$, the points satisfying $\lambda_n(x)>(2/\pi)\log n-C$
  infinitely often form a non-dense set in $(-1,1)$.

The uniform-constant question for nested node sequences remains open.

The theorem's only hypothesis is $M>0$. The Cantor geometry, smooth amplitudes,
zero-free polynomials, actual node rows, and analytic estimates are constructed
in Lean. Theorem 1(i) remains outside the formalization.
[Statement.lean](checks/Statement.lean) and
[Counterexample.lean](checks/Counterexample.lean) write out the node conditions
and Lagrange products. `lake test` checks the complete statements and the axiom
dependencies `propext`, `Classical.choice`, and `Quot.sound`.

The manuscript is available as [PDF](paper/PROOF.pdf) and [LaTeX](paper/PROOF.tex).

## Proof correspondence

| Preprint | Lean source |
|---|---|
| Chebyshev cancellation, §5 | [Cancellation.lean](Erdos1132/Cancellation.lean), [Scales.lean](Erdos1132/Scales.lean) |
| Boundary harmonic measure, §5 | [BoundaryMeasure.lean](Erdos1132/BoundaryMeasure.lean), `boundary_harmonic_measure` |
| Positive-measure contradiction and the set corollary, §6 | [UniformLowSet.lean](Erdos1132/UniformLowSet.lean) |
| Theorem 1(ii) | [Main.lean](Erdos1132/Main.lean), `ae_frequently_lower_bound`, `ae_lebesgue_limsup_shifted` |
| Cantor geometry and the explicit log-integral bound, §§7.1–7.2 | [CantorDensity.lean](Erdos1132/Counterexample/CantorDensity.lean), [CantorGapIntegral.lean](Erdos1132/Counterexample/CantorGapIntegral.lean), [CantorLogarithmicBound.lean](Erdos1132/Counterexample/CantorLogarithmicBound.lean) |
| Smooth positive sequence, §7.3 | [CantorSmoothSequence.lean](Erdos1132/Counterexample/CantorSmoothSequence.lean), `exists_cantor_smooth_sequence` |
| Positive polynomial approximation applied to $1/v_j$, followed by root reflection, §7.4 | [AmplitudeApproximation.lean](Erdos1132/Counterexample/AmplitudeApproximation.lean), `exists_amplitude_logarithmicRatio_approximation` |
| Lemma 9: actual interior rows and the complete upper estimate | [AmplitudeLemma.lean](Erdos1132/Counterexample/AmplitudeLemma.lean), `eventually_exists_amplitude_upper_rows` |
| Uniform remainder and finite-part identity in Lemma 9 | [UniformRemainder.lean](Erdos1132/Counterexample/UniformRemainder.lean), [CoordinateIntegral.lean](Erdos1132/Counterexample/CoordinateIntegral.lean) |
| Theorem 2: both assertions for one array, §7.5 | [Theorem2.lean](Erdos1132/Counterexample/Theorem2.lean), [Theorem2Unshifted.lean](Erdos1132/Counterexample/Theorem2Unshifted.lean) |

The formal proof obtains smooth cutoffs from an open-set support function,
with value one on the prescribed gap middle halves. It uses ratio approximation
with error below $1/2$, which suffices for both conclusions. Degree blocks pass
the estimates to every sufficiently large row, not merely to a subsequence.

`python3 checks/amplitude_numerics.py` evaluates the corrected finite term at
prescribed phase midpoints for three fixed polynomials and degrees $50,100,\ldots,800$.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition.
An independent Codex agent also reviewed the complete counterexample proof.
The Lean formalization was generated using OpenAI Codex (GPT-6).
