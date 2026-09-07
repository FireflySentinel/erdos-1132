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

[Statement.lean](checks/Statement.lean) writes out the node conditions and the
Lagrange product formula in full, and [Counterexample.lean](checks/Counterexample.lean)
expands the integral and Lagrange product of the amplitude rows; `lake test` checks
both together with the axiom dependencies.

Not formalized: Theorem 1(i), and, in the counterexample, the Cantor construction and
its geometric measure estimates (§§7.1–7.2), the smooth amplitude sequence (§7.3), the
factorization leading to $|h|^{-1}$ (§7.4), and the remaining analytic estimates of
Lemma 9. The assembly theorem takes the row family and its upper and lower estimates
as hypotheses.

## Proof correspondence

| Preprint | Lean source |
|---|---|
| Chebyshev cancellation, §5 | [Cancellation.lean](Erdos1132/Cancellation.lean), [Scales.lean](Erdos1132/Scales.lean) |
| Boundary harmonic measure, §5 | [BoundaryMeasure.lean](Erdos1132/BoundaryMeasure.lean), `boundary_harmonic_measure` |
| Positive-measure contradiction and the set corollary, §6 | [UniformLowSet.lean](Erdos1132/UniformLowSet.lean) |
| Theorem 1(ii) | [Main.lean](Erdos1132/Main.lean), `ae_frequently_lower_bound`, `ae_lebesgue_limsup_shifted` |
| Explicit log-integral bound (7.7) | [LogIntegralLowerBound.lean](Erdos1132/Counterexample/LogIntegralLowerBound.lean) |
| Lemma 9: amplitude polynomial, phase, interior roots | [AmplitudePolynomial.lean](Erdos1132/Counterexample/AmplitudePolynomial.lean), [AmplitudeRoots.lean](Erdos1132/Counterexample/AmplitudeRoots.lean) |
| Degree blocks, final quantifiers and non-density, §7.5 | [Assembly.lean](Erdos1132/Counterexample/Assembly.lean) |

`python3 checks/amplitude_numerics.py` evaluates the corrected finite term at
prescribed phase midpoints for three fixed polynomials and degrees $50,100,\ldots,800$.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition.
An independent Codex agent also reviewed the complete counterexample proof.
The Lean formalization was generated using OpenAI Codex (GPT-6).
