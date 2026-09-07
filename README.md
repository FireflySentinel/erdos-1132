# Erdős Problem #1132: sharp pointwise bounds for Lebesgue functions

Preprint on [Erdős Problem #1132](https://www.erdosproblems.com/1132): for arbitrary
triangular interpolation arrays, a bounded additive loss on a dense set of points with
point-dependent constants, and the sharp normalized lower bound almost everywhere.
For general arrays, no additive constant uniform in $x$, absolute or array-dependent,
guarantees a dense set of points attaining the lower bound infinitely often.
The logarithmic order was already known from
[Erdős–Vértesi (1981), Theorem 2.1](https://www.renyi.hu/~p_erdos/1981-18.pdf).

Release [v2.0.0](https://github.com/FireflySentinel/erdos-1132/releases/tag/v2.0.0)
is archived as [Zenodo v9](https://doi.org/10.5281/zenodo.22646508).

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1132
```

## Exact statement

The complete **Theorem 1** is [`theorem1`](Erdos1132/AdditiveMain.lean).
For every triangular array of distinct nodes in $[-1,1]$, it proves both:

- the points $x\in(-1,1)$ for which some finite $C(x)$ satisfies
  $\lambda_n(x)>(2/\pi)\log n-C(x)$ infinitely often form a dense set;
- $\limsup_{n\to\infty}\lambda_n(x)/\log n\ge 2/\pi$ almost everywhere.

The individual conclusions are `dense_additive_lower_bound` and
[`ae_lebesgue_limsup`](Erdos1132/Main.lean). These statements use exactly `n`
nodes in row `n`. The almost-everywhere proof internally uses rows of size
`n + 2`; reindexing removes this shift in the final theorem.

The set corollary is `eventually_exists_lower_bound_unshifted`: for every
measurable $E\subset(-1,1)$ of positive measure and every $0<c<2/\pi$, every
sufficiently large row has some $x\in E$ with $c\log n<\lambda_n(x)$.

The complete **Theorem 2** is
[`theorem2`](Erdos1132/Counterexample/Theorem2.lean).
For every $M>0$, it constructs one array of distinct interior nodes such that

- every fixed $x\in(-1,1)$ eventually satisfies $\lambda_n(x)\le(2/\pi)\log n-M$;
- for every finite $C$, the points satisfying $\lambda_n(x)>(2/\pi)\log n-C$
  infinitely often form a non-dense set in $(-1,1)$.

The uniform-constant question for nested node sequences remains open.

Both theorems are proved from the node conditions (and $M>0$) alone; no
analytic estimate is assumed, including the local potential estimates cited
from Tao.
[`Corollaries.lean`](Erdos1132/Counterexample/Corollaries.lean) also proves the
absence of a uniform interval constant for the same counterexample array.
[Statement.lean](checks/Statement.lean) and
[Counterexample.lean](checks/Counterexample.lean) write out the node conditions
and Lagrange products. `lake test` checks the complete statements and the axiom
dependencies `propext`, `Classical.choice`, and `Quot.sound`.

The manuscript is available as [PDF](paper/PROOF.pdf) and [LaTeX](paper/PROOF.tex).

## Proof correspondence

| Preprint | Lean source |
|---|---|
| Local Riesz formula and near-equality estimate, §2 | [FiniteRiesz.lean](Erdos1132/FiniteRiesz.lean), [LocalRiesz.lean](Erdos1132/LocalRiesz.lean) |
| Local potential, positive density, and quadrature, §2: proved directly, not assumed | [TaoPotential.lean](Erdos1132/TaoPotential.lean), [DensityPositive.lean](Erdos1132/DensityPositive.lean), [QuadratureRate.lean](Erdos1132/QuadratureRate.lean) |
| Sharp interpolant derivatives and nearby high values, §2 | [InterpolantDerivative.lean](Erdos1132/InterpolantDerivative.lean), [InterpolantSecondDerivative.lean](Erdos1132/InterpolantSecondDerivative.lean), [InterpolantPeak.lean](Erdos1132/InterpolantPeak.lean) |
| Weighted derivative-jump energy, §3 | [DerivativeJumps.lean](Erdos1132/DerivativeJumps.lean), [RieszEnergy.lean](Erdos1132/RieszEnergy.lean), [JumpEnergyLower.lean](Erdos1132/JumpEnergyLower.lean) |
| High-value sets, second moments, and Baire, §4 | [HighCovers.lean](Erdos1132/HighCovers.lean), [LocalRecurrence.lean](Erdos1132/LocalRecurrence.lean), [BaireBounds.lean](Erdos1132/BaireBounds.lean) |
| Theorem 1(i), and both parts together | [AdditiveMain.lean](Erdos1132/AdditiveMain.lean), `dense_additive_lower_bound`, `theorem1` |
| Chebyshev cancellation, §5 | [Cancellation.lean](Erdos1132/Cancellation.lean), [Scales.lean](Erdos1132/Scales.lean) |
| Boundary harmonic measure, §5 | [BoundaryMeasure.lean](Erdos1132/BoundaryMeasure.lean), `boundary_harmonic_measure` |
| Positive-measure contradiction and the set corollary, §6 | [UniformLowSet.lean](Erdos1132/UniformLowSet.lean) |
| Theorem 1(ii) | [Main.lean](Erdos1132/Main.lean), `ae_lebesgue_limsup` |
| Cantor geometry and the explicit log-integral bound, §§7.1–7.2 | [CantorDensity.lean](Erdos1132/Counterexample/CantorDensity.lean), [CantorGapIntegral.lean](Erdos1132/Counterexample/CantorGapIntegral.lean), [CantorLogarithmicBound.lean](Erdos1132/Counterexample/CantorLogarithmicBound.lean) |
| Smooth positive sequence, §7.3 | [CantorSmoothSequence.lean](Erdos1132/Counterexample/CantorSmoothSequence.lean), `exists_cantor_smooth_sequence` |
| Positive polynomial approximation applied to $1/v_j$, followed by root reflection, §7.4 | [AmplitudeApproximation.lean](Erdos1132/Counterexample/AmplitudeApproximation.lean), `exists_amplitude_logarithmicRatio_approximation` |
| Lemma 9: interior rows and the complete upper estimate | [AmplitudeLemma.lean](Erdos1132/Counterexample/AmplitudeLemma.lean), `amplitude_lemma` |
| Uniform remainder and finite-part identity in Lemma 9 | [UniformRemainder.lean](Erdos1132/Counterexample/UniformRemainder.lean), [CoordinateIntegral.lean](Erdos1132/Counterexample/CoordinateIntegral.lean) |
| Theorem 2 and the interval-constant corollary | [Theorem2.lean](Erdos1132/Counterexample/Theorem2.lean), [Theorem2Shifted.lean](Erdos1132/Counterexample/Theorem2Shifted.lean), [Corollaries.lean](Erdos1132/Counterexample/Corollaries.lean) |

The formal proof of Theorem 1(i) uses circular contours for the finite Riesz
formula, proves the needed Lipschitz quadrature estimate directly from the
Poisson representation, and uses bounded overlap to estimate the high-value
covers. The manuscript uses the same circular contour and direct quadrature
estimate; Lean uses bounded overlap in the final covering argument.

For Theorem 2, the formal proof obtains smooth cutoffs from an open-set support function,
with value one on the prescribed gap middle halves. It uses ratio approximation
with error below $1/2$, which suffices for both conclusions. Degree blocks pass
the estimates to every sufficiently large row, not merely to a subsequence.

`python3 checks/amplitude_numerics.py` evaluates the corrected finite term at
prescribed phase midpoints for three fixed polynomials and degrees $50,100,\ldots,800$.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition.
The Lean formalization was generated using OpenAI Codex (GPT-6).
