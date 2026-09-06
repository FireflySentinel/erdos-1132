# Erdős Problem #1132: sharp pointwise lower bounds for Lebesgue functions

Preprint on [Erdős Problem #1132](https://www.erdosproblems.com/1132): a fixed point at
which the Lebesgue function exceeds $(2/\pi)\log n$ by a bounded additive loss infinitely
often, and the sharp normalized lower bound almost everywhere.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1132
```

## Exact statement

[`Erdos1132.ae_lebesgue_limsup`](Erdos1132/Main.lean) proves Theorem 1(ii): for every
triangular array of nodes, $\limsup_{n\to\infty}\lambda_n(x)/\log n\ge 2/\pi$ for almost
every $x\in(-1,1)$.

Theorem 1(i), the bounded additive loss at a fixed point, is outside this formalization.

## Proof correspondence

| Preprint | Lean result |
|---|---|
| Barycentric weights and moment cancellation, §5 | [`weight_eq_derivative`, `signedMass_cancellation`](Erdos1132/Interpolation.lean) |
| Positive transforms and `λ = H / |g|`, §5 | [`sum_split_mass`](Erdos1132/Interpolation.lean), [`lebesgue_transform`](Erdos1132/Cauchy.lean) |
| Lemma 6, Chebyshev cancellation | [`cauchy_polynomial_identity`, `cancellation_ratio_bound`](Erdos1132/Cancellation.lean), [`eventually_cancellation_bound`, `tendsto_cancellationError`](Erdos1132/Scales.lean) |
| Lemma 7, boundary harmonic measure | [`boundary_harmonic_measure`](Erdos1132/BoundaryMeasure.lean) |
| Poisson semigroup and truncated convolution, §§5–6 | [`gamma_semigroup`](Erdos1132/PoissonSemigroup.lean), [`truncatedPotential_operator`](Erdos1132/KernelOperator.lean) |
| Two boundary events and the local estimate, §6 | [`split_event_probabilities`](Erdos1132/BoundaryEvents.lean), [`truncatedPotential_low_bound`](Erdos1132/LocalLowBound.lean) |
| Symmetrization, §6 | [`symmetric_ratio_energy`](Erdos1132/SymmetricEnergy.lean), [`kernelEnergy_le_of_ratio_bound`](Erdos1132/RatioEnergy.lean) |
| Approximate identity and changing sets, §6 | [`probability_kernel_tendsto`](Erdos1132/ApproximateIdentity.lean), [`changing_kernelEnergy_tendsto`](Erdos1132/ChangingSets.lean) |
| Positive-measure contradiction, §6 | [`uniform_low_set_null`](Erdos1132/UniformLowSet.lean) |
| Theorem 1(ii) | [`ae_lebesgue_limsup`](Erdos1132/Main.lean) |

The manuscript and Lean proof both use polynomial division and `T_(m-1)`
directly for the Chebyshev step. The resulting finite bound implies the
uniform estimate `20 m^(2a) exp(-m^(1-a)/4)` for all sufficiently large `m`.
Both also use the local comparison factor `(1 + |x-y|/η)^2`, proved in
[`truncatedPotential_local`](Erdos1132/TruncatedPotential.lean).
Boundary harmonic measure is expressed as
`arg ((z-a)/(z-b)) / π` for the open interval `(a,b)`.
The changing-set limit follows from continuity in measure under translation
and the kernel tail bound.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition. The author
reviewed the final manuscript and takes full responsibility for its content.
The Lean formalization was generated using OpenAI Codex (GPT-6).
