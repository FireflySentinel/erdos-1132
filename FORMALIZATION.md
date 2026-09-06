# Lean formalization of the almost-everywhere bound

This project proves Theorem 1(ii) of the preprint, following §§5–6 of
[`PROOF.tex`](paper/PROOF.tex).
The bounded additive loss assertion, Theorem 1(i), is outside this formalization.
The almost-everywhere proof is independent of Tao's local Bernstein theory.

## Exact statement

The main theorem is [`Erdos1132.ae_lebesgue_limsup`](Erdos1132/Main.lean):

```lean
theorem ae_lebesgue_limsup (X : ∀ n, Nodes n) :
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1),
      ((2 / Real.pi : ℝ) : EReal) ≤
        limsup (fun n => (((X n).lebesgue x /
          Real.log (n : ℝ) : ℝ) : EReal)) atTop
```

`Nodes m` consists of an injective map `Fin m → ℝ` with values in `[-1,1]`.
`lebesgue` is the sum of the absolute values of the Lagrange cardinal
polynomials. The rows are arbitrary and need not be nested. The limsup is
taken in the extended real line.

The theorem `ae_frequently_lower_bound` also gives the equivalent formulation:
at almost every interior point, every `c < 2 / π` satisfies
`c * log (n + 2) < λ_(n+2)(x)` for infinitely many `n`. The proof works with
rows of size `n + 2`; `limsup_nat_add` restores the original indexing.

## Build

Lean is pinned to `v4.33.0-rc2`; the mathlib revision and its dependencies are
recorded in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Check.lean
lake env leanchecker Erdos1132
```

[`Check.lean`](Check.lean) checks the axiom dependencies of the main theorem
and two central intermediate results: `propext`, `Classical.choice`, and
`Quot.sound`. The [GitHub workflow](.github/workflows/lean.yml) runs the build,
axiom checks, and kernel replay.

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
