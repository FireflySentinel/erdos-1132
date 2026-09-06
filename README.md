# Erdős Problem #1132: sharp pointwise bounds for Lebesgue functions

Preprint on [Erdős Problem #1132](https://www.erdosproblems.com/1132): sharp pointwise
bounds for Lebesgue functions of arbitrary triangular interpolation arrays.
The paper proves a bounded additive loss on a dense set, with constants that may
depend on the point, and the sharp normalized lower bound almost everywhere.

Theorem 2 gives counterexamples to uniform additive constants. For every $M>0$,
there is an array such that every fixed $x\in(-1,1)$ eventually satisfies
$\lambda_n(x)\le(2/\pi)\log n-M$. For the same array, no single finite constant
gives a dense set of points with infinitely many lower-bound occurrences.
This counterexample does not impose nesting between rows and does not settle
the version restricted to initial segments of one infinite node sequence.

The current manuscript is available as [PDF](paper/PROOF.pdf) and [LaTeX](paper/PROOF.tex).

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos1132
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
[Statement.lean](checks/Statement.lean) writes out the node conditions and the
Lagrange product formula in full; `lake test` checks it and the axiom dependencies.

The set corollary is `eventually_exists_lower_bound`: for every measurable
$E\subset(-1,1)$ of positive measure and every $0<c<2/\pi$, every sufficiently
large row has some $x\in E$ with $c\log n<\lambda_n(x)$. Its proof uses
`uniform_low_set_null`, whose uniform upper-bound hypothesis need hold only
infinitely often. Both statements are covered by the checks.

Theorem 1(i), the bounded additive loss on a dense set of points, and Theorem 2,
the counterexamples to uniform additive constants, are outside this formalization.
The new counterexample has received an independent paper-proof review by a Codex
agent; it is not a Lean-verified result.

## Proof correspondence

| Preprint | Lean source |
|---|---|
| Chebyshev cancellation, §5 | [Cancellation.lean](Erdos1132/Cancellation.lean), [Scales.lean](Erdos1132/Scales.lean) |
| Boundary harmonic measure, §5 | [BoundaryMeasure.lean](Erdos1132/BoundaryMeasure.lean), `boundary_harmonic_measure` |
| Local comparison (6.4), factor $(1+Rh/\eta)^2$ | [ProofParameters.lean](Erdos1132/ProofParameters.lean), `localizationFactor` |
| Positive-measure contradiction, §6 | [UniformLowSet.lean](Erdos1132/UniformLowSet.lean), `uniform_low_set_null` |
| Set corollary, §6 | [UniformLowSet.lean](Erdos1132/UniformLowSet.lean), `eventually_exists_lower_bound` |
| Theorem 1(ii) | [Main.lean](Erdos1132/Main.lean), `ae_frequently_lower_bound`, `ae_lebesgue_limsup_shifted` |

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition.
An independent Codex agent also reviewed the complete counterexample proof.
The Lean formalization was generated using OpenAI Codex (GPT-6).
Lean 4's kernel checks the proofs, and CI replays the project declarations with
`leanchecker`; verification does not use the generation tool.
