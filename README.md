# Erdős Problem #1132: sharp pointwise bounds for Lebesgue functions

Preprint on [Erdős Problem #1132](https://www.erdosproblems.com/1132): sharp pointwise
bounds for Lebesgue functions of arbitrary triangular interpolation arrays.
The paper proves a bounded additive loss on a dense set, with constants that may
depend on the point, and the sharp normalized lower bound almost everywhere.
The logarithmic order was already known from
[Erdős–Vértesi (1981), Theorem 2.1](https://www.renyi.hu/~p_erdos/1981-18.pdf).
Theorem 1(ii) supplies the sharp coefficient $2/\pi$ in the almost-everywhere
limsup lower bound.

Theorem 2 gives counterexamples to uniform additive constants. For every $M>0$,
there is an array such that every fixed $x\in(-1,1)$ eventually satisfies
$\lambda_n(x)\le(2/\pi)\log n-M$. For the same array, no single finite constant
gives a dense set of points with infinitely many lower-bound occurrences.
This counterexample does not impose nesting between rows and does not settle
the version restricted to initial segments of one infinite node sequence.
The uniform-constant question for that nested setting remains open.

For arbitrary arrays, Theorem 2 rules out both an absolute constant guaranteeing
one good point for every array and a constant depending only on the array that
guarantees a dense good-point set. Theorem 1(i) still guarantees a dense set of
points when the finite constant may vary from point to point.

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
This corollary has a different scope from Erdős–Vértesi's 1981 Theorem 2.1:
their result controls all points outside a set of arbitrarily small measure
with coefficient $\eta(\varepsilon)>0$, while this corollary controls at least
one point of each fixed positive-measure set with any coefficient $c<2/\pi$.
Neither conclusion subsumes the other. Their Corollary 2.2 gives the associated
integral estimate.

Theorem 1(i), the bounded additive loss on a dense set of points, and the complete
Theorem 2 remain outside this formalization. Selected lemmas from Section 7 are
now proved in Lean, as detailed below. The complete counterexample has received
an independent paper-proof review by a Codex agent; it is not yet a fully
Lean-verified result.

## Proof correspondence

| Preprint | Lean source |
|---|---|
| Chebyshev cancellation, §5 | [Cancellation.lean](Erdos1132/Cancellation.lean), [Scales.lean](Erdos1132/Scales.lean) |
| Boundary harmonic measure, §5 | [BoundaryMeasure.lean](Erdos1132/BoundaryMeasure.lean), `boundary_harmonic_measure` |
| Local comparison (6.4), factor $(1+Rh/\eta)^2$ | [ProofParameters.lean](Erdos1132/ProofParameters.lean), `localizationFactor` |
| Positive-measure contradiction, §6 | [UniformLowSet.lean](Erdos1132/UniformLowSet.lean), `uniform_low_set_null` |
| Set corollary, §6 | [UniformLowSet.lean](Erdos1132/UniformLowSet.lean), `eventually_exists_lower_bound` |
| Theorem 1(ii) | [Main.lean](Erdos1132/Main.lean), `ae_frequently_lower_bound`, `ae_lebesgue_limsup_shifted` |

## Formalized parts of Section 7

The following modules are imported by `Erdos1132` and included in the build,
axiom checks, and kernel replay. Their declarations live in the namespace
`Erdos1132.Counterexample`.

| Paper argument | Lean source and scope |
|---|---|
| Equation (7.1); operator stability and the local convergence estimate in §7.3 | [LogarithmicOperator.lean](Erdos1132/Counterexample/LogarithmicOperator.lean): absolute integrability, the derivative bound, quantitative control of $Lf/f$, and an $L^1$ tail bound when two functions agree near the query point |
| Distance comparison (7.5) and the smooth distance in §7.2 | [GapGeometry.lean](Erdos1132/Counterexample/GapGeometry.lean): comparison with the distance to the endpoints, size, derivative, and Lipschitz estimates on a single gap |
| Polynomial approximation and quotient stability in §7.4 | [PolynomialApproximation.lean](Erdos1132/Counterexample/PolynomialApproximation.lean): positive polynomial approximation of a positive $C^1$ function, controlling values, derivatives, and the actual integral quotient $Lf/f$ simultaneously |
| Algebraic part of Lemma 9 | [AmplitudePolynomial.lean](Erdos1132/Counterexample/AmplitudePolynomial.lean): the Chebyshev sum, its trigonometric expansion, and degree exactly $n$ |
| Degree blocks and the final quantifiers in §7.5 | [Assembly.lean](Erdos1132/Counterexample/Assembly.lean): increasing thresholds, transfer to all sufficiently large rows under explicit analytic hypotheses, and relative non-density in $(-1,1)$ |

The assembly theorem assumes a family of valid node rows, their upper estimates,
and eventual lower estimates for an auxiliary function `q`. It does not construct
that family or identify `q` with an amplitude quotient. The existing `Nodes` type
requires nodes in the closed interval; this conditional theorem does not certify
the interior-root construction in Theorem 2.

Still outside the formalization are the Cantor-set construction and global gap
gluing, the full logarithmic integral lower bound and smooth amplitude sequence,
the factorization and reciprocal-square-root approximation leading to
$|h|^{-1}$, and the phase-root and Lebesgue estimates in Lemma 9.

[Counterexample.lean](checks/Counterexample.lean) writes out the integral in the
positive approximation theorem and the Lagrange product in the relative
non-density statement. It also checks that the listed main lemmas depend only
on `propext`, `Classical.choice`, and `Quot.sound`, with no added proof assumptions
hidden as axioms.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition.
An independent Codex agent also reviewed the complete counterexample proof.
The Lean formalization was generated using OpenAI Codex (GPT-6).
Lean 4's kernel checks the proofs, and CI replays the project declarations with
`leanchecker`; verification does not use the generation tool.
