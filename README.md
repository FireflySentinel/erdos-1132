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
The uniform-constant question for nested node sequences remains open.

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
Their Corollary 2.2 gives the associated integral estimate.

Selected lemmas from Section 7 are now proved in Lean, as detailed below.

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

The Section 7 lemmas below are proved from the hypotheses shown in their types.
Not formalized: the Cantor construction and its geometric measure estimates
(§§7.1–7.2), the construction of the smooth amplitude sequence (§7.3), the
factorization and reciprocal-square-root approximation leading to $|h|^{-1}$
(§7.4), and the phase, root, and quadrature estimates in Lemma 9.
The assembly theorem takes the row family, its upper estimates, and the eventual
lower estimates for $q$ as hypotheses. Theorem 1(i) also remains outside the
formalization.

| Paper argument | Lean source and result | Hypotheses |
|---|---|---|
| Equation (7.1), quotient stability, and local convergence in §7.3 | [LogarithmicOperator.lean](Erdos1132/Counterexample/LogarithmicOperator.lean): integrability, derivative and quotient bounds, and an $L^1$ tail estimate. | Derivative bounds, positive denominator bounds for quotients, or local equality and an integrable difference for the tail estimate. |
| Distance comparison (7.5) in §7.2 | [GapGeometry.lean](Erdos1132/Counterexample/GapGeometry.lean): size, derivative, distance, and Lipschitz bounds on one gap. | Ordered gap endpoints and a point in the specified open or closed gap. |
| Numerical inequalities (7.11)–(7.12) | [Constants.lean](Erdos1132/Counterexample/Constants.lean): the real-power contraction, the exponential choice of $\rho$, and the cutoff-index cancellation. | $T\ge16$ for the contraction; $A>1$ and $0<r\le\exp(-1024(A+40))/2$ for the scale estimates; $j>0$ for the cutoff-index cancellation. |
| Explicit log-integral bound (7.7), including near and far integrals and the choice of $\rho$ | [LogIntegralLowerBound.lean](Erdos1132/Counterexample/LogIntegralLowerBound.lean): $Lu/u\ge\frac1{512}\log(1/(4r))-32$ and $Lu/u>A+2$ at the chosen scale. | Measurable $r$ with $0\le r\le2$, $r(x)>0$, the stated size and distance bounds, and the cumulative ball-measure comparison for $U=\{r\ne0\}$. |
| Cutoff estimate on $F$ in §7.3 | [SmoothLowerBound.lean](Erdos1132/Counterexample/SmoothLowerBound.lean): $(A+1)v_j(x)\le Lv_j(x)$ for the explicit profile and cutoff index. | $j>0$, measurable $r,\chi$, $0\le r\le2$, $r(y)\le\lvert x-y\rvert$, $0\le\chi\le1$, $\chi=0$ near $x$, and $A_\tau(x)\ge k_j/16$. |
| Polynomial approximation in §7.4, applied in the paper to $v_j^{-2}$ | [PolynomialApproximation.lean](Erdos1132/Counterexample/PolynomialApproximation.lean): positive $C^1$ polynomial approximation controlling values, derivatives, and $Lp/p$. | A strictly positive function with a continuous derivative on $[-1,1]$, and a positive error tolerance. |
| Algebraic part of Lemma 9 | [AmplitudePolynomial.lean](Erdos1132/Counterexample/AmplitudePolynomial.lean): the Chebyshev sum, its trigonometric expansion, and degree exactly $n$. | Real polynomial coefficients; $n>\deg h$ for the expansion, and additionally $h(0)\ne0$ for the degree. |
| Degree blocks and final quantifiers in §7.5 | [Assembly.lean](Erdos1132/Counterexample/Assembly.lean): increasing thresholds, all-row bounds, and relative non-density in $(-1,1)$. | Valid node rows, increasing thresholds, eventual coverage by $K_j$, and the stated upper and lower estimates; an eventual upper bound on an open interval gives non-density. |

The integral proof uses [RadialComparison.lean](Erdos1132/Counterexample/RadialComparison.lean)
for the layer-cake comparison, [LogProfile.lean](Erdos1132/Counterexample/LogProfile.lean)
and [FarProfile.lean](Erdos1132/Counterexample/FarProfile.lean) for the explicit
profile and its primitive, and [InverseDistance.lean](Erdos1132/Counterexample/InverseDistance.lean)
and [RadialIntervals.lean](Erdos1132/Counterexample/RadialIntervals.lean) for the
one-dimensional integral identities. Kernel integrability and the cutoff-weighted
integral estimate are proved in Lean.

These modules are imported by `Erdos1132` and included in `lake test` and kernel
replay. [Counterexample.lean](checks/Counterexample.lean) expands the integral
and Lagrange product in the checked statements and checks the axiom dependencies
`propext`, `Classical.choice`, and `Quot.sound`.

## Numerical check

```sh
python3 checks/amplitude_numerics.py
```

This standard-library script evaluates the corrected finite term at prescribed
phase midpoints for three fixed polynomials and degrees $50,100,\ldots,800$.
The paper's numerical remark gives the formulas and compares these floating-point
values with Vértesi's constant $0.521251626\ldots$.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition.
An independent Codex agent also reviewed the complete counterexample proof.
The Lean formalization was generated using OpenAI Codex (GPT-6).
Lean 4's kernel checks the proofs, and CI replays the project declarations with
`leanchecker`; verification does not use the generation tool.
