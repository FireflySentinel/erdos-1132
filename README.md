# Erdős Problem #1132: sharp pointwise bounds for Lebesgue functions

[Preprint](paper/PROOF.pdf) on [Erdős Problem #1132](https://www.erdosproblems.com/1132): for arbitrary
triangular interpolation arrays, a bounded additive loss on a dense set of points with
point-dependent constants, and the sharp normalized lower bound almost everywhere.
For general arrays, no additive constant uniform in $x$ gives a dense set of points
attaining the lower bound infinitely often.
The logarithmic order was already known from
[Erdős–Vértesi (1981), Theorem 2.1](https://www.renyi.hu/~p_erdos/1981-18.pdf).

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
python3 scripts/prune_obsolete_modules.py
lake test
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1132
```

## Exact statement

**Theorem 1** is [`Erdos1132.theorem1`](Erdos1132/Theorems.lean). For every triangular array
of distinct nodes in $[-1,1]$, with exactly $n$ nodes in row $n$:

- the points $x\in(-1,1)$ for which some finite $C(x)$ satisfies
  $\lambda_n(x)>(2/\pi)\log n-C(x)$ infinitely often form a dense set;
- $\limsup_{n\to\infty}\lambda_n(x)/\log n\ge 2/\pi$ almost everywhere.

**Theorem 2** is [`Erdos1132.theorem2`](Erdos1132/Theorems.lean). For every $M>0$
it constructs one array of distinct interior nodes such that

- every fixed $x\in(-1,1)$ eventually satisfies $\lambda_n(x)\le(2/\pi)\log n-M$;
- for every finite $C$, the points satisfying $\lambda_n(x)>(2/\pi)\log n-C$
  infinitely often form a non-dense set.

Both are proved from the node conditions, and from $M>0$, alone. The uniform-constant
question for nested node sequences remains open.

`Erdos1132.positive_measure_lower_bound` gives the set corollary: for every measurable
$E\subset(-1,1)$ of positive measure and every $0<c<2/\pi$, every sufficiently large row
has some $x\in E$ with $c\log n<\lambda_n(x)$.
`Erdos1132.no_uniform_interval_constant` includes both assertions of Theorem 2
and the absence of a uniform interval constant for the same array. Its only
hypothesis is $M>0$.

## Proof correspondence

Start with the paper's Introduction and Organization subsection, then open
[`Theorems.lean`](Erdos1132/Theorems.lean), which collects the two main theorems and
two corollaries. [Statement.lean](checks/Statement.lean) and
[Counterexample.lean](checks/Counterexample.lean) write out the node conditions
and Lagrange products; [Check.lean](checks/Check.lean) checks their axioms.

The proof modules are grouped into [Additive/](Erdos1132/Additive/) (§§2–4),
[AlmostEverywhere/](Erdos1132/AlmostEverywhere/) (§§5–6), and
[Counterexample/](Erdos1132/Counterexample/) (§7), with common tools in
[Shared/](Erdos1132/Shared/) and node definitions in
[Interpolation.lean](Erdos1132/Interpolation.lean). Each module's opening comment
identifies its paper section. The almost-everywhere proof imports no `Additive/`
modules and does not use Tao's estimates.

| Preprint | Lean source |
|---|---|
| Local Riesz formula and near-equality estimate, §2 | [LocalRiesz.lean](Erdos1132/Additive/LocalRiesz.lean) |
| Local potential and quadrature, §2, proved directly in Lean | [TaoPotential.lean](Erdos1132/Additive/TaoPotential.lean), [QuadratureRate.lean](Erdos1132/Additive/QuadratureRate.lean) |
| Weighted derivative-jump energy, §3 | [JumpEnergyLower.lean](Erdos1132/Additive/JumpEnergyLower.lean) |
| High-value sets, second moments, and Baire, §4 | [HighCovers.lean](Erdos1132/Additive/HighCovers.lean), [BaireBounds.lean](Erdos1132/Shared/BaireBounds.lean) |
| Theorem 1(i) and (ii) | [Additive/Main.lean](Erdos1132/Additive/Main.lean), [AlmostEverywhere/Main.lean](Erdos1132/AlmostEverywhere/Main.lean) |
| Chebyshev cancellation and boundary harmonic measure, §5 | [Cancellation.lean](Erdos1132/Shared/Cancellation.lean), [BoundaryMeasure.lean](Erdos1132/Shared/BoundaryMeasure.lean) |
| Positive-measure contradiction, §6 | [UniformLowSet.lean](Erdos1132/AlmostEverywhere/UniformLowSet.lean) |
| Cantor geometry and the log-integral bound, §§7.1–7.2 | [CantorLogarithmicBound.lean](Erdos1132/Counterexample/CantorLogarithmicBound.lean) |
| Smooth cutoffs, §7.3 | [SmoothCutoffs.lean](Erdos1132/Counterexample/SmoothCutoffs.lean), [CantorSmoothSequence.lean](Erdos1132/Counterexample/CantorSmoothSequence.lean) |
| Amplitude lemma, §7.4: interior rows and the upper estimate | [AmplitudeLemma.lean](Erdos1132/Counterexample/AmplitudeLemma.lean), `amplitude_lemma` |
| Theorem 2 | [Theorem2.lean](Erdos1132/Counterexample/Theorem2.lean), `theorem2` |
| Positive-measure and interval-constant corollaries, §8 | [Theorems.lean](Erdos1132/Theorems.lean) |

In the covering argument for Theorem 1(i) the Lean proof uses bounded overlap where the
manuscript argues differently; the conclusion is the same. Theorem 2 uses the
same smooth cutoff construction and fixed ratio-approximation error below $1/2$
in the manuscript and Lean.

The [proof bridge](checks/FormalConjecturesBridge.lean) derives the corresponding
problem statements and is included in `lake test`.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition.
The Lean formalization was generated using OpenAI Codex (GPT-6).
