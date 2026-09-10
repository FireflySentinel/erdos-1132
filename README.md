# Erdős Problem #1132: sharp pointwise bounds for Lebesgue functions

Lean 4 formalization of sharp pointwise bounds for Lebesgue functions, in connection with
[Erdős Problem #1132](https://www.erdosproblems.com/1132).

For arbitrary triangular arrays, [`theorem1`](Erdos1132/Theorems.lean) proves
that $\lambda_n(x)>(2/\pi)\log n-C(x)$ infinitely often on a dense set,
with a finite constant depending on the point, and that
$\limsup_n\lambda_n(x)/\log n\ge2/\pi$ almost everywhere.
[`theorem2`](Erdos1132/Theorems.lean) disproves two uniform strengthenings:
an absolute additive constant valid for all arrays, and a constant for each
array giving a dense set of points. Its counterexample uses arbitrary
triangular arrays; the uniform-constant question for initial segments of
a single node sequence remains open.

The manuscripts are [Sharp pointwise bounds for Lebesgue functions](paper/PROOF.pdf)
and [Nonuniform additive constants for Lebesgue functions](paper/NONUNIFORM.pdf).

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1132
```

## Proof correspondence

[`Theorems.lean`](Erdos1132/Theorems.lean) collects the two main theorems and two
corollaries. The proof modules are grouped into [AlmostEverywhere/](Erdos1132/AlmostEverywhere/)
(main paper, §§2–3), [Additive/](Erdos1132/Additive/)
(main paper, §§4–6), and [Counterexample/](Erdos1132/Counterexample/)
(companion note), with common tools in
[Shared/](Erdos1132/Shared/) and node definitions in
[Interpolation.lean](Erdos1132/Interpolation.lean).
The almost-everywhere proof imports no `Additive/` modules.

| Preprint | Lean source |
|---|---|
| Chebyshev cancellation and boundary harmonic measure, §2 | [Cancellation.lean](Erdos1132/Shared/Cancellation.lean), [BoundaryMeasure.lean](Erdos1132/Shared/BoundaryMeasure.lean) |
| Positive-measure contradiction, §3 | [UniformLowSet.lean](Erdos1132/AlmostEverywhere/UniformLowSet.lean) |
| Local Riesz formula and near-equality estimate, §4 | [LocalRiesz.lean](Erdos1132/Additive/LocalRiesz.lean) |
| Local potential and quadrature, §4, proved directly in Lean | [TaoPotential.lean](Erdos1132/Additive/TaoPotential.lean), [QuadratureRate.lean](Erdos1132/Additive/QuadratureRate.lean) |
| Weighted derivative-jump energy, §5 | [JumpEnergyLower.lean](Erdos1132/Additive/JumpEnergyLower.lean) |
| High-value sets, second moments, and Baire, §6 | [HighCovers.lean](Erdos1132/Additive/HighCovers.lean), [BaireBounds.lean](Erdos1132/Shared/BaireBounds.lean) |
| Theorem 1(i) and (ii) | [Additive/Main.lean](Erdos1132/Additive/Main.lean), [AlmostEverywhere/Main.lean](Erdos1132/AlmostEverywhere/Main.lean) |
| Cantor geometry and the log-integral bound, companion §§2.1–2.2 | [CantorLogarithmicBound.lean](Erdos1132/Counterexample/CantorLogarithmicBound.lean) |
| Smooth cutoffs, companion §2.3 | [SmoothCutoffs.lean](Erdos1132/Counterexample/SmoothCutoffs.lean), [CantorSmoothSequence.lean](Erdos1132/Counterexample/CantorSmoothSequence.lean) |
| Amplitude lemma, companion §3: interior rows and the upper estimate | [AmplitudeLemma.lean](Erdos1132/Counterexample/AmplitudeLemma.lean), `amplitude_lemma` |
| Companion note, Theorem 1 | [Theorem2.lean](Erdos1132/Counterexample/Theorem2.lean), `theorem2` |
| Positive-measure and interval-constant corollaries, main §7 and companion §5 | [Theorems.lean](Erdos1132/Theorems.lean) |

In the covering argument for Theorem 1(i) the Lean proof uses bounded overlap where the
manuscript argues differently; the conclusion is the same.
The counterexample formalization retains explicit constants and cutoff choices;
the companion note gives their existence arguments.

The [proof bridge](checks/FormalConjecturesBridge.lean) derives the corresponding
problem statements and is included in `lake test`.

## Use of generative AI

GPT-6 Astra proposed the arguments and drafted the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review.
The Lean formalization was generated with OpenAI Codex (GPT-6).
The author completed the manuscript and is responsible for the content.
