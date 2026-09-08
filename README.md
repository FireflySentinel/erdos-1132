# Erdős Problem #1132: sharp pointwise bounds for Lebesgue functions

Lean 4 formalization answering both questions of
[Erdős Problem #1132](https://www.erdosproblems.com/1132).
[`Erdos1132.theorem1`](Erdos1132/Theorems.lean) and
[`Erdos1132.theorem2`](Erdos1132/Theorems.lean) are proved from the node conditions,
and from $M>0$, alone: no analytic estimate is assumed, including the local potential
estimates cited from Tao, which are proved directly in Lean.

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
corollaries. The proof modules are grouped into [Additive/](Erdos1132/Additive/) (§§2–4),
[AlmostEverywhere/](Erdos1132/AlmostEverywhere/) (§§5–6), and
[Counterexample/](Erdos1132/Counterexample/) (§7), with common tools in
[Shared/](Erdos1132/Shared/) and node definitions in
[Interpolation.lean](Erdos1132/Interpolation.lean). Each module's opening comment
identifies its paper section. The almost-everywhere proof imports no `Additive/` modules.

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
manuscript argues differently; the conclusion is the same.

The [proof bridge](checks/FormalConjecturesBridge.lean) derives the corresponding
problem statements and is included in `lake test`.

## Use of generative AI

GPT-6 Astra proposed the arguments and drafted the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review.
The Lean formalization was generated with OpenAI Codex (GPT-6).
The author completed the manuscript and is responsible for the content.
