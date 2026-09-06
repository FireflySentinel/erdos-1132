# Erdős Problem #1132: sharp pointwise lower bounds for Lebesgue functions

Preprint on [Erdős Problem #1132](https://www.erdosproblems.com/1132): a fixed point at
which the Lebesgue function exceeds $(2/\pi)\log n$ by a bounded additive loss infinitely
often, and the sharp normalized lower bound almost everywhere.

[Preprint PDF](paper/PROOF.pdf) · [LaTeX source](paper/PROOF.tex) ·
[Formalization notes](FORMALIZATION.md)

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

## Declaration of generative AI and AI-assisted technologies

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition. The author
reviewed the final manuscript and takes full responsibility for its content.
The Lean formalization was generated using OpenAI Codex (GPT-6).
