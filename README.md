# Erdős Problem #1132: sharp pointwise lower bounds for Lebesgue functions

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22322281.svg)](https://doi.org/10.5281/zenodo.22322281)

Preprint on [Erdős Problem #1132](https://www.erdosproblems.com/1132): a fixed point at
which the Lebesgue function exceeds $(2/\pi)\log n$ by a bounded additive loss infinitely
often, and the sharp normalized lower bound almost everywhere.

**Qiyuan Gu**, University of Chicago, <phoenix1203@uchicago.edu>

Comments and corrections: email or issue.

## Status

| | |
|---|---|
| Manuscript | v4, 11 pages, 5 September 2026: [`PROOF.pdf`](PROOF.pdf), [`PROOF.tex`](PROOF.tex) |
| DOI | [10.5281/zenodo.22322281](https://doi.org/10.5281/zenodo.22322281) (always the latest version; this version is [10.5281/zenodo.22333216](https://doi.org/10.5281/zenodo.22333216)) |
| erdosproblems.com | listed open as of 5 September 2026; [proof claim posted](https://www.erdosproblems.com/forum/thread/1132/proof-claims) |
| Refereeing | not yet refereed |

## Abstract

For each $n$, let $\lambda_n$ be the Lebesgue function for polynomial interpolation at an
arbitrary set of $n$ distinct nodes in $[-1,1]$. We prove that there are a fixed point
$x \in (-1,1)$ and a constant $C$ such that $\lambda_n(x) > (2/\pi)\log n - C$ for
infinitely many $n$. We also prove that
$\limsup_{n\to\infty} \lambda_n(x)/\log n \ge 2/\pi$ for almost every $x \in (-1,1)$.
The first conclusion answers the bounded-loss question in the interpretation that the
constant may depend on the array and the point; the second answers the almost-everywhere
question in Erdős Problem 1132. The first proof combines Tao's local potential estimates
with a local Riesz differentiation formula, an energy estimate for nodal derivative jumps,
and a second moment argument. The second proof uses positive Cauchy transforms and
harmonic measure, and is independent of Tao's local Bernstein theory.

## Main theorem

Write $P_n(x)=\prod_{k=1}^n (x-x_{k,n})$, $\ \ell_{k,n}(x)=P_n(x)/((x-x_{k,n})P_n'(x_{k,n}))$,
and $\lambda_n(x)=\sum_{k=1}^n |\ell_{k,n}(x)|$.

**Theorem 1.** For every triangular array of distinct nodes $-1 \le x_{1,n} < \cdots < x_{n,n} \le 1$:

**(i)** There exist $x \in (-1,1)$ and a finite constant $C$ such that

$$\lambda_n(x) > \frac{2}{\pi}\log n - C$$

for infinitely many $n$.

**(ii)** For Lebesgue almost every $x \in (-1,1)$,

$$\limsup_{n\to\infty} \frac{\lambda_n(x)}{\log n} \ge \frac{2}{\pi}.$$

The constant in (i) is independent of $n$; it may depend on the array and on $x$. The rows
of the array need not be nested, so this covers the single-infinite-sequence form in which
the problem is stated on erdosproblems.com.

## Prior work

| | |
|---|---|
| Faber, Bernstein, Erdős–Turán, Erdős, Vértesi | the global lower bound for $\max_x \lambda_n(x)$: order $\log n$, then the sharp constant $2/\pi$, then error $O(\log\log n)$, then $O(1)$, then optimal asymptotics through the constant term |
| Bernstein (1931) | the set where $\limsup \lambda_n(x)/\log n \ge 2/\pi$ is everywhere dense |
| Erdős (1961) | $\max_{x\in[-1,1]} \lambda_n(x) > \frac{2}{\pi}\log n - O(1)$, for the global maximum |
| Erdős–Vértesi (1980) | $\limsup_n \lambda_n(x) = \infty$ a.e., unboundedness without a rate |
| Tao ([arXiv:2603.21453](https://arxiv.org/abs/2603.21453), Thm 1.10(i)) | $\sup_{x\in I}\lambda_n(x) \ge \frac{2}{\pi}\log n - O_I(1)$ for every fixed nondegenerate $I \subset [-1,1]$ |
| Tao (Cor. 1.11, Rem. 1.12) | for every prescribed $\omega(n)\to\infty$, a dense, indeed comeager, set of $x$ with $\lambda_n(x) \ge \frac{2}{\pi}\log n - \omega(n)$ infinitely often |

Theorem 1(i) gives a fixed additive constant at a fixed point in place of the prescribed
loss $\omega(n)$ on a dense set. Theorem 1(ii) gives the sharp normalized bound on a set of
full measure in place of a dense set.

## Method

For the first assertion, a Baire category reduction gives an interval on which
$\lambda_n \le (2/\pi)\log n + O(1)$, if the assertion is false. On that interval, Tao's
potential estimates and a local Riesz formula control derivatives of all interpolants with
bounded nodal data. A positive definite kernel then gives a sharp lower average for the
derivative jumps of $\lambda_n$ at the nodes, producing linearly many separated points with
values at least $(2/\pi)\log n - O(1)$; a second moment argument yields a set of positive
measure on which this recurs infinitely often.

The almost-everywhere assertion is proved separately. Normalized barycentric weights define
two positive Cauchy transforms whose difference is small above the real line. Harmonic
measure transfers a hypothetical upper bound on a fixed measurable set to an inequality for
a positive convolution operator; symmetry and the approximate identity property contradict
it.

## Declaration of generative AI and AI-assisted technologies

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review of the exposition. The author
reviewed the final manuscript and takes full responsibility for its content.

## Citation

```bibtex
@misc{gu2026erdos1132,
  author       = {Qiyuan Gu},
  title        = {Sharp pointwise lower bounds for Lebesgue functions},
  year         = {2026},
  doi          = {10.5281/zenodo.22322281},
  howpublished = {Preprint, Zenodo},
  note         = {Erd\H{o}s Problem 1132}
}
```

Problem statement quoted from T. F. Bloom, *Erdős Problem #1132*,
<https://www.erdosproblems.com/1132>.
