# Community contribution preparation: Erdős 1132

Prepared locally on 2026-09-07. The two questions for a nested sequence follow from the stronger triangular-array theorem. The additive constant in part (i) may depend on the point. The file also states the array counterexample and leaves the absolute-constant question for nested sequences open.

## Files

- [Formal Conjectures statement](formal-conjectures/FormalConjectures/ErdosProblems/1132.lean)
- [Proof bridge](../checks/FormalConjecturesBridge.lean)
- [Formal Conjectures PR draft](formal-conjectures/PR.md)
- [Proposed database entry](teorth/entry.yaml) and [patch](teorth/problems.patch)
- [Pinned upstream revisions](upstream.json)

The statement file follows Formal Conjectures' placeholder convention. The bridge
contains complete proofs for every declaration with a `formal_proof` link and
checks their axiom dependencies. It copies the definitions and theorem types,
omitting the contribution attributes and the identity elaborator `answer`.
`check_bridge.py` compares those sources; Lean checks the proofs.

## Reproduce the checks

In this repository, using its pinned Lean 4.33.0 toolchain:

```sh
python3 submissions/check_bridge.py
lake test
```

In a Formal Conjectures checkout at the revision in `upstream.json`, copy the
prepared `1132.lean` to `FormalConjectures/ErdosProblems/1132.lean`, then run:

```sh
lake --wfail build 'FormalConjectures.ErdosProblems.«1132»'
```

The latter was checked with upstream's Lean 4.33.1 toolchain. The Mathlib
source files are identical at the two pinned revisions. Pass
`--upstream /path/to/formal-conjectures` to `check_bridge.py` to verify both the
upstream revision and the copied file. The two projects remain separate;
this repository has no dependency on upstream's placeholder theorems.

## Database proposal

The patch changes only `formal_status`. It keeps the current `informal_status`
and leaves the generated `status` and `formalized` fields untouched.
The combined three-problem patch and PR draft are in the erdos-1132 repository,
under `submissions/teorth/`. The upstream validator accepts the combined patch
against the saved base revision.

## Submission references

The existing tracking issue is
[formal-conjectures#1971](https://github.com/google-deepmind/formal-conjectures/issues/1971).
The checked rules are [Formal Conjectures CONTRIBUTING](https://github.com/google-deepmind/formal-conjectures/blob/2c817e975be7a95478b72a8429155ca568e1a3de/CONTRIBUTING.md)
and [erdosproblems CONTRIBUTING](https://github.com/teorth/erdosproblems/blob/5308c57c700559416b9f205df274b136784203e7/CONTRIBUTING.md).
Neither contribution process requires an arXiv link.

The external proof links point to fixed commits of the proved results.
The community submissions are prepared here for separate review.
Before an actual Formal Conjectures submission, check the Google CLA and coordinate
on the existing issue. Its adopted [Mathlib AI policy](https://leanprover-community.github.io/contribute/index.html#use-of-ai)
requires tool/use disclosure, the `LLM-generated` label for substantial generated
code, and personally written review comments. The draft includes the disclosure.
