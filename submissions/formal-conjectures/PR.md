# feat(ErdosProblems): formalize problem 1132

Fixes #1971.

Add the statements of Erdős Problem 1132 and closely related variants.
The two questions for a nested sequence follow from the stronger triangular-array theorem. The additive constant in part (i) may depend on the point. The file also states the array counterexample and leaves the absolute-constant question for nested sequences open.

Formalization choices:

- A row uses the explicit Lagrange products; injectivity excludes repeated nodes.
- The main questions use one infinite sequence, restricted to `Fin n` in row n. The bridge specializes the array theorem.
- The normalized limsup is in `EReal`. Terms at n = 0 and n = 1 have no effect on the filter at infinity; the empty and singleton rows have Lean tests.

The external proof attributes link to the [proved results](https://github.com/FireflySentinel/erdos-1132/blob/d352ff88a5a170c2fad8207684377df1022457f7/Erdos1132/Theorems.lean).
`checks/FormalConjecturesBridge.lean` in the proof repository proves the linked
statements using the proposed definitions. Its axiom guards allow only
`propext`, `Classical.choice`, and `Quot.sound`.

Validation: `lake --wfail build 'FormalConjectures.ErdosProblems.«1132»'`
on Lean 4.33.1; the proof bridge compiles on the proof repository's Lean 4.33.0.
A source comparison checks that the definitions and linked statement types agree.

AI assistance: OpenAI Codex (GPT-6) was used to prepare the statements, proof
bridges, and this draft.
