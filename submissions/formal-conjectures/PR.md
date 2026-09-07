# feat(ErdosProblems): formalize problem 1132

Fixes #1971.

Add the statements of Erdős Problem 1132 and closely related variants.
The two questions for a nested sequence follow from the stronger triangular-array theorem. The additive constant in part (i) may depend on the point. The file also states the array counterexample and leaves the absolute-constant question for nested sequences open.

Formalization choices:

- A row uses the explicit Lagrange products; injectivity excludes repeated nodes.
- The main questions use one infinite sequence, restricted to `Fin n` in row n. The bridge specializes the array theorem.
- The normalized limsup is in `EReal`. Terms at n = 0 and n = 1 have no effect on the filter at infinity; the empty and singleton rows have Lean tests.

The external proof attributes link to each declaration in the [proof bridge](https://github.com/FireflySentinel/erdos-1132/blob/0a245ce8833d4ee1d3edaffb79510cedbaf365cc/checks/FormalConjecturesBridge.lean#L50).
The theorem types use the proposed definitions; the axiom guards allow only
`propext`, `Classical.choice`, and `Quot.sound`.

Validation: `lake --wfail build 'FormalConjectures.ErdosProblems.«1132»'`
on Lean 4.33.1; the proof bridge compiles on the proof repository's Lean 4.33.0.
A source comparison checks that the definitions and linked statement types agree.

AI assistance: OpenAI Codex (GPT-6) was used to prepare the statements, proof
bridges, and this draft.
