# Record Lean proofs for problems 917, 1075, and 1132

Update `formal_status` with proof links and scope notes:

- [#1132](https://github.com/FireflySentinel/erdos-1132): both questions for triangular arrays, hence for nested sequences, with the additive constant allowed to depend on the point. The absolute-constant question for nested sequences remains open.
- [#1075](https://github.com/FireflySentinel/erdos-1075): counterexamples for every r >= 5, refuting the assertion quantified over all r >= 3. The r = 3 and r = 4 cases remain open.
- [#917](https://github.com/FireflySentinel/erdos-917): a k = 12 counterexample to the general asymptotic formula. The k = 6 question remains open.

The proofs use Lean 4 / Mathlib and only `propext`, `Classical.choice`, and
`Quot.sound`. Each repository contains a checked bridge to the proposed community
statement. The existing `informal_status` values are retained; neither `status`
nor `formalized` is edited.

For #917, the proposed formal status concerns the general asymptotic question
only. The contribution guide does not explicitly settle aggregation of
`formal_status` for a multi-part problem with an open part; please review that
classification with the scope note.

Validation: `scripts/validate.py --base <base problems.yaml>` passes at
5308c57c700559416b9f205df274b136784203e7. The only notices concern the expected
automatic regeneration of the three derived status values.

AI assistance: OpenAI Codex (GPT-6) prepared this metadata update and draft.
