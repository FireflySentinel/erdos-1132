# Database contribution

[three-problems.patch](three-problems.patch) updates the entries for 917, 1075,
and 1132 in one change. [PR.md](PR.md) is the accompanying draft.
Each proof repository also contains its own single-entry `problems.patch`.

The base is teorth/erdosproblems at
`5308c57c700559416b9f205df274b136784203e7`.
In a checkout of that repository, apply the combined patch and validate:

```sh
git show 5308c57c700559416b9f205df274b136784203e7:data/problems.yaml > /tmp/erdosproblems-base.yaml
git apply /path/to/three-problems.patch
uv run --with PyYAML==6.0.2 --with jsonschema==4.23.0 --with ruamel.yaml==0.18.15 python scripts/validate.py --base /tmp/erdosproblems-base.yaml
```

The validator reports three notices about automatic regeneration of `status`
and then `Validation OK`. The patch leaves `informal_status`, `status`, and
`formalized` unchanged.

The #917 entry is a proposal to record the formally refuted general asymptotic
question. Its open `k = 6` part is explicit in both the entry and the PR draft;
the draft asks the maintainer to confirm aggregation of `formal_status`.
