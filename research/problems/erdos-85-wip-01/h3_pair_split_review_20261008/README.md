# Updated H3 pair engine and split: independent review

The conditional chain passed the independent cloud artifact audit. Build job
`20261008T081543-erdos85__h3-pair-formal-20261008-329751` exited zero at
`bc7532e9303e8082b8a8dfe7b305732ec194150a`. Its Engine, Bridge and Split sources
equal the files at reviewed commit `b3545ac16ae75faa072a66400bedb087544a03bf`
and the cloud checkout observed during this audit.

All three modules were freshly built in that job: Engine in 9.8 seconds,
Bridge in 4.8 seconds, Split in 3.8 seconds. Their actual nonempty Lean objects
have modification times within the successful job interval; their hashes were
stable across independent observations. The raw build reports four exports,
each using exactly `propext`, `Classical.choice` and `Quot.sound`:

- `Erdos85.H3Pair.search_sound`;
- `Erdos85.H3Pair.threeHighCanonicalRepresentativeExcluded_zero_of_pairSearch`;
- `Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero_of_pairSearch`;
- `Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero_of_parts`.

`AUDIT.json` pins sources, objects, raw evidence and the read-only auditor.
The exact sources, job log, spec and exit are retained here. Objects remain in
the existing cloud build volume. The audit neither ran Lean nor changed a
live job or source file.

## Source review

This extends the earlier `h3_pair_statement_review_20261008` review. Bridge
source is unchanged. The Engine changes from `90d79916b7d70d5a710e24a1b22434d5cd6ce74c`
introduce a cheaper occurrence-count heuristic, factor one phase-two node into
`step2`, and factor the triple partition into `patLoopSplit`. Soundness does
not require the new heuristic to match the old choice: the selected vertex
retains explicit range and degree guards, and the soundness proof covers any
such choice. `patLoopSplit_eq` relates the factored partition to the previously
reviewed one by reflexivity. `dfs2_sound` unfolds `step2` and rewrites that
equality before applying the existing argument. No statement weakening or
new trust escape was found in this delta.

The split distributes phase-one leaves using `stKey s % m`. For any state,
its own residue belongs to the full index range when `0 < m`; that part's
successful leaf test forces the original `leaf1` test. Hash injectivity or
balanced bucket sizes are unnecessary. The induction carries every part
through the same phase-one branches and the previously reviewed twin
transport. Positivity also supplies a part in the zero-fuel case. The final
composition still assumes success of every part. The later Split edit only
replaces redundant tactic alternatives with `rfl`.

## Limits

This is conditional soundness, not a completed pair exclusion. None of the
24 native part results or the final unconditional Cell exports is credited.
The earlier job `320500` was observed with a `Terminated` log and no exit file;
it is not accepted as a successful build. Replacement native job
`20261008T081713-erdos85__h3-pair-formal-20261008-331716` was observed live at
review commit `b3545ac16ae75faa072a66400bedb087544a03bf`. Its eventual result
needs a separate terminal, source, object and axiom audit.
