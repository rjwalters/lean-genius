# Independent H3 pair statement-chain review

Verdict: **no blocking semantic issue found in the conditional chain** at
`a4d9e8f7fbb92cf0e21cdaa3b3f5f12e2ff06e48` on
`erdos85/h3-pair-formal-20261008`. The native search and unconditional exclusion
remain outside this verdict. No peer source was edited, no Lean build was
repeated, and no Python search was run for this review.

## Graph statement and encoding

The endpoint is exactly `OrderFortyNineTripleCellExcluded 3 0`: every C4-free
simple graph on `Fin 49` with minimum degree at least seven, three high vertices
and zero triple-support low vertices is excluded. The bridge composes the
existing `threeHighCanonicalGraphCover_zero` with canonical representative
exclusion via `orderFortyNineTripleCellExcluded_three_of_canonical`.

`ThreeHighCanonicalRepresentativeExcluded 0` quantifies over all 1,176 edge
bits satisfying `orderFortyNineBooleanConstraints 3
(threeHighRepresentativeMasks 0)`. It is not a restriction to the Python core
or host enumerations. Those counts and programs are absent from the proof chain.

`model_of_constraints` derives every `Model` field from the relation constraints
and the encoding's symmetric, irreflexive adjacency. Its neighbour lists are
the actual finite neighbour sets, with exact degree eight for indices 0–2 and
seven for all other vertices. The common-neighbour bound gives `Model.c4`;
the exact colour-fibre partition gives both existence and uniqueness on low
vertices. Kernel-decided `mask_col` connects the fixed masks to the canonical
array. `initRow_edges` and prescribed high adjacency give `Compat s0 adj`.
No matching, normalized-core or host-list assertion is added as a hypothesis.

## Search and symmetry checks

- `Compat` preserves every known edge. For an edge of a compatible model,
  `allowed_sound` establishes the two degree-cap tests and the absence of a
  conflicting length-three path. Thus `tryAdd_none` rejects only an edge that
  cannot belong to that model. `tryAdd_some` preserves well-formedness and
  compatibility, and an already-present edge is handled idempotently.
- `twin_transport` requires two low vertices, equal masks and equal known
  adjacency rows. The swap preserves colours, degree caps and low status;
  symmetry of the partial graph also preserves columns. The proof transports
  both `Model` and compatibility. Phase 1's skip test additionally fixes the
  clause vertex and uses a strictly smaller index, justifying strong induction.
- Phase 2 keeps `FreshWit`: every untouched empty vertex has a colour triple
  in the available list. A triple may repeat a pair-support vertex. This is
  necessary and is handled by `pairOK`, `AdjAll` and idempotent `tryAdd`; the
  search does not silently require three distinct neighbours.
- `stateOK` is a checked Boolean guard. Its failure returns false. When a core
  vertex has deficient degree, `exists_fresh_nbr` excludes unknown high/core
  neighbours and already-touched empty neighbours using degree saturation and
  colour uniqueness. A compatible completion therefore supplies a fresh empty
  neighbour. Swapping it with the chosen zero-row empty vertex is covered by
  `twin_transport` and fixes all colour-triple entries.
- `patLoop_sound` justifies the candidate ban: a candidate is removed from the
  remaining witness list only in the branch where no fresh vertex realizes it.
  If one does realize it, the corresponding child is used. The proof retains
  `FreshWit` for remaining fresh vertices after the swap and insertion.
- Phase 3's counting gate bounds the possible neighbour list. Its subset
  enumeration contains a sufficiently long sublist of actual unknown model
  neighbours. `addMany` preserves compatibility on that branch, so a true
  recursive result contradicts the model.
- All three zero-fuel cases return false. Phase 3 also returns false when no
  deficient empty vertex remains. Therefore neither exhausted fuel nor reaching
  a complete candidate is treated as rejection. The proof is intentionally
  one-sided: `search = true` excludes a model; false does not establish one.

The fixed fuel values 70, 30 and 40 need no separate completeness assumption
for the conditional theorem. A successful checked evaluation is still required
to obtain the unconditional exclusion. `stateOK` need not be proved invariant
because any false guard prevents a successful rejection certificate.

## Independent build evidence

The cloud host was inspected read-only. Both relevant jobs have authoritative
exit files containing zero and fresh `Built` records, not only replayed output:

| Module | Job suffix | Execution commit | Printed exports |
| --- | --- | --- | --- |
| Engine | `073251-…-299945` | `9d1b51d0afa158491f80a6b963b2f08a976422d6` | `search_sound` |
| Bridge | `073435-…-301486` | `9aad4f0656deeb3084095d14ef8595a6ea0607eb` | Both conditional exclusions |

All three selected exports have exactly `propext`, `Classical.choice`,
`Quot.sound`. The successful build sources equal both the current cloud sources
and the reviewed commit's source bytes. `AUDIT.json` binds the raw log and
source hashes to the retained compiler-object hashes. Exact sources, job logs,
specs and exit files are retained in the module subdirectories. Objects remain
in the cloud build cache; they are not duplicated into this Git evidence bundle.
The earlier failed Engine job `20261008T072733-…-296343` is not accepted evidence.

The native job `20261008T073527-erdos85__h3-pair-formal-20261008-302533` was
still without a terminal exit when this review's jobs snapshot was taken.
No `pairSearch_true` axiom report or unconditional exclusion is credited here.
After success, independently check its terminal exit, source/object/log hashes
and all three final exports against the actual native axiom emitted by Lean.

## Nonblocking documentation corrections

The reviewed README references a `receipt.md` that is not present in that
commit. Add the actual receipt after the run. The Search module's introductory
comment names `Lean.ofReduceBool`; use the actual Lean 4.31 printed trust set
when reporting the finished result. These are documentation points, not proof
defects, and do not warrant changing the source of a running build.
